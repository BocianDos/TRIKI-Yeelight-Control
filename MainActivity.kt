package pl.zabka.trikidimmer

import android.Manifest
import android.annotation.SuppressLint
import android.app.Activity
import android.app.AlertDialog
import android.bluetooth.*
import android.bluetooth.le.*
import android.content.Context
import android.content.SharedPreferences
import android.graphics.*
import android.graphics.drawable.GradientDrawable
import android.net.wifi.WifiManager
import android.os.*
import android.text.InputType
import android.util.Base64
import android.util.TypedValue
import android.view.*
import android.widget.*
import java.io.BufferedReader
import java.io.InputStreamReader
import java.io.OutputStreamWriter
import java.net.*
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.util.UUID
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import kotlin.math.*

data class LampNode(
    val ip: String,
    var id: String = "",
    var customName: String = "",
    var model: String = "bulb",
    var isOn: Boolean = true,
    var bright: Double = 50.0,
    var ct: Int = 4000,
    var nightMode: Boolean = false
) {
    fun displayName(): String = customName.ifBlank { "Yeelight (${ip.substringAfterLast('.')})" }
}

@SuppressLint("MissingPermission", "SetTextI18n")
class MainActivity : Activity() {

    private val lamps = CopyOnWriteArrayList<LampNode>()
    private var selectedIdx = 0 // lamps.size == WSZYSTKIE

    private lateinit var prefs: SharedPreferences
    private val ui = Handler(Looper.getMainLooper())
    private val netPool = Executors.newCachedThreadPool()

    // Stałe połączenia TCP Keep-Alive do żarówek (chronią przed przepełnieniem gniazd w Yeelight)
    private val socketMap = ConcurrentHashMap<String, Socket>()
    private val writerMap = ConcurrentHashMap<String, OutputStreamWriter>()

    // UUID profilu GATT dla kapsla TRIKI (CAP001)
    private val uuidService = UUID.fromString("6e400001-b5a3-f393-e0a9-e50e24dcca9e")
    private val uuidRx = UUID.fromString("6e400002-b5a3-f393-e0a9-e50e24dcca9e")
    private val uuidTx = UUID.fromString("6e400003-b5a3-f393-e0a9-e50e24dcca9e")
    private val uuidLed = UUID.fromString("6e400004-b5a3-f393-e0a9-e50e24dcca9e")
    private val uuidCccd = UUID.fromString("00002902-0000-1000-8000-00805f9b34fb")

    private val TRIKI_PRE_INIT = byteArrayOf(0x01, 0x00)
    private val TRIKI_START_FRAME = byteArrayOf(
        0x20, 0x10, 0x00, 0xD0.toByte(), 0x07, 0x34, 0x00, 0x03
    )

    private var gatt: BluetoothGatt? = null
    private var rxChar: BluetoothGattCharacteristic? = null
    private var txChar: BluetoothGattCharacteristic? = null
    private var ledChar: BluetoothGattCharacteristic? = null

    private var bleConnected = false
    private var scanningBle = false
    @Volatile private var rxPacketCount = 0L
    private var ledManualState = false
    private var invertDirection = false

    // Szeregowa kolejka BLE GATT
    private val gattQueue = ConcurrentLinkedQueue<() -> Unit>()
    @Volatile private var gattBusy = false
    private val gattTimeoutRunnable = Runnable {
        if (gattBusy) {
            gattBusy = false
            processNextGattOp()
        }
    }

    // Debounce przycisku i blokada ruchu (Motion-Lock)
    private var rawBtnFrames = 0
    private var debouncedBtnPressed = false
    private var btnDownTs = 0L
    private var maxGyroWhilePressed = 0
    private var rotatedDuringPress = false
    private var longPressFired = false
    private var clickCounter = 0

    // Fizyka żyroskopu i akcelerometru
    private var gyroBiasZ = 0f
    private var smoothedGz = 0f
    private var lastFrameTs = 0L
    private var uprightAccelSign = 1f
    private var gravityCalibrated = false
    private var upsideDownFrames = 0
    private var upsideDownLatched = false
    private var lastFlipTs = 0L

    // Limiter komend Yeelight (ochrona przed banem 60 cmd/min)
    private var lastNetSendTs = 0L
    private var lastSentBright = -1
    private var lastSentCt = -1
    private var pendingFlushIsCt = false
    private var sensitivityMultiplier = 1.0f

    // Komponenty UI
    private lateinit var hudView: TrikiHudView
    private lateinit var chipContainer: LinearLayout
    private lateinit var statusBadge: TextView
    private lateinit var logBox: TextView

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        window.statusBarColor = 0xFF0A0D12.toInt()
        window.navigationBarColor = 0xFF0A0D12.toInt()

        prefs = getSharedPreferences("triki_yeelight_cfg", Context.MODE_PRIVATE)
        sensitivityMultiplier = prefs.getFloat("sens", 1.0f)
        invertDirection = prefs.getBoolean("inv_dir", false)

        buildLayout()
        ensurePermissions()
        loadCachedLamps()
        scanLanForLamps()
    }

    override fun onDestroy() {
        super.onDestroy()
        runCatching { gatt?.close() }
        closeAllSockets()
        netPool.shutdownNow()
    }

    // =========================================================================
    // BUDOWANIE INTERFEJSU
    // =========================================================================
    private fun buildLayout() {
        val root = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            setBackgroundColor(0xFF0A0D12.toInt())
            setPadding(16.dp, 12.dp, 16.dp, 12.dp)
        }

        val topBar = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }

        val titleCol = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
        }
        val appTitle = TextView(this).apply {
            text = "TRIKI // CONTROL DECK"
            textSize = 16.5f
            typeface = Typeface.create(Typeface.MONOSPACE, Typeface.BOLD)
            setTextColor(0xFF00F5D4.toInt())
        }
        statusBadge = TextView(this).apply {
            text = "BLE: ROZŁĄCZONY  •  LAN: SKAN..."
            textSize = 10.5f
            typeface = Typeface.MONOSPACE
            setTextColor(0xFF8A99AD.toInt())
        }
        titleCol.addView(appTitle)
        titleCol.addView(statusBadge)

        val btnBle = makeActionPill("⚡ TRIKI", 0xFF00BBF9.toInt()) { toggleBleConnection() }
        val btnDir = makeActionPill("🔄 OŚ", 0xFF9D4EDD.toInt()) {
            invertDirection = !invertDirection
            prefs.edit().putBoolean("inv_dir", invertDirection).apply()
            log("[CFG] Odwrócono kierunek kręcenia kapslem (Inwersja: $invertDirection)")
        }
        val btnLan = makeActionPill("📡 LAN", 0xFF00F5D4.toInt()) { scanLanForLamps() }

        topBar.addView(titleCol)
        topBar.addView(btnBle)
        topBar.addView(Space(this).apply { layoutParams = LinearLayout.LayoutParams(6.dp, 1) })
        topBar.addView(btnDir)
        topBar.addView(Space(this).apply { layoutParams = LinearLayout.LayoutParams(6.dp, 1) })
        topBar.addView(btnLan)
        root.addView(topBar)

        val chipScroll = HorizontalScrollView(this).apply {
            isHorizontalScrollBarEnabled = false
            setPadding(0, 10.dp, 0, 6.dp)
        }
        chipContainer = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }
        chipScroll.addView(chipContainer)
        root.addView(chipScroll)

        hudView = TrikiHudView(this).apply {
            layoutParams = LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1f)
            onDialChanged = { newBright, newCt, isCtEdit ->
                applyManualDialChange(newBright, newCt, isCtEdit)
            }
            onCenterTap = { toggleActivePower() }
            onCenterLongPress = { toggleActiveNightMode() }
        }
        root.addView(hudView)

        val scenesRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            setPadding(0, 6.dp, 0, 6.dp)
        }
        val scenes = listOf(
            "🎬 KINO" to { applyScene(5, 2700, false) },
            "🥃 RELAKS" to { applyScene(35, 3200, false) },
            "💻 PRACA" to { applyScene(100, 5500, false) },
            "🌙 NOCNY" to { applyScene(15, 2700, true) },
            "💀 OFF" to { killAllLamps() }
        )
        scenes.forEachIndexed { i, (label, action) ->
            val accent = if (label.contains("OFF")) 0xFFFF0055.toInt() else 0xFF2B3545.toInt()
            val tv = TextView(this).apply {
                text = label
                textSize = 11f
                typeface = Typeface.create(Typeface.DEFAULT, Typeface.BOLD)
                setTextColor(Color.WHITE)
                gravity = Gravity.CENTER
                setPadding(8.dp, 8.dp, 8.dp, 8.dp)
                background = roundRect(accent, 10.dp, if (i == 4) 0xFFFF0055.toInt() else 0xFF3E4C63.toInt())
                layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f).apply {
                    if (i > 0) leftMargin = 6.dp
                }
                setOnClickListener {
                    it.performHapticFeedback(HapticFeedbackConstants.VIRTUAL_KEY)
                    action()
                }
            }
            scenesRow.addView(tv)
        }
        root.addView(scenesRow)

        val sensRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            setPadding(8.dp, 2.dp, 8.dp, 2.dp)
        }
        val sensLabel = TextView(this).apply {
            text = "CZUŁOŚĆ KAPSLA: ${(sensitivityMultiplier * 100).toInt()}%"
            textSize = 11f
            typeface = Typeface.MONOSPACE
            setTextColor(0xFF8A99AD.toInt())
        }
        val seek = SeekBar(this).apply {
            max = 250
            progress = (sensitivityMultiplier * 100).toInt()
            layoutParams = LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1f)
            setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
                override fun onProgressChanged(s: SeekBar?, p: Int, fromUser: Boolean) {
                    val clamped = p.coerceAtLeast(15)
                    sensitivityMultiplier = clamped / 100f
                    sensLabel.text = "CZUŁOŚĆ KAPSLA: $clamped%"
                    prefs.edit().putFloat("sens", sensitivityMultiplier).apply()
                }
                override fun onStartTrackingTouch(s: SeekBar?) {}
                override fun onStopTrackingTouch(s: SeekBar?) {}
            })
        }
        sensRow.addView(sensLabel)
        sensRow.addView(seek)
        root.addView(sensRow)

        logBox = TextView(this).apply {
            text = "[SYS] Gotowy. Kliknij 'Ż' na kapslu i naciśnij ⚡ TRIKI."
            textSize = 10f
            typeface = Typeface.MONOSPACE
            setTextColor(0xFF00F5D4.toInt())
            background = roundRect(0xFF11161F.toInt(), 8.dp, 0xFF1E2736.toInt())
            setPadding(10.dp, 8.dp, 10.dp, 8.dp)
            minLines = 2
            maxLines = 3
        }
        root.addView(logBox)

        setContentView(root)
        rebuildLampChips()
    }

    private fun makeActionPill(label: String, strokeColor: Int, onClick: () -> Unit): TextView {
        return TextView(this).apply {
            text = label
            textSize = 11.5f
            typeface = Typeface.create(Typeface.MONOSPACE, Typeface.BOLD)
            setTextColor(Color.WHITE)
            setPadding(10.dp, 7.dp, 10.dp, 7.dp)
            background = roundRect(0xFF161E2B.toInt(), 16.dp, strokeColor)
            setOnClickListener {
                it.performHapticFeedback(HapticFeedbackConstants.KEYBOARD_TAP)
                onClick()
            }
        }
    }

    // =========================================================================
    // KOLEJKA BLE GATT + INICJALIZACJA KAPSLA TRIKI
    // =========================================================================
    private fun enqueueGattOp(op: () -> Unit) {
        gattQueue.add(op)
        if (!gattBusy) processNextGattOp()
    }

    private fun processNextGattOp() {
        val next = gattQueue.poll()
        if (next == null) {
            gattBusy = false
            return
        }
        gattBusy = true
        ui.removeCallbacks(gattTimeoutRunnable)
        ui.postDelayed(gattTimeoutRunnable, 450)
        runCatching { next.invoke() }.onFailure { markGattOpDone() }
    }

    private fun markGattOpDone() {
        ui.removeCallbacks(gattTimeoutRunnable)
        gattBusy = false
        processNextGattOp()
    }

    private fun writeCharQueued(
        c: BluetoothGattCharacteristic?,
        payload: ByteArray,
        forceResponse: Boolean = true
    ) {
        val g = gatt ?: return
        val target = c ?: return
        enqueueGattOp {
            val props = target.properties
            target.writeType = when {
                forceResponse && (props and BluetoothGattCharacteristic.PROPERTY_WRITE) != 0 ->
                    BluetoothGattCharacteristic.WRITE_TYPE_DEFAULT
                (props and BluetoothGattCharacteristic.PROPERTY_WRITE_NO_RESPONSE) != 0 ->
                    BluetoothGattCharacteristic.WRITE_TYPE_NO_RESPONSE
                else ->
                    BluetoothGattCharacteristic.WRITE_TYPE_DEFAULT
            }
            target.value = payload
            if (!g.writeCharacteristic(target)) markGattOpDone()
        }
    }

    private fun enableNotifyQueued(c: BluetoothGattCharacteristic) {
        val g = gatt ?: return
        enqueueGattOp {
            g.setCharacteristicNotification(c, true)
            val desc = c.getDescriptor(uuidCccd)
            if (desc != null) {
                desc.value = BluetoothGattDescriptor.ENABLE_NOTIFICATION_VALUE
                if (!g.writeDescriptor(desc)) markGattOpDone()
            } else {
                markGattOpDone()
            }
        }
    }

    private fun toggleBleConnection() {
        if (bleConnected) {
            runCatching { gatt?.disconnect(); gatt?.close() }
            bleConnected = false
            gattQueue.clear()
            gattBusy = false
            updateTopStatus()
            log("[BLE] Rozłączono z kapslem.")
            return
        }
        startBleScan()
    }

    private fun startBleScan() {
        val adapter = BluetoothAdapter.getDefaultAdapter()
        if (adapter == null || !adapter.isEnabled) {
            log("[BLE] Włącz Bluetooth w telefonie!")
            return
        }
        val scanner = adapter.bluetoothLeScanner ?: return
        if (scanningBle) return
        scanningBle = true
        log("[BLE] Szukam TRIKI... Kliknij guzik 'Ż' na kapslu!")
        updateTopStatus()

        val callback = object : ScanCallback() {
            override fun onScanResult(callbackType: Int, result: ScanResult) {
                val devName = result.device.name ?: result.scanRecord?.deviceName ?: ""
                if (devName.contains("TRIKI", ignoreCase = true) || devName.contains("CAP", ignoreCase = true)) {
                    scanningBle = false
                    runCatching { scanner.stopScan(this) }
                    log("[BLE] Znaleziono $devName. Łączę...")
                    gatt = result.device.connectGatt(this@MainActivity, false, gattCallback, BluetoothDevice.TRANSPORT_LE)
                }
            }
        }
        scanner.startScan(callback)
        ui.postDelayed({
            if (scanningBle) {
                scanningBle = false
                runCatching { scanner.stopScan(callback) }
                updateTopStatus()
                log("[BLE] Timeout. Kliknij 'Ż' na kapslu i spróbuj ponownie.")
            }
        }, 8000)
    }

    private val gattCallback = object : BluetoothGattCallback() {
        override fun onConnectionStateChange(g: BluetoothGatt, status: Int, newState: Int) {
            if (newState == BluetoothProfile.STATE_CONNECTED) {
                bleConnected = true
                rxPacketCount = 0L
                gyroBiasZ = 0f
                smoothedGz = 0f
                lastFrameTs = 0L
                gravityCalibrated = false
                upsideDownFrames = 0
                upsideDownLatched = false
                rawBtnFrames = 0
                debouncedBtnPressed = false
                gattQueue.clear()
                gattBusy = false
                updateTopStatus()
                log("[BLE] Połączono! Inicjalizuję strumień IMU...")
                g.requestConnectionPriority(BluetoothGatt.CONNECTION_PRIORITY_HIGH)
                g.discoverServices()
            } else if (newState == BluetoothProfile.STATE_DISCONNECTED) {
                bleConnected = false
                gattQueue.clear()
                gattBusy = false
                updateTopStatus()
                log("[BLE] Kapsel rozłączony (uśpiony).")
            }
        }

        override fun onServicesDiscovered(g: BluetoothGatt, status: Int) {
            val nus = g.getService(uuidService)
            if (nus != null) {
                rxChar = nus.getCharacteristic(uuidRx)
                txChar = nus.getCharacteristic(uuidTx)
                ledChar = nus.getCharacteristic(uuidLed)
            } else {
                for (srv in g.services) {
                    for (c in srv.characteristics) {
                        when (c.uuid) {
                            uuidRx -> rxChar = c
                            uuidTx -> txChar = c
                            uuidLed -> ledChar = c
                        }
                    }
                }
            }

            txChar?.let { enableNotifyQueued(it) }
            writeCharQueued(rxChar, TRIKI_PRE_INIT, forceResponse = true)
            writeCharQueued(rxChar, TRIKI_START_FRAME, forceResponse = true)

            setCapLed(true)
            ui.postDelayed({ setCapLed(false) }, 200)
        }

        override fun onDescriptorWrite(g: BluetoothGatt, descriptor: BluetoothGattDescriptor, status: Int) {
            markGattOpDone()
        }

        override fun onCharacteristicWrite(g: BluetoothGatt, characteristic: BluetoothGattCharacteristic, status: Int) {
            markGattOpDone()
        }

        override fun onCharacteristicChanged(
            g: BluetoothGatt,
            c: BluetoothGattCharacteristic,
            value: ByteArray
        ) {
            processImuFrame(value)
        }

        @Deprecated("Deprecated in Java")
        override fun onCharacteristicChanged(g: BluetoothGatt, c: BluetoothGattCharacteristic) {
            if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) {
                val raw = c.value ?: return
                processImuFrame(raw)
            }
        }
    }

    private fun setCapLed(turnOn: Boolean) {
        val target = ledChar ?: return
        writeCharQueued(target, byteArrayOf(if (turnOn) 0x01 else 0x00), forceResponse = true)
    }

    private fun pulseTrikiLed(blinks: Int) {
        if (!bleConnected || ledChar == null) return
        netPool.execute {
            repeat(blinks.coerceIn(1, 4)) {
                setCapLed(true)
                Thread.sleep(100)
                setCapLed(false)
                Thread.sleep(100)
            }
        }
    }

    // =========================================================================
    // STABILNY PARSER RAMEK 0x22 Z FILTREM DRGAŃ I CAŁKOWANIEM KĄTA OBROTU
    // Układ bajtów w ramce 14-bajtowej:
    // [0]     = 0x22 (nagłówek)
    // [1]     = Przycisk (0x00 = puszczony, 0x01 = wciśnięty)
    // [2..3]  = gyroX (int16 LE)
    // [4..5]  = gyroY (int16 LE)
    // [6..7]  = gyroZ (int16 LE)  <-- OBRÓT POKRĘTŁEM W OSI Z!
    // [8..9]  = accelX (int16 LE)
    // [10..11]= accelY (int16 LE)
    // [12..13]= accelZ (int16 LE) <-- WEKTOR GRAWITACJI (odwrócenie na plecy)!
    // =========================================================================
    private val clickResolver = Runnable {
        val clicks = clickCounter
        clickCounter = 0
        if (clicks == 1) {
            cycleTargetLamp()
        } else if (clicks >= 2) {
            toggleActivePower()
        }
    }

    private val longPressResolver = Runnable {
        if (debouncedBtnPressed && !rotatedDuringPress && maxGyroWhilePressed < 450) {
            longPressFired = true
            hudView.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
            toggleActiveNightMode()
        }
    }

    // Trailing-edge flush: gwarantuje wysłanie ostatniej wartości po zatrzymaniu ręki
    private val trailingNetworkFlush = Runnable {
        val targets = activeLampList()
        if (targets.isEmpty()) return@Runnable
        val primary = targets.first()
        if (pendingFlushIsCt) {
            val ct = primary.ct
            if (ct != lastSentCt) {
                lastSentCt = ct
                targets.forEach { sendYeelightRpc(it.ip, "set_ct_abx", "[$ct,\"smooth\",200]") }
            }
        } else {
            val br = primary.bright.roundToInt()
            if (br != lastSentBright) {
                lastSentBright = br
                targets.forEach { lamp ->
                    if (lamp.nightMode) {
                        sendYeelightRpc(lamp.ip, "set_scene", "[\"nightlight\",$br]")
                    } else {
                        sendYeelightRpc(lamp.ip, "set_bright", "[$br,\"smooth\",200]")
                    }
                }
            }
        }
    }

    private fun handleDebouncedButton(pressed: Boolean) {
        if (pressed && !debouncedBtnPressed) {
            debouncedBtnPressed = true
            btnDownTs = SystemClock.elapsedRealtime()
            maxGyroWhilePressed = 0
            rotatedDuringPress = false
            longPressFired = false
            ui.postDelayed(longPressResolver, 750)
        } else if (!pressed && debouncedBtnPressed) {
            debouncedBtnPressed = false
            ui.removeCallbacks(longPressResolver)
            val holdDuration = SystemClock.elapsedRealtime() - btnDownTs

            // Pojedynczy/podwójny klik zaliczamy TYLKO wtedy, gdy kapsel nie był w tym czasie kręcony!
            if (!rotatedDuringPress && !longPressFired && maxGyroWhilePressed < 500 && holdDuration in 40..550) {
                clickCounter++
                ui.removeCallbacks(clickResolver)
                ui.postDelayed(clickResolver, 320)
            }
        }
    }

    private fun processImuFrame(data: ByteArray) {
        rxPacketCount++
        if (data.size < 14 || data[0] != 0x22.toByte()) return

        val now = SystemClock.elapsedRealtime()
        val dtSec = if (lastFrameTs == 0L) 0.01f else ((now - lastFrameTs) / 1000f).coerceIn(0.002f, 0.05f)
        lastFrameTs = now

        val buf = ByteBuffer.wrap(data).order(ByteOrder.LITTLE_ENDIAN)

        // Prawdziwe osie wg dokumentacji TrikiScope:
        val gx = buf.getShort(2).toInt()
        val gy = buf.getShort(4).toInt()
        val gzRaw = buf.getShort(6).toInt()  // Oś Z żyroskopu (pokrętło)
        val ax = buf.getShort(8).toInt()
        val ay = buf.getShort(10).toInt()
        val az = buf.getShort(12).toInt()    // Oś Z akcelerometru (grawitacja)

        // 1. Filtr drgań przycisku (wymaga 4 stabilnych ramek ~45ms)
        val rawBtn = (data[1].toInt() == 1)
        if (rawBtn) {
            rawBtnFrames = (rawBtnFrames + 1).coerceAtMost(10)
            if (rawBtnFrames >= 4 && !debouncedBtnPressed) {
                ui.post { handleDebouncedButton(true) }
            }
        } else {
            rawBtnFrames = (rawBtnFrames - 1).coerceAtLeast(0)
            if (rawBtnFrames == 0 && debouncedBtnPressed) {
                ui.post { handleDebouncedButton(false) }
            }
        }

        // 2. Ciągła kalibracja dryfu zera żyroskopu, gdy kapsel leży nieruchomo
        val totalGyroMag = abs(gx) + abs(gy) + abs(gzRaw)
        if (totalGyroMag < 300) {
            gyroBiasZ = gyroBiasZ * 0.96f + gzRaw * 0.04f
            if (!gravityCalibrated && abs(az) > 800) {
                uprightAccelSign = sign(az.toFloat())
                gravityCalibrated = true
            }
        }

        val gzClean = gzRaw - gyroBiasZ
        // Filtr dolnoprzepustowy wygładzający drżenia ręki
        smoothedGz = smoothedGz * 0.65f + gzClean * 0.35f
        val gzInt = smoothedGz.toInt()

        if (debouncedBtnPressed) {
            maxGyroWhilePressed = max(maxGyroWhilePressed, abs(gzInt))
        }

        // 3. Detekcja odwrócenie kapsla na plecy -> Wyłącz wszystkie lampy
        // Wymaga spokojnego położenia kapsla do góry nogami przez ~350ms (32 ramki), żeby ruch ręki go nie wyzwalał
        val orientedAz = az * uprightAccelSign
        if (orientedAz < -1100f && totalGyroMag < 1200) {
            upsideDownFrames++
            if (upsideDownFrames >= 32 && !upsideDownLatched && now - lastFlipTs > 3000) {
                upsideDownLatched = true
                lastFlipTs = now
                ui.post {
                    hudView.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
                    killAllLamps()
                }
            }
        } else if (orientedAz > 700f) {
            upsideDownFrames = 0
            upsideDownLatched = false
        }

        // 4. Pokrętło w osi Z (całkowanie realnego kąta obrotu w stopniach)
        // Martwa strefa: 260 LSB (~16 deg/s) całkowicie wycina drgania stołu i przypadkowe dotknięcia
        val deadzone = 260
        if (abs(gzInt) > deadzone && lamps.isNotEmpty()) {
            val targets = activeLampList()
            val primary = targets.first()

            val effectiveGz = (abs(gzInt) - deadzone) * sign(smoothedGz)
            // Przeliczenie na przyrost kątowy w czasie dtSec (~1 pełny obrót 360° = 100% jasności przy sens=100%)
            val dirSign = if (invertDirection) 1f else -1f
            val deltaPercent = (effectiveGz / 16.4f) * dtSec * 0.28f * sensitivityMultiplier * dirSign

            if (debouncedBtnPressed && abs(gzInt) > 450) {
                // Świadome trzymanie guzika + wyraźny obrót = Temperatura bieli (2700K - 6500K)
                rotatedDuringPress = true
                ui.removeCallbacks(longPressResolver)
                ui.removeCallbacks(clickResolver)

                val newCt = (primary.ct + (deltaPercent * 38f).roundToInt()).coerceIn(2700, 6500)
                if (newCt != primary.ct) {
                    targets.forEach { it.ct = newCt; it.nightMode = false; it.isOn = true }
                    throttledNetworkPush(newCt, isCt = true, targets = targets)
                }
            } else if (!debouncedBtnPressed) {
                // Sam obrót (bez trzymania guzika) = Jasność (1% - 100%)
                val newBright = (primary.bright + deltaPercent).coerceIn(1.0, 100.0)
                targets.forEach { it.bright = newBright; it.isOn = true }
                throttledNetworkPush(newBright.roundToInt(), isCt = false, targets = targets)
            }
        }

        if (rxPacketCount % 8L == 0L) {
            ui.post {
                hudView.updateImuTelemetry(
                    (ax / 2048f).coerceIn(-1f, 1f),
                    (ay / 2048f).coerceIn(-1f, 1f),
                    (orientedAz / 2048f).coerceIn(-1f, 1f),
                    gzInt,
                    debouncedBtnPressed,
                    upsideDownLatched
                )
                logBox.text = "[PKT #$rxPacketCount] BTN:${if (debouncedBtnPressed) "1" else "0"} | GYRO_Z:$gzInt | ACC_Z:$az"
            }
        }
    }

    // =========================================================================
    // WYKRYWANIE I STEROWANIE YEELIGHT LAN (PERSISTENT SOCKETS + RATE LIMITER)
    // =========================================================================
    private fun throttledNetworkPush(value: Int, isCt: Boolean, targets: List<LampNode>) {
        syncHudWithSelection()
        pendingFlushIsCt = isCt

        // Planujemy końcowy zapis po zatrzymaniu ręki (za 220 ms)
        ui.removeCallbacks(trailingNetworkFlush)
        ui.postDelayed(trailingNetworkFlush, 220)

        val now = SystemClock.elapsedRealtime()
        // Wysyłamy w trakcie ruchu max co 360ms (< 60 komend/min, zero banów od Yeelight!)
        if (now - lastNetSendTs >= 360) {
            if (isCt && abs(value - lastSentCt) >= 50) {
                lastNetSendTs = now
                lastSentCt = value
                ui.post { hudView.performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK) }
                targets.forEach { sendYeelightRpc(it.ip, "set_ct_abx", "[$value,\"smooth\",280]") }
            } else if (!isCt && value != lastSentBright) {
                lastNetSendTs = now
                lastSentBright = value
                ui.post { hudView.performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK) }
                targets.forEach { lamp ->
                    if (lamp.nightMode) {
                        sendYeelightRpc(lamp.ip, "set_scene", "[\"nightlight\",$value]")
                    } else {
                        sendYeelightRpc(lamp.ip, "set_bright", "[$value,\"smooth\",280]")
                    }
                }
            }
        }
    }

    private fun sendYeelightRpc(ip: String, method: String, paramsJson: String) {
        netPool.execute {
            val payload = """{"id":1,"method":"$method","params":$paramsJson}""" + "\r\n"
            synchronized(ip.intern()) {
                try {
                    var sock = socketMap[ip]
                    var writer = writerMap[ip]
                    if (sock == null || sock.isClosed || !sock.isConnected || writer == null) {
                        runCatching { sock?.close() }
                        sock = Socket()
                        sock.tcpNoDelay = true
                        sock.keepAlive = true
                        sock.connect(InetSocketAddress(ip, 55443), 700)
                        writer = OutputStreamWriter(sock.getOutputStream())
                        socketMap[ip] = sock
                        writerMap[ip] = writer
                    }
                    writer.write(payload)
                    writer.flush()
                } catch (e: Exception) {
                    // Jeśli żarówka zresetowała połączenie, zamknij stare gniazdo i ponów raz
                    runCatching { socketMap.remove(ip)?.close() }
                    writerMap.remove(ip)
                    try {
                        val fresh = Socket()
                        fresh.tcpNoDelay = true
                        fresh.connect(InetSocketAddress(ip, 55443), 700)
                        val w = OutputStreamWriter(fresh.getOutputStream())
                        w.write(payload)
                        w.flush()
                        socketMap[ip] = fresh
                        writerMap[ip] = w
                    } catch (ex: Exception) {
                        log("[LAN ERR] $ip: ${ex.javaClass.simpleName}")
                    }
                }
            }
        }
    }

    private fun closeAllSockets() {
        socketMap.values.forEach { runCatching { it.close() } }
        socketMap.clear()
        writerMap.clear()
    }

    private fun rebuildLampChips() {
        ui.post {
            chipContainer.removeAllViews()
            if (lamps.isEmpty()) {
                val emptyChip = TextView(this).apply {
                    text = "⚠️ Brak lamp (włącz LAN Control w Yeelight i kliknij 📡 LAN)"
                    textSize = 12f
                    setTextColor(0xFFFFB703.toInt())
                    setPadding(12.dp, 8.dp, 12.dp, 8.dp)
                    background = roundRect(0xFF1D1A12.toInt(), 12.dp, 0xFFFFB703.toInt())
                }
                chipContainer.addView(emptyChip)
                hudView.updateLampState("BRAK LAMP", false, 50.0, 4000, false)
                return@post
            }

            val totalItems = lamps.size + 1
            if (selectedIdx >= totalItems) selectedIdx = 0

            for (i in 0 until totalItems) {
                val isGroup = (i == lamps.size)
                val active = (i == selectedIdx)
                val title = if (isGroup) "⚡ WSZYSTKIE (${lamps.size})" else lamps[i].displayName()
                val bgCol = if (active) 0xFF00F5D4.toInt() else 0xFF151C28.toInt()
                val txtCol = if (active) 0xFF061014.toInt() else 0xFFD8E2EF.toInt()
                val borderCol = if (active) 0xFF00F5D4.toInt() else 0xFF283447.toInt()

                val chip = TextView(this).apply {
                    text = title
                    textSize = 12.5f
                    typeface = Typeface.create(Typeface.DEFAULT, if (active) Typeface.BOLD else Typeface.NORMAL)
                    setTextColor(txtCol)
                    setPadding(14.dp, 8.dp, 14.dp, 8.dp)
                    background = roundRect(bgCol, 20.dp, borderCol)
                    layoutParams = LinearLayout.LayoutParams(
                        ViewGroup.LayoutParams.WRAP_CONTENT,
                        ViewGroup.LayoutParams.WRAP_CONTENT
                    ).apply { rightMargin = 8.dp }

                    setOnClickListener {
                        it.performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK)
                        selectedIdx = i
                        lastSentBright = -1
                        lastSentCt = -1
                        rebuildLampChips()
                        syncHudWithSelection()
                    }

                    if (!isGroup) {
                        setOnLongClickListener {
                            it.performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
                            promptRenameLamp(lamps[i])
                            true
                        }
                    }
                }
                chipContainer.addView(chip)
            }
            syncHudWithSelection()
        }
    }

    private fun promptRenameLamp(lamp: LampNode) {
        val input = EditText(this).apply {
            inputType = InputType.TYPE_CLASS_TEXT
            setText(lamp.displayName())
            selectAll()
        }
        AlertDialog.Builder(this, android.R.style.Theme_DeviceDefault_Dialog_Alert)
            .setTitle("Nazwij lampę (${lamp.ip})")
            .setView(input)
            .setPositiveButton("Zapisz") { _, _ ->
                val newName = input.text.toString().trim()
                if (newName.isNotEmpty()) {
                    lamp.customName = newName
                    prefs.edit().putString("name_${lamp.ip}", newName).apply()
                    sendYeelightRpc(lamp.ip, "set_name", """["$newName"]""")
                    rebuildLampChips()
                }
            }
            .setNegativeButton("Anuluj", null)
            .show()
    }

    private fun loadCachedLamps() {
        val cachedIps = prefs.getStringSet("known_ips", emptySet()) ?: emptySet()
        cachedIps.sorted().forEach { ip ->
            val savedName = prefs.getString("name_$ip", "") ?: ""
            lamps.add(LampNode(ip = ip, customName = savedName))
        }
        rebuildLampChips()
    }

    private fun saveKnownIps() {
        val set = lamps.map { it.ip }.toSet()
        prefs.edit().putStringSet("known_ips", set).apply()
    }

    private fun scanLanForLamps() {
        log("[LAN] Skanowanie sieci (SSDP + TCP 55443)...")
        closeAllSockets()
        updateTopStatus()

        netPool.execute {
            runCatching {
                val wm = applicationContext.getSystemService(Context.WIFI_SERVICE) as? WifiManager
                val lock = wm?.createMulticastLock("triki_ssdp")?.apply { acquire() }

                DatagramSocket().use { sock ->
                    sock.soTimeout = 1800
                    sock.broadcast = true
                    val payload = ("M-SEARCH * HTTP/1.1\r\n" +
                            "HOST: 239.255.255.250:1982\r\n" +
                            "MAN: \"ssdp:discover\"\r\n" +
                            "ST: wifi_bulb\r\n\r\n").toByteArray()
                    val pkt = DatagramPacket(payload, payload.size, InetAddress.getByName("239.255.255.250"), 1982)
                    repeat(2) { sock.send(pkt) }

                    val buf = ByteArray(1500)
                    val deadline = SystemClock.elapsedRealtime() + 1800
                    while (SystemClock.elapsedRealtime() < deadline) {
                        val rx = DatagramPacket(buf, buf.size)
                        sock.receive(rx)
                        parseSsdpPacket(String(rx.data, 0, rx.length))
                    }
                }
                lock?.release()
            }
        }

        netPool.execute {
            val prefix = detectSubnetPrefix() ?: return@execute
            val sweepPool = Executors.newFixedThreadPool(32)
            for (host in 1..254) {
                val testIp = "$prefix.$host"
                sweepPool.execute { probeYeelightTcp(testIp) }
            }
            sweepPool.shutdown()
            sweepPool.awaitTermination(3, TimeUnit.SECONDS)
            ui.post {
                saveKnownIps()
                rebuildLampChips()
                updateTopStatus()
            }
        }
    }

    private fun parseSsdpPacket(raw: String) {
        val ip = Regex("yeelight://([0-9.]+):").find(raw)?.groupValues?.get(1) ?: return
        val model = Regex("model:\\s*(\\S+)").find(raw)?.groupValues?.get(1) ?: "bulb"
        val power = Regex("power:\\s*(\\S+)").find(raw)?.groupValues?.get(1) == "on"
        val bright = Regex("bright:\\s*(\\d+)").find(raw)?.groupValues?.get(1)?.toDoubleOrNull() ?: 50.0
        val ct = Regex("ct:\\s*(\\d+)").find(raw)?.groupValues?.get(1)?.toIntOrNull() ?: 4000
        val nlBr = Regex("nl_br:\\s*(\\d+)").find(raw)?.groupValues?.get(1)?.toIntOrNull() ?: 0
        val rawName = Regex("name:\\s*(\\S+)").find(raw)?.groupValues?.get(1) ?: ""

        registerOrUpdateLamp(ip, model, power, if (nlBr > 0) nlBr.toDouble() else bright, ct, nlBr > 0, rawName)
    }

    private fun probeYeelightTcp(ip: String) {
        try {
            Socket().use { s ->
                s.connect(InetSocketAddress(ip, 55443), 220)
                s.soTimeout = 400
                val out = OutputStreamWriter(s.getOutputStream())
                val inp = BufferedReader(InputStreamReader(s.getInputStream()))
                out.write("""{"id":99,"method":"get_prop","params":["power","bright","ct","nl_br","active_mode","name"]}""" + "\r\n")
                out.flush()
                val line = inp.readLine() ?: return
                if (line.contains("\"result\"")) {
                    val arrPart = line.substringAfter("[").substringBefore("]")
                    val tokens = arrPart.split(",").map { it.trim().removeSurrounding("\"") }
                    if (tokens.size >= 5) {
                        val isOn = tokens[0] == "on"
                        val br = tokens[1].toDoubleOrNull() ?: 50.0
                        val ctVal = tokens[2].toIntOrNull() ?: 4000
                        val nlBr = tokens[3].toIntOrNull() ?: 0
                        val activeMode = tokens[4].toIntOrNull() ?: 0
                        val night = (activeMode == 1 || nlBr > 0)
                        val nameToken = tokens.getOrNull(5) ?: ""
                        registerOrUpdateLamp(ip, "yeelight", isOn, if (night && nlBr > 0) nlBr.toDouble() else br, ctVal, night, nameToken)
                    }
                }
            }
        } catch (_: Exception) {}
    }

    private fun registerOrUpdateLamp(
        ip: String, model: String, isOn: Boolean, bright: Double, ct: Int, night: Boolean, rawName: String
    ) {
        val savedCustom = prefs.getString("name_$ip", "") ?: ""
        val decodedName = if (savedCustom.isNotBlank()) savedCustom else decodeLampName(rawName)

        val existing = lamps.find { it.ip == ip }
        if (existing != null) {
            existing.isOn = isOn
            existing.bright = bright.coerceIn(1.0, 100.0)
            existing.ct = ct.coerceIn(2700, 6500)
            existing.nightMode = night
            if (decodedName.isNotBlank() && existing.customName.isBlank()) existing.customName = decodedName
        } else {
            lamps.add(
                LampNode(
                    ip = ip,
                    customName = decodedName,
                    model = model,
                    isOn = isOn,
                    bright = bright.coerceIn(1.0, 100.0),
                    ct = ct.coerceIn(2700, 6500),
                    nightMode = night
                )
            )
            lamps.sortBy { it.ip.substringAfterLast('.').toIntOrNull() ?: 999 }
            rebuildLampChips()
        }
        updateTopStatus()
    }

    private fun decodeLampName(raw: String): String {
        if (raw.isBlank()) return ""
        return runCatching {
            val bytes = Base64.decode(raw, Base64.DEFAULT)
            val str = String(bytes, Charsets.UTF_8).trim()
            if (str.all { it.isLetterOrDigit() || it.isWhitespace() || it in "-_." }) str else raw
        }.getOrDefault(raw)
    }

    private fun detectSubnetPrefix(): String? {
        runCatching {
            val interfaces = NetworkInterface.getNetworkInterfaces()
            for (intf in interfaces) {
                if (intf.isLoopback || !intf.isUp) continue
                for (addr in intf.inetAddresses) {
                    if (addr is Inet4Address && !addr.isLoopbackAddress) {
                        val s = addr.hostAddress ?: continue
                        if (s.startsWith("192.168.") || s.startsWith("10.") || s.startsWith("172.")) {
                            return s.substringBeforeLast('.')
                        }
                    }
                }
            }
        }
        return null
    }

    private fun activeLampList(): List<LampNode> {
        if (lamps.isEmpty()) return emptyList()
        return if (selectedIdx >= lamps.size) lamps else listOf(lamps[selectedIdx])
    }

    private fun cycleTargetLamp() {
        if (lamps.isEmpty()) return
        selectedIdx = (selectedIdx + 1) % (lamps.size + 1)
        lastSentBright = -1
        lastSentCt = -1
        hudView.performHapticFeedback(HapticFeedbackConstants.CLOCK_TICK)
        rebuildLampChips()
        pulseTrikiLed(if (selectedIdx == lamps.size) 4 else selectedIdx + 1)
    }

    private fun applyManualDialChange(newBright: Double, newCt: Int, isCtEdit: Boolean) {
        val targets = activeLampList()
        if (targets.isEmpty()) return
        if (isCtEdit) {
            targets.forEach { it.ct = newCt; it.nightMode = false; it.isOn = true }
            throttledNetworkPush(newCt, isCt = true, targets = targets)
        } else {
            targets.forEach { it.bright = newBright; it.isOn = true }
            throttledNetworkPush(newBright.roundToInt(), isCt = false, targets = targets)
        }
    }

    private fun toggleActivePower() {
        val targets = activeLampList()
        if (targets.isEmpty()) return
        val turnOn = !targets.first().isOn
        targets.forEach {
            it.isOn = turnOn
            sendYeelightRpc(it.ip, "set_power", "[\"${if (turnOn) "on" else "off"}\",\"smooth\",250]")
        }
        syncHudWithSelection()
        log("[CMD] Zasilanie -> ${if (turnOn) "ON" else "OFF"}")
    }

    private fun toggleActiveNightMode() {
        val targets = activeLampList()
        if (targets.isEmpty()) return
        val enableNight = !targets.first().nightMode
        targets.forEach { lamp ->
            lamp.nightMode = enableNight
            lamp.isOn = true
            val modeCode = if (enableNight) 5 else 1
            sendYeelightRpc(lamp.ip, "set_power", "[\"on\",\"smooth\",300,$modeCode]")
        }
        syncHudWithSelection()
        log("[CMD] Tryb ${if (enableNight) "🌙 NOCNY (Moonlight)" else "☀️ DZIENNY (CT)"}")
    }

    private fun applyScene(bright: Int, ct: Int, night: Boolean) {
        val targets = activeLampList()
        if (targets.isEmpty()) return
        targets.forEach { lamp ->
            lamp.isOn = true
            lamp.bright = bright.toDouble()
            lamp.ct = ct
            lamp.nightMode = night
            if (night) {
                sendYeelightRpc(lamp.ip, "set_scene", "[\"nightlight\",$bright]")
            } else {
                sendYeelightRpc(lamp.ip, "set_scene", "[\"ct\",$ct,$bright]")
            }
        }
        syncHudWithSelection()
        log("[SCENA] Ustawiono: ${bright}% | ${if (night) "Moonlight" else "${ct}K"}")
    }

    private fun killAllLamps() {
        lamps.forEach {
            it.isOn = false
            sendYeelightRpc(it.ip, "set_power", "[\"off\",\"smooth\",300]")
        }
        syncHudWithSelection()
        log("[KILLSWITCH] Kapsel na plecach -> Wyłączono wszystkie lampy!")
    }

    private fun syncHudWithSelection() {
        ui.post {
            if (lamps.isEmpty()) return@post
            val isGroup = (selectedIdx >= lamps.size)
            val ref = if (isGroup) lamps.first() else lamps[selectedIdx]
            val label = if (isGroup) "WSZYSTKIE LAMPY (${lamps.size})" else ref.displayName()
            hudView.updateLampState(label, ref.isOn, ref.bright, ref.ct, ref.nightMode)
        }
    }

    private fun updateTopStatus() {
        ui.post {
            val bleStr = when {
                bleConnected -> "🟢 TRIKI POŁĄCZONY"
                scanningBle -> "🟡 SZUKAM TRIKI..."
                else -> "⚪ BLE ROZŁĄCZONY"
            }
            statusBadge.text = "$bleStr  •  💡 LAMPY: ${lamps.size}"
        }
    }

    private fun log(msg: String) {
        ui.post { logBox.text = msg }
    }

    private fun ensurePermissions() {
        val perms = mutableListOf(Manifest.permission.ACCESS_FINE_LOCATION, Manifest.permission.INTERNET)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
            perms.add(Manifest.permission.BLUETOOTH_SCAN)
            perms.add(Manifest.permission.BLUETOOTH_CONNECT)
        }
        requestPermissions(perms.toTypedArray(), 101)
    }

    private val Int.dp: Int
        get() = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, this.toFloat(), resources.displayMetrics).toInt()

    private fun roundRect(fillColor: Int, radiusPx: Int, strokeColor: Int): GradientDrawable {
        return GradientDrawable().apply {
            shape = GradientDrawable.RECTANGLE
            cornerRadius = radiusPx.toFloat()
            setColor(fillColor)
            setStroke(2, strokeColor)
        }
    }

    // =========================================================================
    // CUSTOM CANVAS VIEW: WEKTOROWY HUD POKRĘTŁA + TELEMETRIA 3D IMU
    // =========================================================================
    inner class TrikiHudView(ctx: Context) : View(ctx) {

        var onDialChanged: ((Double, Int, Boolean) -> Unit)? = null
        var onCenterTap: (() -> Unit)? = null
        var onCenterLongPress: (() -> Unit)? = null

        private var lampTitle = "SZUKAM LAMP..."
        private var isLampOn = true
        private var brightness = 50.0
        private var colorTemp = 4000
        private var isNight = false

        private var imuAx = 0f
        private var imuAy = 0f
        private var imuAz = 1f
        private var imuGz = 0
        private var puckPressed = false
        private var puckFlipped = false

        private val arcRect = RectF()
        private val innerArcRect = RectF()
        private var lastTouchAngle = 0f
        private var isDraggingDial = false
        private var touchDownTs = 0L
        private var longPressTriggeredTouch = false

        private val paintTrack = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            style = Paint.Style.STROKE
            strokeCap = Paint.Cap.ROUND
        }
        private val paintActive = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            style = Paint.Style.STROKE
            strokeCap = Paint.Cap.ROUND
        }
        private val paintFill = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            style = Paint.Style.FILL
        }
        private val paintText = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            textAlign = Paint.Align.CENTER
            typeface = Typeface.create(Typeface.MONOSPACE, Typeface.BOLD)
        }

        fun updateLampState(title: String, on: Boolean, br: Double, ct: Int, night: Boolean) {
            lampTitle = title
            isLampOn = on
            brightness = br
            colorTemp = ct
            isNight = night
            invalidate()
        }

        fun updateImuTelemetry(ax: Float, ay: Float, az: Float, gz: Int, pressed: Boolean, flipped: Boolean) {
            imuAx = ax; imuAy = ay; imuAz = az; imuGz = gz
            puckPressed = pressed; puckFlipped = flipped
            invalidate()
        }

        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)
            val cx = width / 2f
            val cy = height / 2f
            val radius = min(width, height) * 0.39f

            arcRect.set(cx - radius, cy - radius, cx + radius, cy + radius)
            val innerR = radius * 0.78f
            innerArcRect.set(cx - innerR, cy - innerR, cx + innerR, cy + innerR)

            val mainAccent = when {
                !isLampOn -> 0xFF3E4C63.toInt()
                isNight -> 0xFF9D4EDD.toInt()
                else -> 0xFF00F5D4.toInt()
            }

            val tickCount = 40
            paintTrack.strokeWidth = 4f
            for (i in 0..tickCount) {
                val frac = i / tickCount.toFloat()
                val deg = 135f + frac * 270f
                val rad = Math.toRadians(deg.toDouble())
                val activeTick = frac <= (brightness / 100.0)
                paintTrack.color = if (activeTick && isLampOn) mainAccent else 0xFF1F2937.toInt()
                val r1 = radius * 1.09f
                val r2 = radius * (if (i % 5 == 0) 1.16f else 1.13f)
                canvas.drawLine(
                    cx + (cos(rad) * r1).toFloat(), cy + (sin(rad) * r1).toFloat(),
                    cx + (cos(rad) * r2).toFloat(), cy + (sin(rad) * r2).toFloat(),
                    paintTrack
                )
            }

            paintTrack.strokeWidth = radius * 0.11f
            paintTrack.color = 0xFF141B26.toInt()
            canvas.drawArc(arcRect, 135f, 270f, false, paintTrack)

            val sweepBright = (brightness.toFloat() / 100f) * 270f
            paintActive.strokeWidth = radius * 0.11f
            paintActive.color = mainAccent
            canvas.drawArc(arcRect, 135f, sweepBright, false, paintActive)

            paintTrack.strokeWidth = radius * 0.055f
            paintTrack.color = 0xFF111722.toInt()
            canvas.drawArc(innerArcRect, 135f, 270f, false, paintTrack)

            val ctNorm = ((colorTemp - 2700f) / (6500f - 2700f)).coerceIn(0f, 1f)
            val ctColor = interpolateCtColor(ctNorm)
            paintActive.strokeWidth = radius * 0.055f
            paintActive.color = if (isNight) 0xFF7B2CBF.toInt() else ctColor
            canvas.drawArc(innerArcRect, 135f, ctNorm * 270f, false, paintActive)

            val coreR = radius * 0.56f
            paintFill.color = if (puckPressed) 0xFF19283A.toInt() else 0xFF0E141D.toInt()
            canvas.drawCircle(cx, cy, coreR, paintFill)

            paintTrack.strokeWidth = 3f
            paintTrack.color = if (puckPressed) 0xFFFFBE0B.toInt() else 0xFF223042.toInt()
            canvas.drawCircle(cx, cy, coreR, paintTrack)

            val dotX = (cx + (imuAx.coerceIn(-1f, 1f) * coreR * 0.45f))
            val dotY = (cy + (imuAy.coerceIn(-1f, 1f) * coreR * 0.45f))
            paintFill.color = 0x3300F5D4
            canvas.drawCircle(dotX, dotY, 18f, paintFill)
            paintFill.color = if (puckFlipped) 0xFFFF0055.toInt() else 0xFF00BBF9.toInt()
            canvas.drawCircle(dotX, dotY, 7f, paintFill)

            paintText.color = 0xFF8A99AD.toInt()
            paintText.textSize = radius * 0.095f
            canvas.drawText(lampTitle.uppercase(), cx, cy - coreR * 0.45f, paintText)

            paintText.color = if (isLampOn) Color.WHITE else 0xFF556275.toInt()
            paintText.textSize = radius * 0.34f
            val mainValText = if (!isLampOn) "OFF" else "${brightness.roundToInt()}%"
            canvas.drawText(mainValText, cx, cy + radius * 0.08f, paintText)

            paintText.color = if (isNight) 0xFFC77DFF.toInt() else ctColor
            paintText.textSize = radius * 0.11f
            val subText = when {
                puckFlipped -> "⚠️ KAPSEL NA PLECACH"
                isNight -> "🌙 MOONLIGHT MODE"
                puckPressed -> "⚡ EDYCJA BARWY: ${colorTemp}K"
                else -> "☀️ BARWA: ${colorTemp}K"
            }
            canvas.drawText(subText, cx, cy + coreR * 0.48f, paintText)

            paintText.color = 0xFF4C5B70.toInt()
            paintText.textSize = radius * 0.075f
            canvas.drawText("GYRO Z: $imuGz  |  DOTKNIJ: ON/OFF  |  PRZYTRZYMAJ: NOCNY", cx, height - 10f, paintText)
        }

        private fun interpolateCtColor(t: Float): Int {
            val r = (255 - t * 65).toInt().coerceIn(0, 255)
            val g = (175 + t * 65).toInt().coerceIn(0, 255)
            val b = (75 + t * 180).toInt().coerceIn(0, 255)
            return Color.rgb(r, g, b)
        }

        @SuppressLint("ClickableViewAccessibility")
        override fun onTouchEvent(ev: MotionEvent): Boolean {
            val cx = width / 2f
            val cy = height / 2f
            val dx = ev.x - cx
            val dy = ev.y - cy
            val dist = hypot(dx.toDouble(), dy.toDouble()).toFloat()
            val radius = min(width, height) * 0.39f

            when (ev.actionMasked) {
                MotionEvent.ACTION_DOWN -> {
                    touchDownTs = SystemClock.elapsedRealtime()
                    longPressTriggeredTouch = false
                    if (dist > radius * 0.55f) {
                        isDraggingDial = true
                        lastTouchAngle = Math.toDegrees(atan2(dy.toDouble(), dx.toDouble())).toFloat()
                    } else {
                        isDraggingDial = false
                        ui.postDelayed({
                            if (!isDraggingDial && SystemClock.elapsedRealtime() - touchDownTs >= 550) {
                                longPressTriggeredTouch = true
                                performHapticFeedback(HapticFeedbackConstants.LONG_PRESS)
                                onCenterLongPress?.invoke()
                            }
                        }, 560)
                    }
                    return true
                }
                MotionEvent.ACTION_MOVE -> {
                    if (isDraggingDial) {
                        val curAngle = Math.toDegrees(atan2(dy.toDouble(), dx.toDouble())).toFloat()
                        var delta = curAngle - lastTouchAngle
                        if (delta > 180f) delta -= 360f
                        if (delta < -180f) delta += 360f
                        lastTouchAngle = curAngle

                        val editingCt = dist < radius * 0.85f
                        if (editingCt) {
                            colorTemp = (colorTemp + (delta * 16f).toInt()).coerceIn(2700, 6500)
                            isNight = false
                            onDialChanged?.invoke(brightness, colorTemp, true)
                        } else {
                            brightness = (brightness + delta * 0.42).coerceIn(1.0, 100.0)
                            onDialChanged?.invoke(brightness, colorTemp, false)
                        }
                        invalidate()
                    }
                    return true
                }
                MotionEvent.ACTION_UP, MotionEvent.ACTION_CANCEL -> {
                    if (!isDraggingDial && !longPressTriggeredTouch && SystemClock.elapsedRealtime() - touchDownTs < 500) {
                        performHapticFeedback(HapticFeedbackConstants.VIRTUAL_KEY)
                        onCenterTap?.invoke()
                    }
                    isDraggingDial = false
                    return true
                }
            }
            return super.onTouchEvent(ev)
        }
    }
}
