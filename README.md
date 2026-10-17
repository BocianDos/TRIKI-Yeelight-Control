# TRIKI // Control Deck ⚡

> *Because turning off your lights by standing up and using a wall switch in 2026 is for total casuals.*

**TRIKI Control Deck** is an over-engineered, hardware-hacked bridge that turns a promotional Bluetooth puck from a convenience store loyalty program (*Żabka's Triki*) into a real-time smart home control deck for **Yeelight** smart bulbs over local LAN. Zero cloud dependency, zero lag, 100% pure local-network speed.

---

## 🚀 Features

* **BLE GATT Raw Stream Engine:** Bypasses proprietary apps by connecting directly to the nRF52810 SoC inside the puck, injecting initialization frames (`0x20 10 00 D0 07 34 00 03`) to unlock the IMU.
* **Vector HUD Interface:** A custom 60 FPS Android Canvas rendering dial that acts as a live virtual dimmer and 3D gyroscope telemetry visualizer.
* **Dual-Engine LAN Discovery:** Automatically sweeps local subnets and fires SSDP multicast queries to map all Yeelight bulbs in milliseconds.
* **Persistent TCP Keep-Alive:** Manages direct socket connections to the bulbs while strictly respecting the 60 commands/minute hardware rate limit to prevent connection bans.
* **Axis Inversion & Sensitivity Tuning:** Built-in UI controls to invert rotation direction and adjust gyroscope sensitivity on the fly.

---

## 🎮 Gesture Control Suite

| Gesture | Action |
| :--- | :--- |
| **Twist (Gyro Z)** | Smooth brightness scaling (`1% – 100%`) |
| **Hold + Twist** | Smooth white color temperature tuning (`2700K – 6500K`) |
| **Single Click** | Cycle through active lighting zones / lamps |
| **Double Click** | Toggle power (`ON/OFF`) for the active lamp |
| **Long Press (~0.7s)** | Toggle Night Mode (`Moonlight`) on/off |
| **Flip Down (Master Kill-Switch)** | Place the puck upside down on the desk to instantly shut down all lamps in the house |

---

## 📦 Installation & Setup

1. Download the latest `app-debug.apk` from the [Releases](../../releases) section.
2. Install it on your Android device (Android 8.0+ required).
3. Open your official Yeelight app, go to device settings, and ensure **LAN Control** is enabled for all your bulbs.
4. Open TRIKI Control Deck, press the **"Ż"** button on your Triki puck to wake it up, and tap **⚡ TRIKI** to connect!

*Built in native Kotlin with zero heavy UI frameworks, because real engineers write raw code between pizza slices.* 🍕
