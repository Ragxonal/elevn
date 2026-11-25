# Elevn – FPL assistant

Elevn runs on top of the Fantasy Premier League site and helps with your squad, transfers, captain, chips, leagues, live points and news. Enter any FPL team ID.

Current version: **3.77** (see [`version.json`](version.json)).

## Install

| Device | File | How |
|---|---|---|
| Android | [Elevn-Android-v3-77.apk](https://github.com/Ragxonal/elevn/raw/main/dist/Elevn-Android-v3-77.apk) | Download and open it. Allow installs from your browser if Android asks. To update, install the new APK over the old one. |
| Chrome (computer) | [Elevn-Chrome-v3-77.zip](https://github.com/Ragxonal/elevn/raw/main/dist/Elevn-Chrome-v3-77.zip) | Unzip it. Open `chrome://extensions`, turn on Developer mode, click **Load unpacked** and pick the `Elevn` folder. On a Mac, Safari may unzip it for you: the `Elevn` folder is then already in Downloads. To update, unzip over the same folder and click **Reload**. |
| iPhone / iPad (Safari) | [Elevn.user.js](https://raw.githubusercontent.com/Ragxonal/elevn/main/dist/Elevn.user.js) | Install the free **Userscripts** app, open this link in Safari and add the script. It updates itself after that. |

Elevn checks this repository once a day and shows a banner with the right download when a new version is out.

## Privacy

Everything Elevn saves (team IDs, plans, settings, an optional odds key) stays on your own device. This repository holds only the app files.

## Feed race (GitHub Actions)

`.github/workflows/feedrace.yml` runs `race/feedrace.js` every 20 minutes during Premier League matches and records how many seconds before FPL each live source (FotMob, ESPN, Premier League match centre) showed every goal and assist. Results are on the `feedrace-data` branch: `out/feedrace-GW.json` (one row per goal or assist) and `ledger/race-GW.json` (raw first-seen times).
