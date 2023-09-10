# jwl-backup-merger
This Python-based utility simplifies the process of merging backups made by the JW Library app.

### Features
- Combine two JW Library backup files into one, which can then be re-imported into all your devices.
- <s>Automatically detect and handle conflicting data between backups, and allow for manual conflict resolution.</s> (Coming soon; for now conflicting data is deduplicated, and if that fails then it is skipped.)

**Warning:**
Before attempting to restore merged backups generated by this app, it is **strongly recommended** to create a backup using JW Library on **all** your devices. 

**Disclaimer:**
This project is not affiliated with jw.org or the official JW Library app. It is an independent tool created by me, for personal use. Use this app at your own risk.

### Usage

Pre-requisites:

    pip install pandas tqdm tk

Running the app:

    python jwl-backup-merger.py
