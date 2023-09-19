# jwl-backup-merger
This Python-based utility simplifies the process of merging backups made by the JW Library app.

### Features
- Combine two or more JW Library backup files into one, which can then be re-imported into JW Library on all your devices.
- Automatically detect and merge conflicting data between backups.
- Coming soon: allow for manual conflict resolution.

**Warning:**
Before attempting to restore merged backups generated by this app, it is **strongly recommended** to create backups using JW Library on **all** your devices and to store these backups safely. 

**Disclaimer:**
This project is not affiliated with jw.org or the official JW Library app. It is an independent tool created by me, for personal use. Use this app at your own risk.

### Usage

Pre-requisites:

    pip install pandas tqdm tk

Running the app:

    python jwl-backup-merger.py [--debug] [--folder FOLDER_PATH] [--file FILE_PATH] [--file FILE_PATH] ...

#### Arguments

- `--folder FOLDER_PATH`: Folder containing JWL files to merge.
- `--file FILE_PATH`: JW Library backup file to add to the list of files to merge. You can specify multiple --file arguments to merge multiple files.
- `--debug`: Enable verbose debug output and Excel file creation to help with debugging; also prevents deletion of temporary files.

#### Example usage

    python jwl-backup-merger.py --folder /path/to/folder-with-jwl-backups
    python jwl-backup-merger.py --folder /path/to/folder-with-jwl-backups --file /path/to/additional-file1.jwlbackup
    python jwl-backup-merger.py --file /path/to/phone.jwlbackup --file /path/to/tablet.jwlbackup --file /path/to/computer.jwlbackup




