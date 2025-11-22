# SaladSoftware - A Kuriimu1/2 MT Framework-only Python Variant
**Version 2.4.1**

![Screenshot 2025-05-09 123142](https://github.com/user-attachments/assets/88742bf3-1e9f-443b-8be5-d3b23ff674ea)
![Screenshot 2025-05-09 121140](https://github.com/user-attachments/assets/e23ae47c-b4db-4d64-9464-68096804baf7)

- **Dark Mode UI**
- **Drag & Drop Support** (Files and Folders)
- **High-DPI / 4K Support**
- **Atomic Writes** (Prevents corruption if a save fails)
- **Threaded Scanning & Parallel Compression**
- **Windows Context Menu Integration**

SaladSoftware uses Kuriimu (1) Karameru C# code logic adapted to Python. Original MTArc, Komponent, Encryption, and C# code processing logic belongs to IcySon55 and FanTranslatorInternational. I adapted it to Python, added a GUI with dark mode, logging, and stability features like atomic saves and memory safety caps.

## Dependencies
If running from source, you must install the following:
```bash
pip install pycryptodome tkinterdnd2
```

## Tab Descriptions

### 1. Extract from ARC(s)
- **Purpose:** Unpack an original game archive (.arc) into a folder.
- **Usage:** Drag and drop .arc files or select them via the button.
- **Output:** Each ARC is extracted into a subfolder next to the original file (e.g., `resident.arc` -> `resident_arc/`).
- **Note:** Preserves internal folder structure.

### 2. Repack Folder (In-Place)
- **Purpose:** Rebuild an edited folder back into a byte-perfect .arc file. **(Recommended for Modding)**
- **Usage:** Select the directory containing both your original `.arc` and your edited `_arc` folder.
- **Logic:** 
  - Finds pairs (e.g., `file.arc` and `file_arc`).
  - Uses the original ARC to copy headers, version info, and unchanged files (High-Fidelity Rebuild).
  - Only compresses files that have actually changed on disk.
- **Safety:** 
  - Creates a `.tmp` file first to ensure write success.
  - Moves the original `.arc` and the source `_arc` folder into an `original_data` subfolder upon success.
  - **Optional:** Can be set to delete `original_data` automatically after a successful rebuild.

### 3. Build New ARC from Folder
- **Purpose:** Create a completely new .arc file from a folder of assets.
- **Warning:** Uses default settings (Switch/PC hybrid defaults). Not recommended for modding existing files; use Tab 2 instead.

### 4. Batch: Extract All in Folder
- **Purpose:** Recursively scan a root directory for *any* .arc files and extract them.
- **Output:** Creates `_arc` folders next to every found .arc file.

### 5. Batch: Repack Folders (In-Place)
- **Purpose:** Recursively find and rebuild all ARCs from their extracted folders.
- **Logic:** Same as Tab 2, but scans subdirectories.
- **Cleanup:** Options to move originals to `original_data` or delete them after successful repacking.

### 6. Batch: Extract All (Single Folder / Flatten)
- **Purpose:** Extract contents of many ARCs into one single "flat" folder.
- **Usage:** Useful for dumping all textures or sounds to one place.
- **Naming:** Filenames are prefixed with the source ARC name (e.g., `resident_arc_font.tex`) to prevent conflicts.

### 7. Advanced: Partial Extract (Internal ARC View)
- **Purpose:** Preview and extract specific files without unpacking the whole archive.
- **Usage:** 
  - Load an ARC.
  - Check boxes next to files or folders.
  - Extract to specific location.

### 8. Advanced: Partial Inject (Internal ARC Injection)
- **Purpose:** Replace specific files inside an existing ARC without full unpacking/repacking.
- **Usage:**
  - Load an ARC.
  - Select a specific file in the tree view.
  - Click "Replace Selected File..." and choose your new file from disk.
  - Click "Start Injection".
- **Behavior:** Creates a new ARC where only the targeted files are replaced; all other data is copied raw from the original.

## CLI Usage
The tool automatically detects if you pass a file or folder argument, but specific commands are available.

**Usage:** `python SaladSoftware.py [command] [options]`

### Commands

1.  **extract** `<ARC_FILE...>`
    *   Extracts one or more .arc files into `_arc` folders.
2.  **inject** `<FOLDER...>` `--output-dir <DIR>`
    *   Builds new ARCs from source folders (Scratch rebuild).
3.  **extract-recursive** `<SOURCE_DIR>`
    *   Recursively finds and extracts all ARCs in a directory.
4.  **inject-recursive** `<SOURCE_DIR>` `[--move-originals]`
    *   In-place recursive rebuild. Scans for `name.arc` + `name_arc` pairs.
    *   Uses high-fidelity repacking.
5.  **extract-flat** `<SOURCE_PATH>` `--output-dir <DIR>`
    *   Extracts all files from an ARC or directory of ARCs into one flat folder.
6.  **install-menu**
    *   **(Windows Only)** Installs context menu items:
        *   Right-click .arc file -> **Extract ARC**
        *   Right-click Folder -> **Rebuild ARC**

## Compiling
To compile this into a standalone EXE (Windows), use PyInstaller. Ensure `tkinterdnd2` is installed in your environment.

```bash
pyinstaller --onefile --windowed --icon salad_icon.ico --name "SaladSoftware 2.4.1" --add-data "extension_index_line.txt;." --add-data "unique_extensions.txt;." --collect-all tkinterdnd2 SaladSoftware.py
```
*(Note: `--collect-all tkinterdnd2` is often required to ensure the drag-and-drop binaries are bundled correctly).*

