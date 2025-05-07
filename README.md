![salad-stock-image-3862675171 (1)](https://github.com/user-attachments/assets/feea76d4-ca61-4d1c-af68-d0188ab1b54a)

# SaladSoftware MHGU ARC Tool

Welcome to the SaladSoftware MHGU ARC Tool wiki! This tool is designed for extracting and rebuilding `.arc` archive files specifically for Monster Hunter Generations Ultimate (MHGU) on the Nintendo Switch.

## Introduction

The SaladSoftware ARC Tool provides a graphical user interface (GUI) for managing MHGU's `.arc` files. These archives contain various game assets, and this tool allows users to:

*   Extract the contents of `.arc` files into organized folders.
*   Rebuild `.arc` files from these folders, incorporating any modifications made to the extracted files.

This tool is specifically configured for Nintendo Switch `.arc` files (Version 9, Little Endian) as used in MHGU. It does not utilize encryption keys, as MHGU `.arc` files are typically unencrypted.

## Features

*   **GUI Interface:** Easy-to-use tabbed interface for different operations.
*   **MHGU Switch ARC Focused:** Optimized for Version 9 Switch ARCs.
*   **Extraction:**
    *   Extract individual `.arc` files.
    *   Recursively extract all `.arc` files within a directory.
    *   Extracted content is placed in a folder named `<arc_filename_stem>_arc` in the *same directory* as the source `.arc` file.
*   **Rebuilding (Injection):**
    *   Rebuild `.arc` files from individual source folders.
    *   Batch rebuild multiple `.arc` files by matching source folders to original `.arc` names.
*   **Parallel Processing:** Utilizes multiple CPU cores for faster batch operations.
*   **Status Logging:** Detailed feedback on operations, including errors and successes.
*   **Extension Mapping:** Uses an `extension_index_line.txt` file to resolve file extensions from internal hashes, crucial for identifying MHGU file types.

## Requirements

*   **Operating System:** Windows, macOS, or Linux (Python and Tkinter compatible).
*   **Python:** Version 3.7 or newer recommended.
*   **Dependencies:**
    *   `pycryptodome` (though Blowfish encryption is not used for MHGU, it's a core dependency of the underlying framework).
*   **MHGU Game Files:** You'll need access to the `.arc` files from your MHGU game data.

## Setup

### Python

Ensure you have Python installed. You can download it from [python.org](https://www.python.org/). During installation on Windows, make sure to check the box "Add Python to PATH".

### Dependencies

Open a terminal or command prompt and install the required `pycryptodome` library:

```bash
pip install pycryptodome
```
Extension Map

This tool relies on an extension_index_line.txt file to correctly identify file extensions within the ARCs. This file must be present in the same directory as the SaladSoftware.py script.

The extension_index_line.txt file should be a plain text file where each line defines a mapping:

<hash_hex_value>, <.extension_with_dot>
IGNORE_WHEN_COPYING_START
content_copy
download
Use code with caution.
IGNORE_WHEN_COPYING_END

Examples:

05F3328D, .gmd
EF4D6A77, .tex

A comprehensive extension_index_line.txt specific to MHGU is highly recommended for proper file identification.

#### User Interface Overview
> Main Window
The main window of the SaladSoftware ARC Tool features:

> Title Area: Displays the tool's name.
> Tabs: Four tabs for different operations:

* Extract Arc Files (List)
* Inject Arc Folders into Arc (List)
* Recursive Extract Directory
* Folder Inject Directory

#### Status & Progress

* Status Log: A scrollable text area at the bottom displays real-time messages, warnings, errors, and success notifications for all operations. Messages are timestamped.
* Progress Bar: Below the status log, a progress bar shows the advancement of batch operations.

Operations (Tabs)

All extraction operations will create a new folder named <arc_filename_stem>_arc directly alongside the source .arc file. For example, extracting em001_00.arc will create a folder named em001_00_arc in the same directory.

1. Extract Arc Files (List)

This tab allows you to select one or more individual .arc files for extraction.

Input ARC Files:

Select Files: Click to open a file dialog and choose the .arc files you want to extract. You can select multiple files.

Listbox: Displays the selected .arc files.

Clear List: Removes all files from the listbox.

Output:

A label indicates: "Output: Folders named <filename>_arc will be created next to each input .arc file."

Start Extraction: Begins the extraction process for all listed ARC files.

2. Inject Arc Folders into Arc (List)

This tab allows you to rebuild .arc files from one or more source folders (typically folders previously extracted and modified, e.g., somefile_arc).

Input Source Folders:

Add Folder(s): Click to open a directory dialog and select the source folder(s) (e.g., em001_00_arc) to rebuild.

Listbox: Displays the selected source folders.

Clear List: Removes all folders from the listbox.

Output Rebuilt ARC Directory:

Browse...: Select the directory where the newly rebuilt .arc files will be saved. The rebuilt ARC will be named based on the source folder (e.g., em001_00_arc will produce em001_00.arc).

Start Rebuild: Begins the rebuilding process for all listed folders.

3. Recursive Extract Directory

This tab extracts all .arc files found within a specified source directory and its subdirectories.

Source ARC Directory (Recursive):

Browse...: Select the main directory containing the MHGU .arc files you wish to extract. The tool will scan this directory and all its subfolders for .arc files.

Output:

A label indicates: "Output: Folders named <filename>_arc will be created next to each found .arc file."

Start Recursive Extraction: Begins scanning and extracting all found .arc files.

4. Folder Inject Directory

This tab is for batch rebuilding of ARCs. It matches folders in an "Edited Content Directory" to .arc files in an "Original ARC Directory" and saves the rebuilt ARCs to a specified output location. This is useful for applying multiple mods or changes at once.

Original ARC Directory:

Browse...: Select the directory that contains the original, unmodified .arc files. This is used to match names.

Edited Content Directory (Contains Folders):

Browse...: Select the directory that contains the modified folders (e.g., em001_00_arc, quest01_arc). The tool will look for folders here and try to find a corresponding .arc file in the "Original ARC Directory".

For example, if em001_00_arc is in the "Edited Content Directory", the tool will look for em001_00.arc in the "Original ARC Directory".

Output Rebuilt ARC Directory:

Browse...: Select the directory where all newly rebuilt .arc files will be saved.

Start Folder Injection: Begins the matching and rebuilding process.

### Workflow Examples
#### Extracting a Single ARC

> Go to the "Extract Arc Files (List)" tab.
> Click "Select Files" and choose the MHGU .arc file (e.g., common/data/font/font_EU.arc).
> The file path will appear in the listbox.
> Click "Start Extraction".

A new folder (e.g., font_EU_arc) will be created in the same directory as font_EU.arc, containing its extracted contents.

#### Extracting All ARCs in a Directory

Dump your MHGU game files to a directory on your PC (e.g., C:\MHGU_DUMP\romfs\).

Go to the "Recursive Extract Directory" tab.

Click "Browse..." next to "Source ARC Directory (Recursive)" and select C:\MHGU_DUMP\romfs\.

Click "Start Recursive Extraction".

The tool will find all .arc files in C:\MHGU_DUMP\romfs\ and its subdirectories. For each .arc file found, it will create a corresponding _arc folder next to it (e.g., C:\MHGU_DUMP\romfs\em\em001\em001_00.arc will be extracted to C:\MHGU_DUMP\romfs\em\em001\em001_00_arc\).

#### Rebuilding a Single ARC from an Extracted Folder

Assume you have extracted neko_equip.arc to a folder neko_equip_arc and modified some files within it.

Go to the "Inject Arc Folders into Arc (List)" tab.

Click "Add Folder(s)" and select your neko_equip_arc folder.

Click "Browse..." next to "Output Rebuilt ARC Directory" and choose where you want to save the new neko_equip.arc.

Click "Start Rebuild". The new neko_equip.arc will be created in your chosen output directory.


#### Batch Rebuilding Multiple ARCs

This is useful if you have multiple mod folders you want to pack.

> Create a directory structure:

C:\MHGU_Modding\Original_ARCs\ (Place original, unmodified .arc files here, e.g., em001_00.arc, wp00_blk.arc)
C:\MHGU_Modding\My_Mod_Folders\ (Place your modified _arc folders here, e.g., em001_00_arc, wp00_blk_arc)
C:\MHGU_Modding\Rebuilt_ARCs\ (This will be your output directory)

> Go to the "Folder Inject Directory" tab.

Set "Original ARC Directory" to C:\MHGU_Modding\Original_ARCs\.
Set "Edited Content Directory" to C:\MHGU_Modding\My_Mod_Folders\.
Set "Output Rebuilt ARC Directory" to C:\MHGU_Modding\Rebuilt_ARCs\.

> Click "Start Folder Injection".

The tool will rebuild em001_00.arc and wp00_blk.arc into the Rebuilt_ARCs folder using the content from their respective _arc folders.

#### Important Notes for MHGU Modding

File Paths: MHGU is sensitive to file paths within ARCs. Do not rename or move files within an extracted _arc folder unless you know exactly what you are doing. The tool rebuilds ARCs using the filenames and (lack of) subfolder structure found within the source _arc folder.

Extension Map is Key: Without a good extension_index_line.txt, many files will have generic .XXXXXXXX (hex hash) extensions, making them hard to identify and edit.

Backup Your Files: Always back up your original game files and save data before installing any mods.

Test Thoroughly: After rebuilding and installing modded ARCs, test the game thoroughly to ensure stability and that your changes work as expected.

#### Troubleshooting

"Dependency Missing: pycryptodome": Ensure you have installed pycryptodome via pip (see Setup).

"Extension Map: Could not load or parse...": Make sure extension_index_line.txt is in the same directory as the script and is correctly formatted.

Permission Denied Errors: Ensure the tool has read permissions for input files/folders and write permissions for output locations. Try running as administrator if issues persist (though generally not recommended unless necessary).

Slow Performance on Many Small Files: Batch operations on a very large number of ARCs containing many small files can still take time, even with parallel processing. This is normal.

Extraction/Rebuild Errors for Specific Files: Check the status log for details. The error might be due to a corrupted ARC, an issue with a specific file being processed (e.g., unsupported compression if it wasn't standard Zlib, though unlikely for MHGU), or an unexpected file structure.

#### Credits

Handburger: Developer of this Python port and GUI.

IcySon55 (Kuriimu/Karameru): Original C# code and MT Framework ARC logic.

**Key changes and focus points for this MHGU Switch version:**

*   **MHGU Specificity:** Mentioned MHGU throughout.
*   **Switch Focus:** Emphasized Version 9 ARCs, Little Endian, and no encryption.
*   **Extraction Output Location:** Clearly stated that extracted `_arc` folders are created *next to* the source `.arc` file, and updated the UI descriptions and workflow examples accordingly.
*   **`extension_index_line.txt`:** Highlighted its importance for MHGU.
*   **Simplified Encryption:** Stated that encryption keys are not used for MHGU.
*   **Workflow Examples:** Tailored to reflect the new extraction output behavior and common MHGU modding scenarios.

Remember to replace placeholders like `C:\MHGU_DUMP\` with paths relevant to a typical user's setup if you have better examples. You can also add screenshots to the wiki page by uploading images to the GitHub wiki repository and linking them using Markdown's image syntax: `![Alt text](link_to_image.png)`.
IGNORE_WHEN_COPYING_START
content_copy
download
Use code with caution.
IGNORE_WHEN_COPYING_END
