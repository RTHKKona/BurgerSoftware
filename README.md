# SaladSoftware - A Kuriimu1/2 MT Framework-only Python Variant
![Screenshot 2025-05-09 123142](https://github.com/user-attachments/assets/88742bf3-1e9f-443b-8be5-d3b23ff674ea)
![Screenshot 2025-05-09 121140](https://github.com/user-attachments/assets/e23ae47c-b4db-4d64-9464-68096804baf7)

- Uses Dark Mode
- Has individual and recursive arc extraction and injection
- Log for debugging

BurgerSoftware uses Kuriimu2-dev C# code. I did not do this myself.
HotdogSoftware uses Kuriimu2 as well.
SaladSoftware uses Kuriimu (1) Karameru C# code, but uses python instead. Original MTArc, Komponent, Encryption, and C# code processing belongs to IcySon55 and FanTranslatorInternational, all I did was adapt it to Python and add a darkmode and log so its clearer what the app is doing while stalled.

## Tab Descriptions

        * Extract Arc Files
           - Select one or more .arc files.
           - Each ARC is extracted into its own subfolder (e.g., 'file.arc' extracts to 'file_arc/').
           - The internal folder structure of each ARC is preserved within its output subfolder.
           - Output folders are created next to their respective input .arc files.

        * Inject Arc Folders
           - Add one or more source folders to the list. These folders contain files you want to pack into ARCs.
           - Select an output directory where the new .arc files will be saved.
           - Each source folder is rebuilt into a new .arc file (e.g., 'my_mod_folder' becomes 'my_mod_folder.arc').
           - By default, ARCs are created using parameters suitable for Switch games (Version 9, Little Endian).

        * Recursive Extract Arcs
           - Select a root directory.![Screenshot 2025-05-09 123142](https://github.com/user-attachments/assets/cf89e0f2-2bb0-4ce4-af83-d609ff52a111)

           - The tool will scan this directory and all its subdirectories for .arc files.
           - Each found .arc file is extracted similarly to 'Extract Arc Files (List)' (into its own subfolder, next to the ARC).
           - You can keep track of what is happening via the log on the bottom. 

        * Recursive Inject (In-Place)
           - Select a root directory that contains both original .arc files and corresponding unpacked/edited folders (typically named 'original_arc_name_arc').
           - The tool matches *_arc folders with their .arc files.
           - Original .arc files are backed up into an 'original_arc_backups' subfolder (created within the selected root directory).
           - The *_arc folders are then rebuilt into .arc files, replacing the originals.
           - This process attempts to use the *exact parameters* (version, platform, byte order, ARCC status, file order, compression hints) from the original ARC for the rebuild.
           - Processed *_arc folders are also moved to the backup directory.

        * Extract All (Flatten File Structure)
           - Select a root directory containing .arc files (scanned recursively).
           - Select a single output directory.
           - All files from all found ARCs are extracted directly into this single output directory.
           - The original folder structure *within* the ARCs is discarded (flattened).
           - To prevent name collisions, extracted filenames are prefixed with the name of their source ARC (e.g., 'arc1_image.tex', 'arc2_sound.wav').

        * Internal-ARC Extraction
           - Select a single .arc file to load and preview its internal file/folder structure in a tree view.
           - Check the boxes next to individual files or folders within the tree that you wish to extract.
             - Checking a folder will effectively check all its contents.
           - Select an output directory.
           - Click "Extract Selected Items".
             - If a file is checked, it's saved to: `output_dir/filename.ext`
             - If a folder (e.g., 'textures/player') is checked, its contents are saved to: `output_dir/player/content_file.ext`, preserving the structure *relative to the checked folder*.


## Compiling

I used ``` pyinstaller --name "SaladSoftware" --onefile --windowed --icon="salad_icon.ico" --add-data "extension_index_line.txt:." --add-data "unique_extensions.txt:." --hidden-import "Crypto.Cipher.Blowfish" SaladSoftware.py ``` to compile this project into an exe.

###### buh
