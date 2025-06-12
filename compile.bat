@ECHO OFF
TITLE Compiling SaladSoftware.py

ECHO ================================================
ECHO      SaladSoftware Python Compiler
ECHO ================================================
ECHO.
ECHO This script will compile SaladSoftware.py into a single .exe file.
ECHO Make sure you have PyInstaller installed: (pip install pyinstaller)
ECHO.
PAUSE
CLS

ECHO Starting compilation...
ECHO This may take a few moments.
ECHO.

pyinstaller --noconfirm --onefile --windowed --name "SaladSoftware" ^
--icon="salad_icon.ico" ^
--add-data="unique_extensions.txt;." ^
--add-data="extension_index_line.txt;." ^
SaladSoftware.py

ECHO.
ECHO ================================================
ECHO              COMPILATION COMPLETE
ECHO ================================================
ECHO.
ECHO Your file can be found in the 'dist' folder:
ECHO     dist\SaladSoftware.exe
ECHO.
ECHO Cleaning up temporary build files...
rmdir /S /Q build
del SaladSoftware.spec

ECHO.
ECHO Done! Press any key to exit.
PAUSE