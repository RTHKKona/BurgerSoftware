@ECHO OFF
TITLE Compiling SaladSoftware.py

ECHO ================================================
ECHO      SaladSoftware Python Compiler
ECHO ================================================
ECHO.
ECHO This script will compile SaladSoftware.py into a single .exe file.
ECHO Make sure you have PyInstaller installed: (pip install pyinstaller)
ECHO.

:: ----------------------------------------------------------
:: AUTO-DETECT VERSION NUMBER
:: ----------------------------------------------------------
ECHO Detecting version from SaladSoftware.py...

:: This command uses Python to read the file and find the VERSION = "X.X" line using Regex
FOR /F "delims=" %%i IN ('python -c "import re; print(re.search(r'VERSION\s*=\s*[\"\']([^\"\']+)[\"\']', open('SaladSoftware.py').read()).group(1))"') DO SET "VERSION=%%i"

IF "%VERSION%"=="" (
    ECHO ERROR: Could not find a VERSION variable in SaladSoftware.py
    PAUSE
    EXIT /B
)

ECHO Version detected: %VERSION%
:: ----------------------------------------------------------

PAUSE
CLS

ECHO Starting compilation for SaladSoftware v%VERSION%...
ECHO This may take a few moments.
ECHO.

:: Notice the use of %VERSION% in the --name argument
pyinstaller --noconfirm --onefile --windowed --name "SaladSoftware_%VERSION%" ^
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
ECHO     dist\SaladSoftware_%VERSION%.exe
ECHO.
ECHO Cleaning up temporary build files...
rmdir /S /Q build
del SaladSoftware.spec

ECHO.
ECHO Done! Press any key to exit.
PAUSE