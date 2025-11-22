@ECHO OFF
TITLE Compiling SaladSoftware.py
SETLOCAL ENABLEDELAYEDEXPANSION

ECHO ================================================
ECHO      SaladSoftware Python Compiler
ECHO ================================================
ECHO.

:: ----------------------------------------------------------
:: 1. CHECK FOR MAIN FILE
:: ----------------------------------------------------------
IF NOT EXIST "SaladSoftware.py" (
    ECHO ERROR: SaladSoftware.py not found in this folder!
    PAUSE
    EXIT /B
)

:: ----------------------------------------------------------
:: 2. AUTO-DETECT VERSION (The Pure Batch Method)
:: ----------------------------------------------------------
ECHO Detecting version from SaladSoftware.py...

SET "VERSION="

:: 1. Find the line starting with VERSION using Windows findstr
:: 2. Split the line by the "=" sign
:: 3. Take the second part (the number)
FOR /F "tokens=2 delims==" %%I IN ('findstr /B "VERSION" SaladSoftware.py') DO SET "VERSION=%%I"

:: If logic found nothing
IF "%VERSION%"=="" (
    ECHO.
    ECHO ========================================================
    ECHO  ERROR: Could not detect VERSION in SaladSoftware.py
    ECHO ========================================================
    ECHO  Ensure the line starts exactly with:
    ECHO  VERSION = "..."
    ECHO.
    PAUSE
    EXIT /B
)

:: Clean up quotes and spaces from the result
:: Remove double quotes (")
SET "VERSION=%VERSION:"=%"
:: Remove single quotes (')
SET "VERSION=%VERSION:'=%"
:: Remove spaces
SET "VERSION=%VERSION: =%"

ECHO Version detected: [%VERSION%]
ECHO.

:: ----------------------------------------------------------
:: 3. RUN PYINSTALLER
:: ----------------------------------------------------------

ECHO Starting PyInstaller...
ECHO.

:: Check for assets
IF NOT EXIST "salad_icon.ico" ECHO WARNING: salad_icon.ico missing. Default icon will be used.
IF NOT EXIST "unique_extensions.txt" ECHO WARNING: unique_extensions.txt is missing.

pyinstaller --noconfirm --onefile --windowed --name "SaladSoftware_%VERSION%" ^
--icon="salad_icon.ico" ^
--add-data="unique_extensions.txt;." ^
--add-data="extension_index_line.txt;." ^
SaladSoftware.py

IF %ERRORLEVEL% NEQ 0 (
    ECHO.
    ECHO ================================================
    ECHO             COMPILATION FAILED
    ECHO ================================================
    ECHO.
    PAUSE
    EXIT /B
)

ECHO.
ECHO ================================================
ECHO              COMPILATION COMPLETE
ECHO ================================================
ECHO.
ECHO Output location: dist\SaladSoftware_%VERSION%.exe
ECHO.

:: Cleanup build folders
rmdir /S /Q build
del SaladSoftware.spec

PAUSE