@echo off
setlocal EnableExtensions EnableDelayedExpansion
chcp 437 >nul 2>&1
cd /d "%~dp0"

echo ==========================================
echo       Yan Builder (Zero-Error Version)
echo ==========================================
echo.

set "PYEXE="
where py >nul 2>&1 && set "PYEXE=py"
if not defined PYEXE (
    where python >nul 2>&1 && set "PYEXE=python"
)
if not defined PYEXE (
    echo [ERROR] Python not found in system PATH.
    pause
    exit /b 1
)

set /a COUNT=0
for %%F in (*.py) do (
    set /a COUNT+=1
    set "FILE[!COUNT!]=%%~fF"
    set "NAME[!COUNT!]=%%~nxF"
)
if !COUNT! equ 0 (
    echo [ERROR] No .py files found.
    pause
    exit /b 1
)

set "TARGET=!FILE[1]!"
if !COUNT! gtr 1 (
    set "TARGET=!FILE[1]!"
    echo [INFO] Auto-selected the first file.
)

echo [INFO] Target file: !TARGET!
echo [INFO] Installing PyInstaller...
!PYEXE! -m pip install pyinstaller -i https://pypi.tuna.tsinghua.edu.cn/simple

echo [INFO] Building...
!PYEXE! -m PyInstaller -F -w --clean --noupx "!TARGET!"

echo ==========================================
echo [SUCCESS] Done! Press any key to exit.
echo ==========================================
pause
exit /b 0