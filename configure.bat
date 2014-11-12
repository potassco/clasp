@ECHO OFF
SETLOCAL EnableDelayedExpansion
REM  OPTIONS
set static=0
set machine=0
set mt=0
set PREFIX=%HOMEDRIVE%%HOMEPATH%
set BIN_DIR=
set CONFIG=
REM CONFIGURATION
set CXXFLAGS=%CXXFLAGS%
set LIBS=libclasp libprogram_opts
set LDFLAGS=%LDFLAGS%
set LDLIBS=
set BUILDPATH=build\release
set INSTALLPATH=%PREFIX%\bin
SET INCLUDES=
SET LIB_TARGETS=
set CXX=
set POST_BUILD=
SET TBB_LIB=
SET TBB_INCLUDE=

REM Scan arguments.
:ARG_LOOP
IF [%1]==[] (
	GOTO DONE
) ELSE IF [%1]==[/?] ( goto o_help
) ELSE IF [%1]==[--help] (
:o_help
	ECHO.
	ECHO.  %0 [ options ]
	ECHO.
	ECHO.Options:
	ECHO. ?,--help       : print this page
	ECHO. --prefix=PATH  : set install prefix to PATH
	ECHO. --bindir=PATH  : set install path to PATH
	ECHO.
	ECHO. --config=NAME  : set configuration to NAME
	ECHO.    NAME=release: configure for optimized release version 
	ECHO.    NAME=debug  : configure for debug version
	ECHO.    NAME=check  : configure for release version with assertions enabled
	ECHO.    ELSE        : configure for custom configuration
	ECHO.
	ECHO  --with-mt      : enable multi-thread support ^(see below^)
	ECHO  --static       : link statically ^(if supported^)
	ECHO. --m32          : force 32-bit binary ^(if supported^)
	ECHO. --m64          : force 64-bit binary ^(if supported^)
	ECHO. --strip        : discard symbols ^(calls strip after build^)
	ECHO. --clean        : remove all generated files
	ECHO.
	ECHO. Note: Multi-thread support requires Intel Threading Building Blocks 3.x.
	ECHO.       Use option --with-mt and either set TBB30_INSTALL_DIR environment 
	ECHO.       variable or explicitly set include and/or library path via:
	ECHO.   %0 --with-mt TBB_INCLUDE=^<path_to_nclude^> TBB_LIB=^<path_to_lib^>
	ECHO.
	ECHO. Note: To create a custom configuration call %0 like this:
	ECHO.   %0 --config=my_c CXX=my_gcc CXXFLAGS=my_cxxf LDFLAGS=my_ldf
	ECHO.
	GOTO EXIT
) ELSE IF [%1]==[CXX] (
	SET CXX=%2
	SHIFT
) ELSE IF [%1]==[CXXFLAGS]  (
	SET CXXFLAGS=%2
	SHIFT
) ELSE IF [%1]==[LDFLAGS]  (
	SET LDFLAGS=%2
	SHIFT
) ELSE IF [%1]==[TBB_INCLUDE]  (
	SET TBB_INCLUDE=%2
	SHIFT
) ELSE IF [%1]==[TBB_LIB]  (
	SET TBB_LIB=%2
	SHIFT
) ELSE IF [%1]==[--prefix] (
	SET PREFIX=%2
	SHIFT
) ELSE IF [%1]==[--bindir] (
	SET BIN_DIR=%2
	SHIFT
) ELSE IF [%1]==[--config] (
	if not [%CONFIG%]==[] ( 
		ECHO *** Error: multiple values for option '--config'
		goto EXIT
	)
	set CONFIG=%2
	SHIFT
) ELSE IF [%1]==[--static] (
	SET static=1
) ELSE IF [%1]==[--with-mt] (
	SET mt=1
) ELSE IF [%1]==[--m32] (
	SET machine=32
) ELSE IF [%1]==[--m64] (
	SET machine=64
) ELSE IF [%1]==[--strip] (
	SET POST_BUILD=strip
) ELSE IF [%1]==[--clean] (
	IF NOT EXIST build goto EXIT
	RD /S /Q build
	goto EXIT
) ELSE (
	ECHO *** Error: Unknown parameter '%1'.
	ECHO Type '%0 /?' for an overview of supported options.
	GOTO EXIT
)
SHIFT
GOTO ARG_LOOP
:DONE
if [%CONFIG%]==[] (
	set CONFIG=release
)
if [%CONFIG%]==[release] (
	SET CXXFLAGS=-O3 -DNDEBUG
) ELSE IF [%CONFIG%]==[debug] (
	SET CXXFLAGS=-g -D_DEBUG -DDEBUG -O1
) ELSE IF [%CONFIG%]==[check] (
	SET CXXFLAGS=-O2 -DDEBUG
)
IF ["%CXXFLAGS%"]==[""] (
	SET CXXFLAGS=-O3 -DNDEBUG
)
SET BUILDPATH=build\%CONFIG%

IF %mt%==0 (
	SET CXXFLAGS=%CXXFLAGS% -DWITH_THREADS=0
) ELSE (
	if [%TBB_INCLUDE%]==[] (
		set TBB_INCLUDE=%TBB30_INSTALL_DIR%/include
	)
	if [%TBB_LIB%]==[] (
		set TBB_LIB=%TBB30_INSTALL_DIR%/lib
	)
	IF NOT EXIST "%TBB_INCLUDE%/tbb/tbb.h" (
		ECHO *** Error: TBB include path not set!
		ECHO Use 'configure TBB_INCLUDE=^<path_to_tbb^>/include'
		GOTO EXIT
	)
	IF NOT EXIST "%TBB_LIB%/tbb.lib" (
		ECHO *** Error: TBB library path not set or '%TBB_LIB%/tbb.lib' not found!
		ECHO Use 'configure TBB_LIB=^<path_to_tbb_library^>'
		GOTO EXIT
	)
	SET CXXFLAGS=%CXXFLAGS% -DWITH_THREADS=1 -I"%TBB_INCLUDE%"
	SET LDFLAGS=%LDFLAGS% -L"%TBB_LIB%" -Xlinker -rpath -Xlinker "%TBB_LIB%"
	SET LDLIBS=-ltbb 
	SET BUILDPATH=%BUILDPATH%_mt
)
SET CXXFLAGS=%CXXFLAGS%
IF %static%==1 (
	SET LDFLAGS=%LDFLAGS% -static
	SET BUILDPATH=%BUILDPATH%_static
)
IF NOT %machine%==0 (
	SET LDFLAGS=%LDFLAGS% -m%machine%
	SET CXXFLAGS=%CXXFLAGS% -m%machine%
	SET BUILDPATH=%BUILDPATH%_m%machine%
)
IF [%BIN_DIR%]==[] (
    SET INSTALLPATH=%PREFIX%\bin
) ELSE (
    SET INSTALLPATH=%BIN_DIR%
)

REM create & prepare build hierarchy
IF NOT EXIST "%BUILDPATH%" goto CREATEDIR
RD /S /Q "%BUILDPATH%"
:CREATEDIR
MKDIR "%BUILDPATH%\app"
MKDIR "%BUILDPATH%\bin"
SET INCLUDES=
SET LIB_TARGETS=
FOR %%A IN (%LIBS%) DO (
	MKDIR "%BUILDPATH%\%%A\lib"
	SET INCLUDES=-I$^(PROJECT_ROOT^)/%%A !INCLUDES!
	SET LIB_TARGETS=%%A/lib/%%A.a !LIB_TARGETS!
)
SET ROOTPATH=../..
SET TARGET=bin/clasp.exe
cd "%BUILDPATH%"
REM write FLAGS
if ["%CXX%"]==[""] (
echo CXX         ?= g++#         >> FLAGS
) ELSE (
echo CXX         := %CXX%#       >> FLAGS
)
echo CXXFLAGS    := %CXXFLAGS%# >> FLAGS
echo WARNFLAGS   := -W -Wall#   >> FLAGS
echo LDFLAGS     := %LDFLAGS%#  >> FLAGS
echo.#>> FLAGS

REM create Makefiles
SET TOOL_PATH=..\..\tools
SET LIB_MAKES=%TOOL_PATH%\Base.in %TOOL_PATH%\LibRule.in %TOOL_PATH%\BaseRule.in
SET PRO_MAKES=%TOOL_PATH%\Base.in %TOOL_PATH%\ProjRule.in %TOOL_PATH%\BaseRule.in
FOR %%A IN (%LIBS%) DO type %LIB_MAKES% > %%A\Makefile 2>nul
type %PRO_MAKES% > Makefile 2>nul 

REM write project config
echo PROJECT_ROOT := %ROOTPATH%#           >> .CONFIG
echo TARGET       := %TARGET%#             >> .CONFIG
echo FLAGS        := FLAGS#                >> .CONFIG
echo SOURCE_DIR   := $(PROJECT_ROOT)/app#  >> .CONFIG
echo INCLUDE_DIR  := $(PROJECT_ROOT)/app#  >> .CONFIG
echo OUT_DIR      := app#                  >> .CONFIG
echo INCLUDES     := %INCLUDES%#           >> .CONFIG
echo SUBDIRS      := %LIBS%#               >> .CONFIG
echo LIBS         := %LIB_TARGETS%#        >> .CONFIG
echo LDLIBS       := %LDLIBS%#            >> .CONFIG
echo INSTALL_DIR  := "%INSTALLPATH%"#     >> .CONFIG
echo INSTALL      := copy#                >> .CONFIG
if not [%POST_BUILD%]==[] (
ECHO POST_BUILD   := %POST_BUILD%#   >> .CONFIG
)
echo.#>>.CONFIG

REM write lib configs
FOR %%A IN (%LIBS%) DO (
set x=%%A
echo PROJECT_ROOT := %ROOTPATH%/..#      >> %%A\.CONFIG
echo TARGET       := lib/%%A.a#          >> %%A\.CONFIG
echo LDLIBS       := %LDLIBS%#           >> %%A\.CONFIG
echo FLAGS        := ../FLAGS#           >> %%A\.CONFIG
echo INCLUDES     := !INCLUDES!#         >> %%A\.CONFIG
echo SOURCE_DIR   := $^(PROJECT_ROOT^)/%%A/src#    >> %%A\.CONFIG
echo INCLUDE_DIR  := $^(PROJECT_ROOT^)/%%A/!x:~3!# >> %%A\.CONFIG
echo.# >> %%A\.CONFIG
)
REM DONE

ECHO.
ECHO Configuration successfully written to %BUILDPATH%.
ECHO Make flags written to "%BUILDPATH%\FLAGS".
ECHO.
ECHO To compile clasp type:
ECHO   cd "%BUILDPATH%"
ECHO   make
ECHO.
ECHO To install clasp afterwards type:
ECHO   make install
ECHO or copy "%BUILDPATH%\%TARGET%" to a directory of your choice.
IF EXIST "%INSTALLPATH%" goto skip_warn
ECHO.
ECHO Note: Path "%INSTALLPATH%" does not exist!
ECHO       Installation will fail unless it is first created!
:skip_warn
ECHO.
ECHO Note: 'make' must correspond to GNU Make 3.8 or later.
ECHO.

:EXIT
(set static=)
(set machine=)
(set mt=)
(set PREFIX=)
(set BIN_DIR=)
(set CONFIG=)
(set LDFLAGS=)
(set LDLIBS=)
(set BUILDPATH=)
(set CXXFLAGS=)
(set INSTALLPATH=)
(set CXX=)
(set TARGET=)
(set POST_BUILD=)
(set LIB_MAKES=)
(set PRO_MAKES=)
(set TOOL_PATH=)
(set TBB_LIB=)
(set TBB_INCLUDE=)
(set LIBS=)
(set INCLUDES=)
(set LIB_TARGETS=)