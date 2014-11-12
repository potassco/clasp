#!/bin/bash

# OPTIONS
static=0
machine=0
mt=0
rpath=0
PREFIX="/usr/local"
BIN_DIR=""
CONFIG=""
# CONFIGURATION
CXXFLAGS="${CXXFLAGS}"
LDFLAGS="${LDFLAGS}"
LDLIBS=""
BUILDPATH=""
INSTALLPATH=""
CXX=""
POST_BUILD=""
TBB_INCLUDE=""
TBB_LIB=""
while [[ $# > 0 ]]; do
	case $1 in
		CXXFLAGS=*) CXXFLAGS=`echo "$1"| sed  's/^[A-Z]*=*//'`
			;;
		LDFLAGS=*) LDFLAGS=`echo "$1"| sed  's/^[A-Z]*=*//'`
			;;
		CXX=*) CXX=`echo "$1"| sed  's/^[A-Z]*=*//'`
			;;
		TBB_INCLUDE=*) TBB_INCLUDE=`echo "$1"| sed  's/^[A-Z_]*=*//'`
			;;
		TBB_LIB=*) TBB_LIB=`echo "$1"| sed  's/^[A-Z_]*=*//'`
			;;
		"--strip")
			POST_BUILD="strip"
			;;
		"--static")
			static=1
			;;
		"--with-mt")
			mt=1
			;;
		"--set-rpath")
			rpath=1
			;;
		"--m32")
			machine=32
			;;
		"--m64")
			machine=64
			;;
		--bindir*|--prefix*|--config*)
			T=`echo "$1"| sed 's/^--[a-z-]*=*//'`
			A=$1
			if [ -z "$T" ]; then
				if [ -z "$2" ]; then
					echo "error: required parameter missing after '$1'"
					exit 1
				fi
				T=$2
				shift
			fi
			case $A in
				--bindir*) BIN_DIR=$T;;
				--prefix*) PREFIX=$T;;
				--config*) CONFIG=$T;;
			esac
			;;
		"--clean")
			rm -rf build/
			exit 0
			;;
		"--help")
			echo
			echo "$0 [options]"
			echo
			echo "  --help             : show this help"
			echo "  --prefix=PREFIX    : set install prefix to PREFIX"
			echo "    Default: '/usr/local'"
			echo "  --bindir=PATH      : set install path to PATH"
			echo "    Default: '${PREFIX}/bin'"
			echo
			echo "  --config=NAME      : set configuration to NAME"
			echo "    NAME=release     : configure for optimized release version"
			echo "    NAME=debug       : configure for debug version"
			echo "    NAME=check       : configure for release version with assertions enabled"
			echo "    <NAME>           : configure for custom configuration with name <NAME>"
			echo
			echo "  --with-mt          : enable multi-thread support (see below)"
			echo "  --set-rpath        : store path to shared libraries in binary header"
			echo "  --static           : link statically (if supported)"
			echo "  --m32              : force 32-bit binary (if supported)"
			echo "  --m64              : force 64-bit binary (if supported)"
			echo "  --strip            : discard symbols (calls strip after build)"
			echo "  --clean            : remove all generated files"
			echo
			echo "Note: Multi-thread support currently requires Intel® Threading Building Blocks >= 3.x."
			echo "      Use option --with-mt and either set TBB30_INSTALL_DIR environment variable or"
			echo "      explicitly set include and/or library path via:"
			echo "  $0 --with-mt TBB_INCLUDE=<path_to_tbb_include> TBB_LIB=<path_to_tbb_lib>"
			echo
			echo "Note: To create a custom configuration call $0 like this: "
			echo "  $0 --config=my_config CXX=my_gcc CXXFLAGS=my_cxxflags LDFLAGS=my_ldflags"
			echo
			exit 0
			;;
		*)
			echo "*** Error: unknown option $1"
			echo "type '$0 --help' for an overview of supported options"
			exit 1
	esac
	shift
done
if [ -z "$CONFIG" ]; then
	CONFIG="release"
fi
case $CONFIG in
	release) CXXFLAGS="-O3 -DNDEBUG" ;;
	debug)   CXXFLAGS="-g -D_DEBUG -DDEBUG -O1" ;;
	check)   CXXFLAGS="-O2 -DDEBUG" ;;
	*)
		if [ -z "$CXXFLAGS" ]; then
			CXXFLAGS="-O3 -DNDEBUG"
		fi
		;;
esac

BUILDPATH="build/${CONFIG}"

if [[ $mt == 0 ]]; then
	CXXFLAGS="${CXXFLAGS} -DWITH_THREADS=0"
else
	# try to find tbb headers
	echo -ne "Checking for TBB include path..."
	for i in "$TBB_INCLUDE" "$TBB30_INSTALL_DIR/include" "/opt/intel/tbb/include" "/usr/local/include" "/usr/include" "/opt/local/include"; do
		TBB_INCLUDE=""
		if [ -f "$i/tbb/tbb.h" ]; then
			TBB_INCLUDE="$i"
			echo "$TBB_INCLUDE"
			break
		fi
	done
	if [ -z "$TBB_INCLUDE" ]; then
		echo "FAIL"
		echo "*** Error: TBB include path not set!"
		echo "use '$0 TBB_INCLUDE=<path_to_tbb_include>'"
		exit 1
	fi
	# try to find tbb lib
	echo -ne "Checking for TBB library path..."
	for i in "$TBB_LIB" "$TBB30_INSTALL_DIR/lib" "/opt/intel/tbb/lib" "/usr/local/lib" "/usr/lib" "/opt/local/lib" ; do
		TBB_LIB=""
		if [ -f "$i/libtbb.so" -o -f "$i/libtbb.dylib" ]; then
			TBB_LIB="$i"
			echo "$TBB_LIB"
			break
		fi
	done
	if [ -z "$TBB_LIB" ]; then
		echo "FAIL"
		echo "*** Error: TBB library path not set or 'libtbb.{so,dylib}' not found!"
		echo "use '$0 TBB_LIB=<path_to_tbb_library>'"
		exit 1
	fi
	CXXFLAGS="${CXXFLAGS} -DWITH_THREADS=1 -I\"${TBB_INCLUDE}\""
	LDFLAGS="${LDFLAGS} -L\"${TBB_LIB}\""
	LDLIBS="-ltbb"
	if [[ $rpath == 1 ]]; then
		LDFLAGS="${LDFLAGS} -Xlinker -rpath -Xlinker \"${TBB_LIB}\""
	fi
	BUILDPATH="${BUILDPATH}_mt"
fi

CXXFLAGS="${CXXFLAGS}"
if [[ $static == 1 ]]; then
	LDFLAGS="${LDFLAGS} -static"
	BUILDPATH="${BUILDPATH}_static"
fi
if [[ $machine != 0 ]]; then
	LDFLAGS="${LDFLAGS} -m${machine}"
	CXXFLAGS="${CXXFLAGS} -m${machine}"
	BUILDPATH="${BUILDPATH}_m${machine}"
fi
if [ -z "$BIN_DIR" ]; then
	INSTALLPATH="${PREFIX}/bin"
else
	INSTALLPATH=$BIN_DIR
fi

# create & prepare build hierarchy
ROOTPATH="../.."
LIBS="libclasp libprogram_opts"
LIB_TARGETS=""
LIB_INCLUDES=""
mkdir -p "$BUILDPATH/app"
mkdir -p "$BUILDPATH/bin"
for lib in $LIBS; do 
	mkdir -p "$BUILDPATH/$lib/lib" 
	LIB_TARGETS="${LIB_TARGETS} ${lib}/lib/${lib}.a"
	LIB_INCLUDES="-I\$(PROJECT_ROOT)/${lib} ${LIB_INCLUDES}"
done
cd "$BUILDPATH"
rm -f .CONFIG Makefile FLAGS
for lib in $LIBS; do 
	rm -f $lib/.CONFIG $lib/Makefile
done
# write FLAGS
touch FLAGS
if [ ! -z "$CXX" ]; then
echo "CXX         := ${CXX}"      >> FLAGS
else
echo "CXX         ?= g++"         >> FLAGS
fi
echo "CXXFLAGS    := ${CXXFLAGS}" >> FLAGS
echo "WARNFLAGS   := -W -Wall"    >> FLAGS
echo "LDFLAGS     := ${LDFLAGS}"  >> FLAGS
echo ""                           >> FLAGS
# create Makefiles
LIB_MAKES="${ROOTPATH}/tools/Base.in ${ROOTPATH}/tools/LibRule.in ${ROOTPATH}/tools/BaseRule.in"
PRO_MAKES="${ROOTPATH}/tools/Base.in ${ROOTPATH}/tools/ProjRule.in ${ROOTPATH}/tools/BaseRule.in"
for lib in $LIBS; do 
	cat $LIB_MAKES >> $lib/Makefile
done
cat $PRO_MAKES >> Makefile
# write project config
touch  .CONFIG
echo "PROJECT_ROOT := $ROOTPATH"            >> .CONFIG
echo "TARGET       := bin/clasp"            >> .CONFIG
echo "FLAGS        := FLAGS"                >> .CONFIG
echo "SOURCE_DIR   := \$(PROJECT_ROOT)/app" >> .CONFIG
echo "INCLUDE_DIR  := \$(PROJECT_ROOT)/app" >> .CONFIG
echo "OUT_DIR      := app"                  >> .CONFIG
echo "INCLUDES     := ${LIB_INCLUDES}"      >> .CONFIG
echo "SUBDIRS      := ${LIBS}"              >> .CONFIG
echo "LIBS         := ${LIB_TARGETS:1}"     >> .CONFIG
echo "LDLIBS       := ${LDLIBS}"            >> .CONFIG
echo "INSTALL_DIR  := \"${INSTALLPATH}\""   >> .CONFIG
if [ ! -z "$POST_BUILD" ]; then
echo "POST_BUILD  := $POST_BUILD"           >> .CONFIG
fi
echo ""                                     >> .CONFIG
# write lib configs
for lib in $LIBS; do
	touch $lib/.CONFIG
	echo "PROJECT_ROOT := ${ROOTPATH}/.."      >> $lib/.CONFIG
	echo "TARGET       := lib/${lib}.a"        >> $lib/.CONFIG
	echo "FLAGS        := ../FLAGS"            >> $lib/.CONFIG
	echo "TEST_DIR     := \$(PROJECT_ROOT)/${lib}/tests" >> $lib/.CONFIG
	echo "TEST_TARGET  := ./test-lib"          >> $lib/.CONFIG
	echo "LDLIBS       := ${LDLIBS}"           >> $lib/.CONFIG
	echo "SOURCE_DIR   := \$(PROJECT_ROOT)/${lib}/src" >> $lib/.CONFIG
	echo "INCLUDE_DIR  := \$(PROJECT_ROOT)/${lib}/${lib:3}" >> $lib/.CONFIG
	echo "INCLUDES     := ${LIB_INCLUDES}" >> $lib/.CONFIG
	echo "" >> $lib/.CONFIG
done
# DONE
echo
echo "Configuration successfully written to ${BUILDPATH}."
echo "Make flags written to ${BUILDPATH}/FLAGS."
echo
echo "To compile clasp type:"
echo "  cd ${BUILDPATH}"
echo "  make"
echo
echo "To install clasp afterwards type:"
echo "  make install"
echo "or copy '${BUILDPATH}/clasp' to a directory of your choice."
if [ ! -d "$INSTALLPATH" ]; then
echo
echo "Note: install path '$INSTALLPATH' does not exist"
echo "      'make install' will fail unless it is first created!"
fi
echo
echo "Note: \"make\" must correspond to GNU Make 3.8 or later."
echo

