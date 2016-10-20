# libpotassco

libpotassco is a small C++ utility library used by various potassco projects
that mostly provides functions and types for
 - parsing, writing, and converting logic programs in [aspif][aspif] and smodels format,
 - passing information between a grounder and a solver,
 - defining and parsing command-line options and for creating command-line applications.

Furthermore, it comes with the tool `lpconvert` that converts between aspif and smodels format.

libpotassco is part of the potassco project. For further information please visit:

  http://potassco.org/

## Installation

The preferred way to build and install libpotassco is to use [CMake][cmake] 
version 3.1 or later.

The following options can be used to configure the build:
  
    LIB_POTASSCO_BUILD_APP  : whether or not to build the lpconvert tool
    LIB_POTASSCO_BUILD_TESTS: whether or not to build unit tests

For example, to build libpotassco in release mode in directory `<dir>`:

    cmake -H. -B<dir>
    cmake --build <dir>

To install libpotassco under `${CMAKE_INSTALL_PREFIX}`:

    cmake -H. -B<dir> -DCMAKE_BUILD_TYPE="buildtype" -DLIB_POTASSCO_BUILD_TESTS=OFF
    cmake --build <dir> --target install

Repeat for each build type you need (e.g. `Debug` or `Release`).

To use libpotassco in a cmake-based project either:

- Place the library inside your project, e.g. using [git submodules](http://git-scm.com/docs/git-submodule).
- Call `add_subdirectory(<path_to_libpotassco>)`.

or, if libpotassco is installed:
- Call `find_package(potassco <major>.<minor> CONFIG)`.

Finally, call `target_link_libraries(your_target PUBLIC potassco)` to link to the potassco library.

## Documentation
Source code documentation can be generated with [Doxygen][doxygen].
Either explicitly:
  
    cd libclasp/doc/api
    doxygen clasp

or via the `doc` target when using cmake.

[![Build Status master](https://badges.herokuapp.com/travis/potassco/libpotassco?branch=master&label=master)](https://travis-ci.org/potassco/libpotassco?branch=master)
  
[aspif]: http://www.cs.uni-potsdam.de/wv/pdfformat/gekakaosscwa16b.pdf  "Aspif specification"
[cmake]: https://cmake.org/
[doxygen]: http://www.stack.nl/~dimitri/doxygen/