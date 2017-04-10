# clasp

clasp is an answer set solver for (extended) normal and disjunctive logic programs.
It combines the high-level modeling capacities of answer set programming
with state-of-the-art techniques from the area of Boolean constraint solving.
The primary clasp algorithm relies on conflict-driven nogood learning,
a technique that proved very successful for satisfiability checking (SAT).

As of version 3.2.0, clasp supports:

 - optional parallel (multithreaded) solving,
 - disjunctive logic programs as in [`claspD-2`][claspD2],
 - domain heuristic modifications as in [`hclasp`][hclasp] via option `--heuristic=domain`,
 - unsatisfiable-core based optimization as in `unclasp` via `--opt-strategy`,
 - new asp intermediate format [(aspif)] [aspif],
 - [ASP/SAT/PB modulo acyclicity][acyc] via option `--parse-ext` and a dedicated acyclicity
   constraint propagator,
 - optimization in SAT via option `--parse-ext` and `c minweight l1 w1 ... ln wn 0`.

clasp is written in (mostly) Standard-C++. It was successfully built and run
under Linux (x86-32, x86-64) using gcc/clang and Windows (x86-32, x86-64) using
either Microsoft Visual Studio or MinGW.

Detailed information (including a User's manual), source code,
and pre-compiled binaries are available at: http://potassco.org/

## LICENSE
  clasp is part of the Potassco project.
  It is distributed under the MIT License.
  
  See LICENSE for details regarding the license.

## PACKAGE CONTENTS
    LICENSE        - The MIT License
    CHANGES        - Major changes between versions
    README.md      - This file
    CMakeLists.txt - Configuration file for building clasp with CMake
    cmake/         - Module directory for additional CMake scripts
    app/           - Source code directory of the command-line interface
    clasp/         - Header directory of the clasp library
    src/           - Source code directory of the clasp library
    tests/         - Unit tests of the clasp library
    examples/      - Examples using the clasp library
    libpotassco/   - Directory of the potassco library
    tools/         - Some additional files
  

## BUILDING & INSTALLING
  The preferred way to build clasp is to use [CMake][cmake] version 3.1 or later
  together with a c++ compiler that supports C++11.

  The following options can be used to configure the build:
  
    CLASP_BUILD_APP         : whether or not to build the clasp application
    CLASP_BUILD_TEST        : whether or not to build clasp unit tests
                              (requires CppUnit)
    CLASP_BUILD_EXAMPLES    : whether or not to build examples
    CLASP_BUILD_WITH_THREADS: whether or not to build clasp with threading support
                              (requires C++11)

  For example, to build clasp in release mode in directory `<dir>`:

    cmake -H. -B<dir>
    cmake --build <dir>

  To install clasp afterwards:
  
    cmake --build <dir> --target install

  To set the installation prefix, run
  `cmake` with option `-DCMAKE_INSTALL_PREFIX=<path>`.

  Finally, you can always skip installation and simply copy the
  clasp executable to a directory of your choice.

## DOCUMENTATION
  A User's Guide is available from http://potassco.org/
  
  Source code documentation can be generated with [Doxygen][doxygen].
  Either explicitly:
  
    cd libclasp/doc/api
    doxygen clasp

  or via the `doc_clasp` target when using cmake.

## USAGE
  clasp reads problem instances either from stdin, e.g
  
    cat problem | clasp
  
  or from a given file, e.g
  
    clasp problem

  Beside logic programs, clasp also supports SAT-problems in DIMACS-,
  Max-SAT in (extended) DIMACS-, and PB-problems in OPB and WBO-format.

  Type
  
    clasp --help
  
  to get a basic overview of options supported by clasp or
  
    clasp --help={2,3}
  
  for a more detailed list.

  In addition to printing status information, clasp also
  provides information about the computation via its exit status.
  The exit status is:
    
    10 : if the problem was found to be satisfiable
    20 : if the problem was proved to be unsatisfiable
    0  : if the satisfiability of problem is not known,
         because search was either interrupted or not started
    127: if clasp ran out of memory

Furthermore, the exit status of 1 indicates an error.
  
[claspD2]: http://www.cs.uni-potsdam.de/claspD/
[hclasp]: http://www.cs.uni-potsdam.de/hclasp/
[aspif]: http://www.cs.uni-potsdam.de/wv/pdfformat/gekakaosscwa16b.pdf
[acyc]: http://www.cs.uni-potsdam.de/wv/pdfformat/bogejakasc15b.pdf
[doxygen]: http://www.stack.nl/~dimitri/doxygen/
[cmake]: https://cmake.org/
