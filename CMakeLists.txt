cmake_minimum_required(VERSION 3.1)
project(CLASP VERSION 3.2.0 LANGUAGES CXX)
# Enable folders in IDEs like Visual Studio
set_property(GLOBAL PROPERTY USE_FOLDERS ON)
if (POLICY CMP0063)
	cmake_policy(SET CMP0063 NEW)
endif()
if (NOT CMAKE_BUILD_TYPE)
	message(STATUS "No build type selected, using 'Release'")
	set(CMAKE_BUILD_TYPE "Release")
endif()

# Configuration options
option(CLASP_BUILD_APP          "whether or not to build the clasp application" ON)
option(CLASP_BUILD_TEST         "whether or not to build clasp unit tests (requires CppUnit)" ON)
option(CLASP_BUILD_EXAMPLES     "whether or not to build examples" OFF)
option(CLASP_BUILD_WITH_THREADS "whether or not to build clasp with threading support (requires C++11)" ON)
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
set(clasp_include_dest  "include/clasp-${CLASP_VERSION}")
set(clasp_main_lib_dest "lib/potassco-${CLASP_VERSION}")
set(clasp_lib_dest      "${clasp_main_lib_dest}/${CMAKE_BUILD_TYPE}")


# C++11 is required for building with threads
if (CLASP_BUILD_WITH_THREADS)
	set(CMAKE_CXX_STANDARD 11)
	set(CMAKE_CXX_STANDARD_REQUIRED ON)
	set(CMAKE_CXX_EXTENSIONS OFF)
	# some versions of findThreads will fail if C in not enabled
	enable_language(C)
	find_package(Threads REQUIRED)
endif()

# Check for and optionally build external dependency
find_package(potassco 1.0 QUIET CONFIG)
if (NOT potassco_FOUND)
	message("Potassco not found. Cloning...")
	execute_process(COMMAND git submodule update --init WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR})
	add_subdirectory(libpotassco)
endif()

# Build clasp library
add_subdirectory(src)

# Build optional targets
if(CLASP_BUILD_TEST)
	find_package(CppUnit)
	if (NOT CPPUNIT_FOUND)
		message(FATAL_ERROR "CppUnit not found - set path in cache or disable unit tests!")
	endif()
	enable_testing()
	add_subdirectory(tests)
endif()
# optional doc target
find_package(Doxygen)
if(DOXYGEN_FOUND)
	set(doxyfile "${CMAKE_CURRENT_SOURCE_DIR}/doc/api/clasp")
	add_custom_target(doc_clasp
		COMMAND ${DOXYGEN_EXECUTABLE} ${doxyfile}
		WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/doc/api"
		COMMENT "Generating documentation..."
		VERBATIM)
	set_target_properties(doc_clasp PROPERTIES FOLDER doc)
endif()

if(CLASP_BUILD_APP)
	add_subdirectory(app)
endif()

if(CLASP_BUILD_EXAMPLES)
	add_subdirectory(examples)
endif()

# Export
configure_file(cmake/clasp-config-version.cmake.in
	${CMAKE_CURRENT_BINARY_DIR}/clasp-config-version.cmake
	@ONLY)
install(FILES cmake/clasp-config.cmake ${CMAKE_CURRENT_BINARY_DIR}/clasp-config-version.cmake DESTINATION "${clasp_main_lib_dest}")
install(EXPORT clasp DESTINATION "${clasp_lib_dest}")


