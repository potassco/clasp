cmake_minimum_required(VERSION 3.1)
project(LIB_POTASSCO VERSION 1.0 LANGUAGES CXX)
if (POLICY CMP0063)
	cmake_policy(SET CMP0063 NEW)
endif()
# enable folders in IDEs like Visual Studio
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

option(LIB_POTASSCO_BUILD_TESTS "whether or not to build tests" 1)
option(LIB_POTASSCO_BUILD_APP   "whether or not to build lpconvert tool" 1)
set(include_dest  "include/potassco-${LIB_POTASSCO_VERSION}")
set(main_lib_dest "lib/potassco-${LIB_POTASSCO_VERSION}")
set(lib_dest      "${main_lib_dest}/${CMAKE_BUILD_TYPE}")

add_subdirectory(src)
if(LIB_POTASSCO_BUILD_TESTS)
	enable_testing()
	add_subdirectory(tests)
endif()
if(LIB_POTASSCO_BUILD_APP)
	add_subdirectory(app)
endif()

# optional doc target
find_package(Doxygen)
if(DOXYGEN_FOUND)
	set(doxyfile "${CMAKE_CURRENT_SOURCE_DIR}/doc/Doxyfile")
	add_custom_target(doc_potassco
		COMMAND ${DOXYGEN_EXECUTABLE} ${doxyfile}
		WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/doc"
		COMMENT "Generating documentation..."
		VERBATIM)
	set_target_properties(doc_potassco PROPERTIES FOLDER doc)
endif()

# export
configure_file(cmake/potassco-config-version.cmake.in
	${CMAKE_CURRENT_BINARY_DIR}/potassco-config-version.cmake
	@ONLY)
install(FILES cmake/potassco-config.cmake ${CMAKE_CURRENT_BINARY_DIR}/potassco-config-version.cmake DESTINATION "${main_lib_dest}")
install(EXPORT potassco     DESTINATION "${lib_dest}")

