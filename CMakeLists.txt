cmake_minimum_required(VERSION 2.6)
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/tools")
project(clasp)
find_package(TBB)
include_directories (libclasp libprogram_opts)

if(NOT TBB_FOUND)
	MESSAGE (STATUS "TBB not found. Building without threads.")
	add_definitions( -DWITH_THREADS=0 )
else(NOT TBB_FOUND)
	MESSAGE (STATUS "TBB found. Building with threads.")
	add_definitions( -DWITH_THREADS=1 )
	link_directories(${TBB_LIBRARY_DIRS})

endif(NOT TBB_FOUND)
add_subdirectory(libclasp)
add_subdirectory(libprogram_opts)
add_subdirectory(app)

