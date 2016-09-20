# potassco-config.cmake - package configuration file
# Note: Adapted from Jonathan Müller's blog post on supporting CMake install:
# https://foonathan.github.io/blog/2016/03/03/cmake-install.html

get_filename_component(SELF_DIR "${CMAKE_CURRENT_LIST_FILE}" PATH)
include(${SELF_DIR}/${CMAKE_BUILD_TYPE}/potassco_lp.cmake)

