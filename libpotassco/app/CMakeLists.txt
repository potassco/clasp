add_executable(lpconvert lpconvert.cpp)
target_link_libraries(lpconvert potassco)

install(TARGETS lpconvert EXPORT lpconvert DESTINATION "bin")

