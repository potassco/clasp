add_executable(lpconvert lpconvert.cpp)
target_link_libraries(lpconvert potassco)
set_property(TARGET lpconvert PROPERTY FOLDER exe)

install(TARGETS lpconvert EXPORT lpconvert DESTINATION "bin")

