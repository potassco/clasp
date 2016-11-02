set(files
	clasp_app.cpp
	clasp_app.h
	main.cpp)
add_executable(clasp ${files})
target_link_libraries(clasp libclasp)
set_target_properties(clasp PROPERTIES FOLDER exe)
