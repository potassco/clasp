set(files
	example.h
	example1.cpp
	example2.cpp
	example3.cpp
	example4.cpp
	main.cpp)
add_executable(examples ${files})
target_link_libraries(examples clasp)

