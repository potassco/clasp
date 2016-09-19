SHELL = /bin/sh
CXX = g++
CXXFLAGS = 
INCLUDE = -I../ -I.
ALL_CXXFLAGS = $(INCLUDE) $(CXXFLAGS)
TARGET = clasp_test
CPPUNIT_INCLUDE:=~/cppunit-1.12.1/include
CPPUNIT_LIB:=~/cppunit-1.12.1/lib/libcppunit.a
clasp_lib:=../lib/libclasp.a
sources:=$(wildcard *.cpp)
objects:=$(patsubst %.cpp,%.o,$(sources))
deps:=$(patsubst %.cpp,%.dep,$(sources))

$(TARGET):	$(clasp_lib) $(objects) $(deps)
	$(CXX) $(ALL_CXXFLAGS) $(objects) $(clasp_lib) $(CPPUNIT_LIB) -o $(TARGET)

ifneq ($(MAKECMDGOALS),clean)
  ifneq ($(MAKECMDGOALS),distclean)
    -include $(deps)
  endif
endif

%.o:	%.cpp
	$(CXX) $(ALL_CXXFLAGS) -I $(CPPUNIT_INCLUDE) -c $< -o $@

%.dep: %.cpp
	$(CXX) $(INCLUDE) -I $(CPPUNIT_INCLUDE) -MM $< > $@

$(clasp_lib):
	$(MAKE)  -C ../src

.PHONY:	clean distclean
clean:
	@$(RM) $(TARGET)
	@$(RM) $(objects)
	@$(RM) $(deps)

distclean: clean


