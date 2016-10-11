SHELL        ?= /bin/sh
AR           ?= ar
CXX          ?= g++
BUILD_DIR    ?= .
ROOT_DIR     ?= ..
CXXFLAGS     ?= -O3 -DNDEBUG
FLAGS        ?=
LIBS         ?= $(ROOT_DIR)/lib/libclasp.a
ifneq ($(FLAGS),)
-include $(FLAGS)
endif
INCLUDE      := -I $(ROOT_DIR) 
ALL_CXXFLAGS := -W -Wall $(INCLUDE) $(CXXFLAGS) 
TARGET       := $(BUILD_DIR)/example
SOURCES      := $(patsubst $(ROOT_DIR)/example/%.cpp,%.cpp,$(wildcard $(ROOT_DIR)/example/*.cpp))
DEPS         := $(patsubst %.cpp,$(BUILD_DIR)/%.dep, $(SOURCES))
OBJECTS      := $(patsubst %.cpp,$(BUILD_DIR)/%.o, $(SOURCES))
vpath %.cpp $(ROOT_DIR)/example
vpath %.h   $(ROOT_DIR)/example

$(TARGET):  $(FLAGS) $(LIBS) $(DEPS) $(OBJECTS)
	$(CXX) $(WARNFLAGS) $(CXXFLAGS) $(LDFLAGS) $(OBJECTS) $(LIBS) -o $(TARGET)

$(LIBS):
	$(MAKE) -C $(ROOT_DIR) "BUILD_DIR=lib"

ifneq ($(MAKECMDGOALS),clean)
-include $(DEPS)
endif

$(BUILD_DIR)/%.dep: %.cpp $(FLAGS)
	$(CXX) $(ALL_CXXFLAGS) -MT $(BUILD_DIR)/$*.o -MM $< > $@

$(BUILD_DIR)/%.o: %.cpp $(FLAGS)
	$(CXX) $(ALL_CXXFLAGS) -c $< -o $@


.PHONY:	clean 
ifeq ($(findstring Windows,$(OS)),)
clean:
	@$(RM) $(TARGET)
	@$(RM) $(OBJECTS)
	@$(RM) $(DEPS)
else
RM := del /F /Q
clean:
	@$(RM) $(subst /,\,$(TARGET))  2>nul
	@$(RM) $(subst /,\,$(OBJECTS)) 2>nul
	@$(RM) $(subst /,\,$(DEPS))    2>nul
endif
