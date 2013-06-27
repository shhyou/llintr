CXXFLAGS = -std=c++11 -Wall -Wshadow -Wextra -Wconversion -pedantic -MMD

apps = \
	vm.exe

units = \
	runtime

all: $(apps)

$(apps): %.exe: %.o $(units:=.o)
	g++ -o $@ $^ $(CXXFLAGS)

-include $(units:=.d) $(apps:.exe=.d) 