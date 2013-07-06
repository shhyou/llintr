CXXFLAGS = -std=c++11 -Wall -Wshadow -Wextra -Wconversion -pedantic -MMD

apps = \
	vm.exe

units = \
	runtime

all: $(apps)

clean:
	-rm -f $(apps) $(apps:.exe=.o) $(apps:.exe=.d) $(units:=.o) $(units:=.d)

clean-del:
	-del /Q $(apps) $(apps:.exe=.o) $(apps:.exe=.d) $(units:=.o) $(units:=.d)

$(apps): %.exe: %.o $(units:=.o)
	g++ -o $@ $^ $(CXXFLAGS)

-include $(units:=.d) $(apps:.exe=.d)
