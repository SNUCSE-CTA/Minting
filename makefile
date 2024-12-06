CXX=g++
CXXFLAGS=-std=c++17 -O3 -w -DNDEBUG

TARGETS=Minting

all: $(TARGETS)

clean:
	rm -f Minting

Minting: main.cpp graph.h process.h config.h markedCS.h extension.h
	$(CXX) $(CXXFLAGS) main.cpp -o Minting
