all : psmc

psmc : psmc.cpp libz3.a
	g++ -I ../run/unstable/include -static -o psmc psmc.cpp libz3.a -lpthread  -fopenmp -lrt
