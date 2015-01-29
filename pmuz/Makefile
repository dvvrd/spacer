all : pmuz

pmuz : pmuz.cpp libz3.a
	g++ -I ../run/unstable/include -static -o pmuz pmuz.cpp libz3.a -lpthread  -fopenmp -lrt
