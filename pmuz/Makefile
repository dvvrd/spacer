all : pmuz

pmuz : pmuz.cpp
	g++ -I ../run/unstable/include -static -o pmuz pmuz.cpp libz3.a -lpthread  -fopenmp -lrt

clean :
	rm -f pmuz
