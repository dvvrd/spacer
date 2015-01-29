all : pmuz

pmuz : pmuz.cpp
	ar rc libz3.a `find ../build -name "*.o"`
	g++ -I ../run/unstable/include -static -o pmuz pmuz.cpp libz3.a -lpthread  -fopenmp -lrt

clean :
	rm -f pmuz
