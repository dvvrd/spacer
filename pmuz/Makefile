Z3_OBJS=$(shell find ../build -name '*.o')

all : pmuz

libz3.a : $(Z3_OBJS)
	@echo creating libz3.a ...
	@ar rc libz3.a $(Z3_OBJS)

pmuz : pmuz.cpp libz3.a
	g++ -I ../src/api -static -o pmuz pmuz.cpp libz3.a -lpthread  -fopenmp -lrt

clean :
	rm -f libz3.a pmuz
