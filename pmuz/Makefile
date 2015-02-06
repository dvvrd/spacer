SRC=pmuz.cpp
OBJ=$(patsubst %.cpp,%.o,$(SRC))
Z3_OBJS=$(shell find ../build -name '*.o')
CC=gcc
CFLAGS=-static -std=c++11 -Wall -O3 -g
CXX=g++
LIB=-lpthread -fopenmp -lrt
INCLUDE=-I ../src/api

all : pmuz

pmuz : $(OBJ) libz3.a
	$(CXX) $(CFLAGS) $(INCLUDE) -o $@ $^ $(LIB)

%.d : %.cpp
	$(CXX) -MM -MT $(@:%.d=%.o) -o $@ $(CFLAGS) $(INCLUDE) $<

.cpp.o:	
	$(CXX) -c $(CFLAGS) $(INCLUDE) $<

libz3.a : $(Z3_OBJS)
	@echo creating libz3.a ...
	@ar rc libz3.a $(Z3_OBJS)

clean :
	rm -f *.o *.d libz3.a pmuz

-include $(SRC:%.cpp=%.d)
