CXX = g++
NVCC = nvcc

CXXFLAGS = -O3 -march=native -fopenmp -std=c++17
NVCCFLAGS = -O3 -std=c++17

all: primitive_rtrt_cpu primitive_rtrt_cpu_enum primitive_rtrt_cuda_ranked primitive_mk_cuda

primitive_rtrt_cpu: scripts/primitive_rtrt_cpu.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

primitive_rtrt_cpu_enum: scripts/primitive_rtrt_cpu_enum.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

primitive_rtrt_cuda_ranked: scripts/primitive_rtrt_cuda_ranked.cu
	$(NVCC) $(NVCCFLAGS) $< -o $@

primitive_mk_cuda: scripts/primitive_mk_cuda.cu
	$(NVCC) $(NVCCFLAGS) $< -o $@

clean:
	rm -f primitive_rtrt_cpu primitive_rtrt_cpu_enum primitive_rtrt_cuda_ranked primitive_mk_cuda

.PHONY: all clean
