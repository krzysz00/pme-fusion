CFLAGS := $(CFLAGS) -O2 -ggdb
MKL_ROOT = /opt/intel/compilers_and_libraries_2018.3.222/linux/mkl
MKL_PKG_CONFIG_PATH := $(PKG_CONFIG_PATH):$(MKL_ROOT)/bin/pkgconfig
MKL_TYPE = mkl-static-lp64-seq

MKL_CFLAGS := $(shell env PKG_CONFIG_PATH=$(MKL_PKG_CONFIG_PATH) pkg-config --cflags $(MKL_TYPE))
MKL_LDFLAGS := $(shell env  PKG_CONFIG_PATH=$(MKL_PKG_CONFIG_PATH) pkg-config --libs $(MKL_TYPE))

all: fusion_performance_chol_trsm_blas_lapack fusion_performance_chol_trsm\
symmetric_inverse

fusion_performance_chol_trsm: fusion_performance_chol_trsm.o
	gcc $(CFLAGS) $^ -o $@ -lflame -lm -lblis

fusion_performance_chol_trsm_blas_lapack: util.o fusion_performance_chol_trsm_blas_lapack.o
	gcc $(MKL_CFLAGS) $(CFLAGS) $^ -o $@ $(LDFLAGS) $(MKL_LDFLAGS)

symmetric_inverse: util.o symmetric_inverse.o
	gcc $(MKL_CFLAGS) $(CFLAGS) $^ -o $@ $(LDFLAGS) $(MKL_LDFLAGS)

%.o: %.c util.h
	gcc $(MKL_CFLAGS) $(CFLAGS) -o $@ -c $<

clean:
	rm *.o
	rm fusion_performance_chol_trsm

.PHONY: all clean
