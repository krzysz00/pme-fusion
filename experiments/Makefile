CFLAGS = -O2
LIBS = -lflame -lm -lblis -llapack

all: fusion_performance_chol_trsm_blas_lapack fusion_performance_chol_trsm

fusion_performance_chol_trsm: fusion_performance_chol_trsm.o
	gcc $(CFLAGS) $^ -o $@ $(LDFLAGS) $(LIBS)

fusion_performance_chol_trsm_blas_lapack: fusion_performance_chol_trsm_blas_lapack.o
	gcc $(CFLAGS) $^ -o $@ $(LDFLAGS) $(LIBS)

%.o: %.c
	gcc $(CFLAGS) -o $@ -c $<

clean:
	rm *.o
	rm fusion_performance_chol_trsm

.PHONY: all clean
