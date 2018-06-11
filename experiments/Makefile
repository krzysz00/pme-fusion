CFLAGS = -O2
LIBS = -lflame -lm -lblis

all: fusion_performance_chol_trsm

fusion_performance_chol_trsm: fusion_performance_chol_trsm.o
	gcc $(CFLAGS) $^ -o $@ $(LIBS) $(LDFLAGS)

%.o: %.c
	gcc $(CFLAGS) -o $@ -c $<

clean:
	rm *.o
	rm fusion_performance_chol_trsm

.PHONY: all clean
