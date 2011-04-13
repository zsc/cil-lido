#include <stdio.h>

#define N 10
long counters[N] = {0,};
void dump(){
	FILE* fp = fopen("_prof_out","w");
	int i;
	for (i = 0; i < N; ++i) {
		fprintf(fp,"%d,%ld\n",i,counters[i]);
	}
}


int fib(int n){

	counters[0]++;

	if(n<=1) {
		counters[2]++;
		return 1;
	}
	return fib(n-1)+fib(n-2);
}
int main(int argc, char** argv){
	atexit(dump);

	if(argc<=1){
		counters[1]++;
		printf("Need an argument\n");
		return 1;
	}
	int n;
	sscanf(argv[1],"%d",&n);
	printf("fib %d = %d\n",n,fib(n));

	return 0;
}
