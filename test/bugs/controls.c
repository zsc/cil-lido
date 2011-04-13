//#include<stdio.h>
int main (int argc,char** argv){

	if(argc>0){
		exit (-1);
	}

	int i;
	int s=0;
	int j;
	for (i = 0; i < 100; ++i) {
		for (j = 0; j < 100; ++j) {
			if(j==30)break;
			s+=i;
		}

	}
	return 0;
}
