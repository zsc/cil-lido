int main(){
	int i,j,k;
	char ll_i,tmp,tmp2;
	char* yy;
    j = 0;
    tmp = yy[j];
    while ( ll_i != tmp ) {
       j++;
       tmp2 = tmp;
       tmp = yy[j];
       yy[j] = tmp2;
    };
    yy[0] = tmp;

	for(i=0;i<10;i++) printf("d\n",i);
	for(i=0;i<11;) printf("d\n",i);
	for(i=0;;i++) printf("d\n",i);
	for(;i<12;i++) printf("d\n",i);
	for(i=13;i;i--) printf("d\n",i);
	while(i<14) {
		i++;
		printf("d\n",i);
	}
	while(i<15) {
		i=1-i;
		printf("d\n",i);
	}
	while(i<16) {
		i=1+i;
		printf("d\n",i);
	}
	while(i<17) {
		i=1-i;
		printf("d\n",i);
		if(i>3)break;
	}

}
