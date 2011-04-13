#include<stdio.h>
struct str{
	int a;
	int b[10];
	int *c;
	struct str* next;
}st;
int main(){
	int a[10];
	char b[10][10];
	char c[]="a";
	int i=2;
	st.a=0;
	st.b[1]=1;
	struct str* pst = &st;
	pst -> b[st.a]=2;
	struct str** ppst = &pst;
	(*ppst) -> b[3]=3;
	pst = pst ->next;
	pst->next->b[2]=4;
	a[1] =0;
	*(a+2)=1;
	a[i]=2;
	*(a+i)=3;
	*((char*)a+i)=3;
	b[3][2]=0;
	*(*(b+3)+2)=1;
	b[st.a][a[1]]=2;
	i=b[i][i];
	b[i][i]=i;
	pst -> c=a;
	c[3]='0';
	*(c+2)='1';
	printf("%d\n",a[2]);
	printf("%d\n",b[3][2]);
	printf("%s\n",c);
	char* f;
	f = c;
	f = b[2];
	char* e = "abc";
	e[0] = 'd';
	return 0;
}
