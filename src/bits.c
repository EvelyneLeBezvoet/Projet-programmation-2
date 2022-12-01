// This program accompanies Question 1.4.

#include <stdio.h>

typedef unsigned long int ulong;

void print_binary (char *prefix, ulong x, int bits)
{
	ulong b = 1 << (bits-1);
	printf("%s",prefix);
	while (b)
	{
		printf("%c",(x & b)? '1' : '0');
		b = b >> 1;
	}
	printf("\n");
}

int main ()
{
	unsigned int n,m;
	printf("Give me an integer (8 bits) : ");
	scanf("%d",&n);
	n = n & 0xff;
	print_binary("n=",n,8);

	m = ((n * 0x0202020202) & 0x010884422010) % 1023;
	
	print_binary("m=",m,8);
	
}
