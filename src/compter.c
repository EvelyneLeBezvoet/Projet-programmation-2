// This program corresponds to Question 1.4

#include <stdio.h>

int main ()
{
	unsigned int n;
	printf("Give me an integer n :\n");
	printf("n = "); scanf("%d",&n);

	n = ((n & 0xaaaaaaaa) >> 1) + (n & 0x55555555);
	printf("Result: c = %d\n",n);
	n = ((n & 0xcccccccc) >> 2) + (n & 0x33333333);
	printf("Result: c = %d\n",n);
	n = ((n & 0xf0f0f0f0) >> 4) + (n & 0x0f0f0f0f);
	printf("Result: c = %d\n",n);
	n = ((n & 0xff00ff00) >> 8) + (n & 0x00ff00ff);
	printf("Result: c = %d\n",n);
	n = ((n & 0xffff0000) >> 16) + (n & 0x0000ffff);

	printf("Result: c = %d\n",n);

	return 0;
}
