
#include "stdio.h"
#include "graphics.h"
#include "stdlib.h"
#include "math.h"

#define MAX_X 300
#define MAX_Y 200

#define x_src1 100
#define y_src1 80
#define x_src2 120
#define y_src2 90

/*
#define x_src2 180
#define y_src2 110
*/
#define d 400

#define lambda 0.1

#define rs 3
#define eps 0.3

#define int long

#define A 100

int intensite1 (int x, int y)
{
float d1, d2, a, b;
	/* return sin((float)x/20.0) * sin((float)y/20.0) * 16; */

	d1 = sqrt ((x - x_src1) * (x - x_src1) +
		   (y - y_src1) * (y - y_src1) +
		   d * d);
	d2 = sqrt ((x - x_src2) * (x - x_src2) +
		   (y - y_src2) * (y - y_src2) +
		   d * d);

	a = sin (d1 / lambda) + sin (d2 / lambda);
	b = cos (d1 / lambda) + cos (d2 / lambda);
	/* return a * a * 4 */ /* joli ! */
	return (a * a + b * b) * 2;
}

int intensite (int x, int y)
{
float d1, d2, a, b, c, xs, ys;
int n;
	a = 0;
	b = 0;
	n = 0;
	for (xs=x_src1-rs; xs<x_src1+rs; xs+=eps)
	for (ys=y_src1-rs; ys<y_src1+rs; ys+=eps)
	{
		if ((xs-x_src1)*(xs-x_src1)+(ys-y_src1)*(ys-y_src1) < rs*rs)
		{
			d1 = sqrt ((x-xs)*(x-xs)+(y-ys)*(y-ys)+d*d);
			a += sin (d1/lambda);
			b += cos (d1/lambda);
			n++;
		}
	}
	for (xs=x_src2-rs; xs<x_src2+rs; xs+=eps)
	for (ys=y_src2-rs; ys<y_src2+rs; ys+=eps)
	{
		if ((xs-x_src2)*(xs-x_src2)+(ys-y_src2)*(ys-y_src2) < rs*rs)
		{
			d1 = sqrt ((x-xs)*(x-xs)+(y-ys)*(y-ys)+d*d);
			a += sin (d1/lambda);
			b += cos (d1/lambda);
			n++;
		}
	}
	a /= n;
	b /= n;
	/* return (a*a + b*b) * 8 * A; */
	c = (a*a + b*b) / 2;
	if (c < 0) c = 0;
	return log (c) + 15;
}

interf ()
{
int i, j;
	for (i=1; i<MAX_X; i++)
	for (j=1; j<MAX_Y; j++)
		putpixel (i, j, intensite (i, j));
}
main()
{
int driver, mode;
int status;
char buf[1000];
	driver = DETECT;
	mode = VGAHI;

	initgraph (&driver, &mode, "");
	status = graphresult ();
	if (status != grOk)
	{
		printf ("Erreur initgraph %d 0x%X\n", status, status);
		return;
	}

	putpixel (120, 130, 1);
	{
	int i;
		for (i=0; i<150; i++)
		{
			putpixel (i, i, i*16/150);
		}
	}

	interf ();

	gets (buf);
	sleep (1);
	restorecrtmode ();
	printf ("status = %d\n", status);
}


