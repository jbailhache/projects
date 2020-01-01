
#include "stdio.h"
#include "graphics.h"
#include "stdlib.h"
#include "math.h"

#define MAX_X 300
#define MAX_Y 200


#define x_src1 100
#define y_src1 80
#define x_src2 180
#define y_src2 110
#define x_src3 130
#define y_src3 150
#define x_src4 160
#define y_src4 50

#define NSRC 4

int src[][2] = {
	{ 100, 80 },
	{ 180, 110 },
	{ 130, 150 },
	{ 160, 50 } };


/*
#define x_src3 170
#define y_src3 120
*/

#define d 400

#define lambda 1

#define rs 5
#define eps 1

#define int long

int intensite0 (int x, int y)
{
	return sin((float)x/20.0) * sin((float)y/20.0) * 16;

}

int intensite3 (int x, int y)
{
float d1, d2, d3, d4, a, b;

	d1 = sqrt ((x - x_src1) * (x - x_src1) +
		   (y - y_src1) * (y - y_src1) +
		   d * d);
	d2 = sqrt ((x - x_src2) * (x - x_src2) +
		   (y - y_src2) * (y - y_src2) +
		   d * d);
	d3 = sqrt ((x - x_src3) * (x - x_src3) +
		   (y - y_src3) * (y - y_src3) +
		   d * d);
	d4 = sqrt ((x - x_src4) * (x - x_src4) +
		   (y - y_src4) * (y - y_src4) +
		   d * d);

	a = sin (d1 / lambda) + sin (d2 / lambda) + sin (d3 / lambda) + sin (d3 / lambda);
	b = cos (d1 / lambda) + cos (d2 / lambda) + cos (d3 / lambda) + sin (d4 / lambda);
	/* return a * a * 4 */ /* joli ! */
	return (a * a + b * b) / 2 /* * 2 */ ;
}

int intensite (int x, int y)
{
float di, a, b, c;
int i;
	a = 0;
	b = 0;
	for (i=0; i<NSRC; i++)
	{
		di = sqrt ((x - src[i][0]) * (x - src[i][0]) +
			   (y - src[i][1]) * (y - src[i][1]) +
			   d * d);
		a += sin (di / lambda);
		b += cos (di / lambda);
	}
	c = (a * a + b * b) / (NSRC * NSRC * 2);
	i = log (c) + 15;
	if (i < 0) i = 0;
	return i;
}

int intensite2 (int x, int y)
{
float d1, d2, a, b, xs, ys;
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
	a /= n;
	b /= n;
	return (a*a + b*b) * 8;
}

putpixel1 (int x, int y, int c)
{
	/*
	c = (c + 16) / 2;
	if (random (15) < c)
		putpixel (x, y, 1);
	else
		putpixel (x, y, 0);
	*/
	/*
	if (c > 0)
		putpixel (x, y, 1);
	else
		putpixel (x, y, 0);
	*/

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
			putpixel1 (i, i, i*16/150);
		}
	}

	interf ();

	gets (buf);
	sleep (1);
	restorecrtmode ();
	printf ("status = %d\n", status);
}


