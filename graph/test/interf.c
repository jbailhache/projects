/* Interference fringes
   Build : 
   cc -o interf_linux interf_linux.c graphics.c -lX11 -lm
*/

#include "stdio.h"
#include "graphics.h"
#include "stdlib.h"
#include "math.h"

#define gamma gama

#define GRAPH

#define DIFFRACT

#define MAX_X 300
#define MAX_Y 200

int dz = 40;
float lambda = /*1*/ /*3*/ /*10*/ 0.3;

#ifndef DIFFRACT
#define NSOURCES 2

int sources[NSOURCES][2] = { { 100, 80 }, { 200, 110 } };

#else
#define MAXSOURCES 2000

int sources[MAXSOURCES][2];

int NSOURCES;
#endif

float rayon_source = 1.5;

defsources ()
{
#ifdef DIFFRACT
long x, y, dx, dy, i, d2;
float d1;

	i = 0;
	for (x=1; x<MAX_X; x++)
	for (y=1; y<MAX_Y; y++)
	{
		dx = x - 100;
		dy = y - 80;
		d2 = dx*dx + dy*dy;
		d1 = sqrt((float)d2);
		if (d1 <= rayon_source)
		{
			sources[i][0] = x;
			sources[i][1] = y;
			i++;
		}

		dx = x - 200;
		dy = y - 110;
		d2 = dx*dx + dy*dy;
		d1 = sqrt((float)d2);
		if (d1 <= rayon_source)
		{
			sources[i][0] = x;
			sources[i][1] = y;
			i++;
		}

	}
	NSOURCES = i;
#endif
}

float alpha = 1;
float beta = 1;
float gamma = 0;

plot (int x, int y, float a)
{
#ifdef GRAPH
	/* if (random(100) > a*a*25) */
	/* if (a*a > 2) */
#ifdef DIFFRACT
	/* if (2*a > NSOURCES) */
	/* if (1.01*a > NSOURCES) */
	/* if (a*2 > NSOURCES) */
	/* if (a*20 > random (NSOURCES*20)) */
	/* if (a < 6.5) */
	/* if (a < 1.5) */
	/* if (a < 3) */
	/* if (a < 1) */
	if (a*alpha < beta + NSOURCES*gamma)
#else
	if (a*2 > NSOURCES)
#endif
	{
		putpixel (x, y/2, 1);
	}
#endif
}

interf ()
{
long x, y, dx, dy, i, d2;
float a, b, d1, fd2;
	for (y=2; y<MAX_Y; y+=2)
	for (x=1; x<MAX_X; x++)
	{
#ifdef TRACE
		printf ("%ld %ld\n", x, y);
#endif
		a = 0;
		b = 0;
		for (i=0; i<NSOURCES; i++)
		{
			dx = x - sources[i][0];
			dy = y - sources[i][1];
			d2 = dx*dx + dy*dy + dz*dz;
#ifdef TRACE
			printf ("%ld\n", d2);
#endif
			fd2 = (float) d2;
			d1 = sqrt (fd2);
#ifdef TRACE
			printf ("%f\n", d1);
#endif
			a += sin (d1 / lambda);
			b += cos (d1 / lambda);
		}
		plot (x, y, sqrt (a*a + b*b));
	}
}

main()
{
int driver, mode;
int status;
char buf[1000];

	printf ("Rayon source (1.5) ? ");
	scanf ("%f", &rayon_source);

	printf ("Lambda ? (0.3) ");
	scanf ("%f", &lambda);

	printf ("Distance (40) ? ");
	scanf ("%f", &dz);

	printf ("Alpha (1) ? ");
	scanf ("%f", &alpha);

	printf ("Beta (1) ? ");
	scanf ("%f", &beta);

	printf ("Gamma (0) ? ");
	scanf ("%f", &gamma);

	defsources ();
/*
	driver=HERCMONO;
	mode=HERCMONOHI;
*/
/*
	printf ("Driver ? ");
	scanf ("%d", &driver);
	printf ("Mode ? ");
	scanf ("%d", &mode);
*/
	detectgraph (&driver, &mode);

#ifdef GRAPH
	initgraph (&driver, &mode, "");
	status = graphresult ();
	if (status != grOk)
	{
		printf ("Erreur initgraph %d 0x%X\n", status, status);
		return;
	}
#endif
/*
	putpixel (120, 130, 1);
	{
	int i;
		for (i=0; i<150; i++)
		{
			putpixel (i, i, 1);
		}
	}
*/
	interf ();

	gets (buf); gets(buf); gets(buf);
	sleep (1);
/*	restorecrtmode ();*/
	printf ("status = %d\n", status);
}


