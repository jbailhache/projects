
/* build : cc -o chauffeur chauffeur.c graphics.c -lX11 -lm */

#include <stdio.h>
#include <math.h>
#include "graphics.h"

void cleardevice (void);

void xclear ()
{
	cleardevice();
}

#define xmin -12.0
#define xmax 12.0
#define ymin -12.0
#define ymax 12.0

#define width 600
#define height 600

#define lmargin 50
#define tmargin 50

#define graphx(x) ((int)(lmargin+width*((x)-xmin)/(xmax-xmin)))
#define graphy(y) ((int)(tmargin+height*(ymax-(y))/(ymax-ymin)))

void delai ()
{
long i;
	for (i=0; i<10000; i++);
}

void plot (float x, float y, int c)
{
int gx, gy;
	if (x > xmin && x < xmax && y > ymin && y < ymax)
	{
		gx = graphx(x);
		gy = graphy(y);
		putpixel (graphx(x), graphy(y), c);
	}
}

#define plotpoint(x,y) plot(x,y,7)

void test ()
{
float u;
	for (u=-10.0; u<10.0; u+=0.1)
	{
		plot (u, u*u, 7);
	}
}

#define pi 3.1415926

#define dt 0.01

/*
#define s 1
#define c (s*1.5)
#define c1 (s*0.2)
#define c2 (s*0.1)
#define a0 pi
*/

#define v1 5
#define v2 3
#define L 2
//#define T 10

float rho = 0;

void rotation (float rho, float *px, float *py)
{
float x, y;
	x = *px;
	y = *py;
	*px = x * cos(rho) - y * sin(rho);
	*py = x * sin(rho) + y * cos(rho);
}

float h1 (float x, float y, float a, float u1, float u2, float px1, float py1, float pa1)
{
	return u1*u1+x*x+y*y+px1*(-v1*cos(a/pi*180)+v2*cos(u2/pi*180))+py1*(-v1*sin(a/pi*180)+v2*sin(u2/pi*180))+pa1 *v1/L;
}

float h2 (float x, float y, float a, float u1, float u2, float px2, float py2, float pa2)
{
	return -x*x-y*y+px2*(-v1*cos(a/pi*180)+v2*cos(u2/pi*180))+py2*(-v1*sin(a/pi*180)+v2*sin(u2/pi*180))+pa2 *v1/L *u1;
}

void traj (float *psl1, float *psl2, 
			int fp, float T, float px1, float py1, float pa1, float px2, float py2, float pa2)
{
	float sl1 = 0;
	float sl2 = 0;

	float x1 = 0;
	float y1 = 0;
	float x2 = -3;
	float y2 = 1;
	float x = x2 - x1;
	float y = y2 - y1;
	float a = 0;

	// float px1 = -1.5;
	// float py1 = -1.5;
	// float pa1 = -1.5;
	// float px2 = -5;
	// float py2 = -0.5;
	// float pa2 = 1;

	float t, u1, u2;
	int r;

	float u;

	rotation (rho, &x1, &y1);
	rotation (rho, &x2, &y2);
	a += rho;

	// rotation (rho, &px1, &py1);
	// rotation (rho, &px2, &py2);

	if (fp > 0)
	{
		xclear();
	}

	//for (u=0; u<5; u+=0.01)
	//	plot (u*cos(rho), u*sin(rho), 8);

	for (t=0; t<T; t+=dt)
	{
		//delai();

		u1=-0.5*pa1*v1/L;
		if (px2 > 0)
			u2=atan(py2/px2);
		else if (px2 < 0)
			u2=atan(py2/px2)+pi;
		else // (px2 == 0)
		{
			if (py2 >= 0)	
				u2 = pi/2;
			else
				u2 = -pi/2;
		}
		
		//if (x < 0)
		//	u2 += pi;

		//e = 0.1;

		//plot(x,y,12);

		x1=x1+dt*v1*cos(a);
		y1=y1+dt*v1*sin(a);

		x2=x2+dt*v2*cos(u2);
		y2=y2+dt*v2*sin(u2);

		x=x2-x1;
		y=y2-y1;

		if (fp)
		{
			plot(x1,y1,12);
			plot(x2,y2,8);
 			//plotpoint(xmin+(xmax-xmin)*t/T,sl1/8);
			//plotpoint(xmin+(xmax-xmin)*(1-t/T),sl2/8);
		}

		/*
		for (r=1; r<=4; r++)
			plot(r*cos(a),r*sin(a),3);
		a=a+dt*v1/L*u1;
		for (r=1; r<=4; r++)
			plot(r*cos(a),r*sin(a),14);
		*/

		a=a+dt*v1/L*u1;

		px1=px1+dt*(-2*x);
		py1=py1+dt*(-2*y);
		pa1=pa1+dt*(v1*(-px1*sin(a)+py1*cos(a)));

		px2=px2+dt*(2*x);
		py2=py2+dt*(2*y);
		pa2=pa2+dt*(v1*(-px2*sin(a)+py2*cos(a)));

		sl1=sl1+dt*(u1*u1+x*x+y*y);
		sl2=sl2+dt*(-x*x-y*y);
		
		//plot(px1,px2,1);
		//plot(py1,py2,2);
		//plot(pa1,pa2,4);
	}	
	*psl1 = sl1;
	*psl2 = sl2;
}

void solve (float *psl1, float *psl2, float *ppx1, float *ppy1, float *ppa1, float *ppx2, float *ppy2, float *ppa2, 
			float T, float eps, int m)
{
float px1, py1, pa1, px2, py2, pa2;
float sl1, sl2, sl1p, sl2p, sl1t, sl2t, sl1d, sl2d, dp;
int s, af, i;
float x, y, u;
float d1px, d1py, d2px, d2py;
float px1t, py1t, pa1t, px2t, py2t, pa2t;
int ix1, iy1, ia1, ix2, iy2, ia2;

	//for (rho=0; rho<=2*pi; rho+=pi/32) // test
	//{
	 	px1=0;
		py1=0;
		pa1=0;
		px2=1;//1.01;
		py2=0;//1.01;
		pa2=0;//1;

		rotation (rho, &px1, &py1);
		rotation (rho, &px2, &py2);

 		traj(&sl1,&sl2,1,T,px1,py1,pa1,px2,py2,pa2);
		printf ("rho=%f sl1=%f sl2=%f  px1=%f py1=%f pa1=%f  px2=%f py2=%f pa2=%f\n", 
			rho, sl1, sl2, px1, py1, pa1, px2, py2, pa2);
		for (i=0; i<100; i++) delai();
	//}
	//return;

	dp=0.5;

	s=0;

	while (1) 
	{

	 	s=s+1;
 		if (s>m) break; 

 		// plotpoint(px1/10,px2/10);
 		// plotpoint(py1/10,py2/10);
 		// plotpoint(pa1/10,pa2/10);
 
 		// xclear();
		
 		traj(&sl1,&sl2,1,T,px1,py1,pa1,px2,py2,pa2);
		printf ("sl1=%f sl2=%f  px1=%f py1=%f pa1=%f  px2=%f py2=%f pa2=%f\n", 
			sl1, sl2, px1, py1, pa1, px2, py2, pa2);

		sl1p = sl1;
 		sl2p = sl2;

		af = 0;

		for (ix1=-1; ix1<=1; ix1++)
		for (iy1=-1; iy1<=1; iy1++)
		for (ia1=-1; ia1<=1; ia1++)
		{
			px1t=px1+ix1*dp;
			py1t=py1+iy1*dp;
			pa1t=pa1+ia1*dp;
	 		traj(&sl1t,&sl2t,0,T,px1t,py1t,pa1t,px2,py2,pa2);
			if (sl1t < sl1)
			{
				px1=px1t;
				py1=py1t;
				pa1=pa1t;
				sl1=sl1t;
				sl2=sl2t;
			}			
		}				

		for (ix2=-1; ix2<=1; ix2++)
		for (iy2=-1; iy2<=1; iy2++)
		for (ia1=-1; ia1<=1; ia1++)
		{
			px2t=px2+ix2*dp;
			py2t=py2+iy2*dp;
			pa2t=pa2+ia2*dp;
			traj(&sl1t,&sl2t,0,T,px1,py1,pa1,px2t,py2t,pa2t);
			if (sl2t < sl2)
			{
				px2=px2t;
				py2=py2t;
				pa2=pa2t;
				sl1=sl1t;
				sl2=sl2t;
			}
		}		

		/*
		d1px = dp;
		d1py = 0;
		d2px = 0;
		d2py = dp;

		
		//d1px = sqrt(2)*dp;
		//d1py = d1px;
		//d2px = -d1px;
		//d2py = d1px;
		
	
		rotation (rho, &d1px, &d1py);
		rotation (rho, &d2px, &d2py);

		px1t=px1+d1px; py1t=py1+d1py;
 		traj(&sl1t,&sl2t,0,T,px1t,py1t,pa1,px2,py2,pa2);
 		if (sl1t < sl1) 
		{ 
			px1=px1t;
			py1=py1t;
			sl1=sl1t;
			sl2=sl2t;
		}
		else
		{
			px1t=px1-d1px; py1t=py1-d1py;
  			traj(&sl1t,&sl2t,0,T,px1t,py1t,pa1,px2,py2,pa2);
  			if (sl1t < sl1) 
			{
				px1=px1t;
				py1=py1t;
				sl1=sl1t;
				sl2=sl2t;
  			}
		}

		px1t=px1+d2px; py1t=py1+d2py;
		traj(&sl1t,&sl2t,0,T,px1t,py1t,pa1,px2,py2,pa2);
		if (sl1t < sl1) 
		{ 
			px1=px1t;
			py1=py1t;
			sl1=sl1t;
			sl2=sl2t;
		}
		else
		{
			px1t=px1-d2px; py1t=py1-d2py;
			traj(&sl1t,&sl2t,0,T,px1t,py1t,pa1,px2,py2,pa2);
			if (sl1t < sl1) 
			{
				px1=px1t;
				py1=py1t;
				sl1=sl1t;
				sl2=sl2t;
			}
		}

		pa1t=pa1+dp;
		traj(&sl1t,&sl2t,0,T,px1,py1,pa1t,px2,py2,pa2);
		if (sl1t < sl1) 
		{
			pa1=pa1t;
			sl1=sl1t;
			sl2=sl2t;
		}
		else
		{
			pa1t=pa1-dp;
			traj(&sl1t,&sl2t,0,T,px1,py1,pa1-dp,px2,py2,pa2);
			if (sl1t < sl1) 
			{
				pa1=pa1t;
				sl1=sl1t;
				sl2=sl2t;
			}
		}
 		
		px2t=px2+d1px; py2t=py2+d1py;
		traj(&sl1t,&sl2t,0,T,px1,py1,pa1,px2t,py2t,pa2);
		if (sl2t < sl2) 
		{
			px2=px2t;
			py2=py2t;
			sl1=sl1t;
			sl2=sl2t;
		}
		else
		{
			px2t=px2-d1px; py2t=py2-d1py;
			traj(&sl1t,&sl2t,0,T,px1,py1,pa1,px2t,py2t,pa2);
			if (sl2t < sl2) 
			{
				px2=px2t;
				py2=py2t;
				sl1=sl1t;
				sl2=sl2t;
			}
		}

		px2t=px2+d2px; py2t=py2+d2py;
		traj(&sl1t,&sl2t,0,T,px1,py1,pa1,px2t,py2t,pa2);
		if (sl2t < sl2)
		{ 
			px2=px2t;
			py2=py2t;
			sl1=sl1t;
			sl2=sl2t;
		}
		else
		{
			px2t=px2-d2px; py2t=py2-d2py;
			traj(&sl1t,&sl2t,0,T,px1,py1,pa1,px2t,py2t,pa2);
			if (sl2t < sl2) 
			{
				px2=px2t;
				py2=py2t;
				sl1=sl1t;
				sl2=sl2t;
			}
		}

		pa2t=pa2+dp;
		traj(&sl1t,&sl2t,0,T,px1,py1,pa1,px2,py2,pa2t);
		if (sl2t < sl2) 
		{
			pa2=pa2t;
			sl1=sl1t;
			sl2=sl2t;
		}
		else
		{
			pa2t=pa2-dp;
			traj(&sl1t,&sl2t,0,T,px1,py1,pa1,px2,py2,pa2t);
			if (sl2t < sl2) 
			{ 
				pa2=pa2t;
				sl1=sl1t;
				sl2=sl2t;
			}
		}	
		*/		

 		if ((sl1==sl1p) && (sl2==sl2p)) 
  			dp=dp/2;
 		else
  			dp=dp*2;

		if (dp<eps) break;

	}

	traj(&sl1, &sl2, 1,T,px1,py1,pa1,px2,py2,pa2);	
	printf ("rho=%f sl1=%f sl2=%f  px1=%f py1=%f pa1=%f  px2=%f py2=%f pa2=%f\n", 
		rho, sl1, sl2, px1, py1, pa1, px2, py2, pa2);


	*psl1 = sl1;
	*psl2 = sl2;
	*ppx1 = px1;
	*ppy1 = py1;
	*ppa1 = pa1;
	*ppx2 = px2;
	*ppy2 = py2; 
	*ppa2 = pa2;
}


void chauffeur ()
{
float sl1, sl2, px1, py1, pa1, px2, py2, pa2;
int i;
	// for (rho=0; rho<=2*pi; rho+=pi/16)
	{
		solve (&sl1, &sl2, &px1, &py1, &pa1, &px2, &py2, &pa2, 3, 0.01, 100);
		printf ("\nRésultat pour rho=%f:\nsl1=%f sl2=%f px1=%f py1=%f pa1=%f px2=%f py2=%f pa2=%f\n", 
			rho, sl1, sl2, px1, py1, pa1, px2, py2, pa2);
		for (i=0; i<1000; i++) delai();
		
	}
}

int main()
{
int driver, mode;
int status;
char buf[1000];
	driver=HERCMONO;
	mode=HERCMONOHI;
	initgraph (&driver, &mode, "");
	status = graphresult ();
	if (status != grOk)
		printf ("Erreur initgraph %d 0x%X\n", status, status);
	/* putpixel (120, 130, 1); */
	chauffeur();
	fgets (buf, sizeof(buf), stdin);
	restorecrtmode ();
}

