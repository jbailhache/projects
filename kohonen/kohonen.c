
#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <unistd.h>
#include <time.h>

#include "graphics.h"

#define NDIM 2

#define NN 100

int size[] = { 10, 10 };
int coord[2];

#define NDIM_SPACE 2

double max[] = { 100.0, 100.0 };

double map[NN][NDIM_SPACE];

void get_coord (int number, int coord[])
{
int i;
    for (i=0; i<NDIM; i++) {
        coord[i] = number % size[i];
        number /= size[i];
    }
}

int get_number (int coord[]) 
{
int i, n;
    n = 0;
    for (i=NDIM-1; i>=0; i--) {
        n *= size[i];
        n += coord[i];
    }
    return n;
}

int distance (int r, int s) 
{
int i, d, di;
int cr[NDIM], cs[NDIM];
    get_coord (r, cr);
    get_coord (s, cs);
    d = 0;
    for (i=0; i<NDIM; i++) {
        di = cs[i] - cr[i];
        d += di * di;
    }
    return d;
}

double hasard ()
{
    return (float)rand()/((float)RAND_MAX);
}

void init_map ()
{
int i, j;
    for (i=0; i<NN; i++) {
        for (j=0; j<NDIM_SPACE; j++) {
            map[i][j] = max[j] * hasard();             
        }
    }
}

void init_map_test ()
{
int i, j;
int coord[NDIM];
    for (i=0; i<NN; i++) {
        get_coord (i, coord);
        for (j=0; j<NDIM_SPACE; j++) {
            map[i][j] = 10 + 10*coord[j];
        }
    }
}


#define SCALE 5

void draw_line (float x1, float y1, float x2, float y2, int c)
{
    //printf ("Line from %f %f to %f %f \n", x1, y1, x2, y2);
    drawline (SCALE*x1, SCALE*y1, SCALE*x2, SCALE*y2, c);
}

void draw_map ()
{
int i, j, n1, n2;
int coord[NDIM];
double x1, y1, x2, y2;
    for (i=0; i<10; i++) {
        for (j=0; j<9; j++) {
            coord[0] = i;
            coord[1] = j;
            n1 = get_number (coord);
            coord[0] = i;
            coord[1] = j+1;
            n2 = get_number (coord);
            x1 = map[n1][0];
            y1 = map[n1][1];
            x2 = map[n2][0];
            y2 = map[n2][1];
            draw_line (x1, y1, x2, y2, 7);
        }
    }
    for (i=0; i<9; i++) {
        for (j=0; j<10; j++) {
            coord[0] = i;
            coord[1] = j;
            n1 = get_number (coord);
            coord[0] = i+1;
            coord[1] = j;
            n2 = get_number (coord);
            x1 = map[n1][0];
            y1 = map[n1][1];
            x2 = map[n2][0];
            y2 = map[n2][1];
            draw_line (x1, y1, x2, y2, 7);
        }
    }
}

float a = 1.0;

void step (int t)
{
int i, winner, d;
double x, y, dmin, xi, yi, di, dx, dy, h, r;
	a *= 0.9999;
	r = hasard();
    x = 10.0 + r * r * 80.0;
	r = hasard();
    y = 10.0 + r * r * 80.0;
    //printf ("x=%f y=%f\n", x, y);
    winner = -1;
    dmin = 20000.0;
    for (i=0; i<NN; i++) {
        xi = map[i][0];
        yi = map[i][1];
        dx = xi - x;
        dy = yi - y;
        di = dx * dx + dy * dy;
        //printf ("i=%d di=%f\n", i, di);
        if (di < dmin) {
            dmin = di;
            winner = i;
        }
    }
    //printf ("winner = %d\n", winner);
    for (i=0; i<NN; i++) {
        d = distance (winner, i);
        //printf ("d = %d\n", d);
        h = a * exp(-(double)d);
        dx = h * (x - map[i][0]);
        dy = h * (y - map[i][1]);
        map[i][0] += dx;
        map[i][1] += dy;
    }
}

void step_test2 ()
{
int i, j, winner, d;
double x, y, dmin, xi, yi, di, dx, dy, h, w;
    x = 10.0 + hasard() * 80.0;
    y = 10.0 + hasard() * 80.0;
    //printf ("x=%f y=%f\n", x, y);

	for (i=0; i<NN; i++) {
        xi = map[i][0];
        yi = map[i][1];
        dx = xi - x;
        dy = yi - y;
        di = dx * dx + dy * dy;
		w = 1.0 / di;
		for (j=0; j<NN; j++) {
			d = distance (i, j);
			//printf ("d = %d\n", d);
			h = w * exp(-(double)d);
			dx = h * (x - map[j][0]);
			dy = h * (y - map[j][1]);
			map[j][0] += dx;
			map[j][1] += dy;
		}
	}
}

void step_test1 ()
{
int i, winner, d;
double x, y, dmin, xi, yi, di, dx, dy, h;
    x = 10.0 + hasard() * 80.0;
    y = 10.0 + hasard() * 80.0;
    for (i=0; i<NN; i++) {
        xi = map[i][0];
        yi = map[i][1];
        dx = xi - x;
        dy = yi - y;
        di = dx * dx + dy * dy;
        h = exp(-di/100.0);
        dx = h * (x - map[i][0]);
        dy = h * (y - map[i][1]);
        //printf ("i=%d di=%f dx=%f dy=%f\n", i, di, dx, dy);
        map[i][0] += dx;
        map[i][1] += dy;
    }
}

int main () 
{
int driver, mode, status;
int i, n, s, t, u;
char buf[10000];

	srand(time(NULL));
	
	initgraph (&driver, &mode, "");
	status = graphresult ();
	if (status != grOk)
	{
		printf ("Erreur initgraph %d 0x%X\n", status, status);
		return 0;
	}

    /*for (i=0; i<150; i++) {
        putpixel (i, i, 7);
    }*/

    get_coord (38, coord);
    n = get_number (coord);
    printf (" %d %d %d \n", coord[0], coord[1], n);
    printf (" %d \n", distance (12, 35));    
    init_map();
    /*for (i=0; i<NN; i++) {
        printf (" %f %f \n", map[i][0], map[i][1]);
    }*/

    draw_map ();
    sleep(1);
    step(1);
    cleardevice();
    draw_map();
    sleep(1);

    for (t=1; ; t++) {
		for (u=0; u<1000; u++) {
            step (t);
		}
        cleardevice();
        draw_map();
        for (s=0; s<10000; s++);
        if (t > 100) {
            sleep(1);
        }
    }

    gets (buf);

}

