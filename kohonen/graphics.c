
#include "bibx.c"

#include "graphics.h"

void detectgraph (int *pdriver, int *pmode)
{
}

void initgraph (int *pdriver, int *pmode, char *s)
{
	graphic_init();
}

int graphresult(void)
{
	return grOk;
}

void restorecrtmode(void)
{
}

void putpixel (int x, int y, int c)
{
	setcolor (c % 16);
	point (x, y);	
}

void drawline (int x1, int y1, int x2, int y2, int c)
{
    setcolor (c % 16);
    line (x1, y1, x2, y2);
}

