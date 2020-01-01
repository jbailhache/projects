
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

