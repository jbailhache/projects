
#include <stdlib.h>

#include "graphics.h"
#include "ppm.h"


Image *image;

void detectgraph (int *pdriver, int *pmode)
{
}

void initgraph (int *pdriver, int *pmode, char *s)
{
    image = ImageCreate (700, 700);
}

int graphresult(void)
{
	return grOk;
}

void restorecrtmode(void)
{
}

int colors[] = {
 0x000000,
 0x000080,
 0x008000,
 0x008080,
 0x800000,
 0x800080,
 0x808000,
 0xC0C0C0,
 0x808080,
 0x0000FF,
 0x00FF00,
 0x00FFFF,
 0xFF0000,
 0xFF00FF,
 0xFFFF00,
 0xFFFFFF
};


void putpixel (int x, int y, int c)
{
    ImageSetPixel (image, x, y, 0, (colors[c] & 0xFF0000) >> 16);
    ImageSetPixel (image, x, y, 1, (colors[c] & 0x00FF00) >> 8);
    ImageSetPixel (image, x, y, 2, colors[c] & 0x0000FF);
}

void drawline (int x1, int y1, int x2, int y2, int c)
{
int n, i, x, y;
    n = abs(x2-x1) + abs(y2-y1);
    for (i=0; i<n; i++) {
        x = x1 + (x2 - x1) * i / n;
        y = y1 + (y2 - y1) * i / n;
        putpixel (x, y, c);
    }
}

void clear (void)
{
    ImageClear (image, 0, 0, 0);
}

void endgraph ()
{
    ImageWrite (image, "image.ppm");
}

