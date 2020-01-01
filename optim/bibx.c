/*                                                        */
/* Graphics Library for X11-Unix Plathome                 */
/* Written by N.Okamoto<okamoto@ish.ic.kanagawa-it.ac.jp> */
/*                                                        */
/* Based on the [graphics.h]...Borland C++ BGI Compatible */
/*  Library.                                              */
/*                                                        */
/*  Last Modified: May, 16, 1999                          */
/*                                                        */

/* ====================================================== */
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <stdio.h>

/* Color Define */
#define BLACK            0
#define BLUE             1
#define GREEN            2
#define CYAN             3
#define RED              4
#define MAGENTA          5
#define BROWN            6
#define LIGHTGRAY        7
#define DARKGRAY         8
#define LIGHTBLUE        9
#define LIGHTGREEN      10
#define LIGHTCYAN       11
#define PINK            12
#define LIGHTMAGENTA    13
#define YELLOW          14
#define WHITE           15

/* Structure Define */
struct viewporttype {
    int left, top, right, bottom;
    int clip;
};

/* Global Variables */
Display                 *_display;
Window                  _window;
GC                      _gc;
XGCValues               gv;
XSetWindowAttributes    attr;
Colormap                _colmap;
XColor                  _col, _ext;
char ColorTable[16][15] = { "black", "blue", "green", "cyan", "red",
                            "magenta", "brown", "lightgray", "darkgray",
                            "lightblue", "lightgreen", "lightcyan", 
                            "pink", "lightmagenta", "yellow", "white" };
int FgColor, BgColor;
int current_x, current_y;
int NowCol = WHITE;


/* Wrapping Functions */

/* ============================================================= */
/*  Graphic Driver                                               */

int graphic_init(void)
{
    Window rw;

    _display = XOpenDisplay( NULL );
    rw = XDefaultRootWindow( _display );
    _window = XCreateSimpleWindow( _display, rw, 0, 0, 700, 700, 2, 
        WhitePixel( _display, 0 ),BlackPixel( _display, 0 )  );
    _colmap = XDefaultColormap( _display, 0 );    

    attr.backing_store = Always;
    XChangeWindowAttributes( _display, _window, CWBackingStore, &attr );
    attr.override_redirect = True;
    XChangeWindowAttributes( _display, _window, CWOverrideRedirect, &attr );

    XMapWindow( _display, _window );
    gv.line_width = 1;
    _gc = XCreateGC( _display, rw, GCLineWidth, &gv );
    XAllocNamedColor( _display, _colmap, "white", &_col, &_ext );
    XSetForeground( _display, _gc, _col.pixel );
    XSetLineAttributes( _display, _gc, 1, LineSolid, CapButt, JoinMiter );

    XFlush( _display );
    current_x = current_y = 0;
    FgColor = WHITE;
    BgColor = BLACK;
    NowCol = BLACK;
    return 0;
}

void graphic_close( void )
{
    XFreeGC( _display, _gc );
    XDestroyWindow( _display, _window );
    XFlush( _display );
    XCloseDisplay( _display );
}

int getmaxx( void )
{
    return 699;
}

int getmaxy( void )
{
    return 699;
}

void graphdefaults( void )
{
    current_x = 0;
    current_y = 0;
    FgColor = WHITE;
    BgColor = BLACK;
}

void cleardevice( void )
{
    XColor t;

    XAllocNamedColor( _display, _colmap, ColorTable[BgColor], &t, &_ext );
    XSetForeground( _display, _gc, t.pixel );
    XFillRectangle( _display, _window, _gc, 0, 0, 699, 699 ); 
    XSetForeground( _display, _gc, _col.pixel );

    XFlush( _display );
    current_x = 0;
    current_y = 0;
}

/* ============================================================= */
/*  Screen                                                       */

void clearviewport( void )
{
    current_x = 0;
    current_y = 0;
}

void getaspectratio( int *x, int *y )
{
     *x = 10000;
     *y = 10000;
}

void getviewsettings( struct viewporttype *view )
{
    view -> left   = 0;
    view -> top    = 0;
    view -> right  = 699;
    view -> bottom = 799;
    view -> clip   = 0;
} 

/* ============================================================= */
/*  Color                                                        */

int setcolor( int c )
{
    NowCol = c;

    XAllocNamedColor( _display, _colmap, ColorTable[c], &_col, &_ext );
    XSetForeground( _display, _gc, _col.pixel );
}

int setRGBcolor(unsigned char r, unsigned char g, unsigned char b)
{
    XColor color;

    color.red   = r * 256;
    color.green = g * 256;
    color.blue  = b * 256;
    color.flags = DoRed | DoGreen | DoBlue;
    
    XAllocColor( _display, _colmap, &color );
    XSetForeground( _display, _gc, color.pixel );
}

int getbkcolor( void )
{
    return BgColor;
}

void setbkcolor( int color )
{
    BgColor = color;
}

int getcolor( void )
{
    return NowCol;
}

int getmaxcolor( void )
{
    return 16;
}

/* ============================================================= */
/*  Drawing                                                      */

void point( int x, int y )
{
    XDrawPoint( _display, _window, _gc, x, y);
    XFlush( _display );
    current_x = x;
    current_y = y;
}

void line( int x1, int y1, int x2, int y2 )
{
    XDrawLine( _display, _window, _gc, x1, y1, x2, y2 );
    XFlush( _display );
    current_x = x2;
    current_y = y2;
}

void rectangle( int x1, int y1, int x2, int y2 )
{
    XDrawRectangle( _display, _window, _gc, x1, y1, x2 - x1, y2 - y1 );
    XFlush( _display );
    current_x = x2;
    current_y = y2;
}

void fillrectangle( int x1, int y1, int x2, int y2 )
{
    XFillRectangle( _display, _window, _gc, x1, y1, x2 - x1 , y2 - y1 );
    XFlush( _display );
    current_x = x2;
    current_y = y2;
}

void lineto( int x2, int y2 )
{
    XDrawLine( _display, _window, _gc, current_x, current_y, x2, y2 );
    XFlush( _display );
    current_x = x2;
    current_y = y2;
}

void linerel( int dx, int dy )
{
    XDrawLine( _display, _window, _gc, current_x, current_y, 
                    current_x + dx, current_y + dy);
    XFlush( _display );
    current_x += dx;
    current_y += dy;
}

void circle( int x, int y, int radius )
{
    XDrawArc( _display, _window, _gc, x-radius, y-radius, 
                     radius*2, radius*2, 0, 360*64 ); 
    XFlush( _display );
    current_x = x;
    current_y = y;
}

void arc( int x, int y, int sangle, int eangle, int radius )
{
    XDrawArc( _display, _window, _gc, x-radius, y-radius, 
                     radius*2, radius*2, sangle*64, eangle*64 ); 
    XFlush( _display );
    current_x = x;
    current_y = y;
}

void ellipse( int x, int y, int sangle, int eangle, int xradius, int yradius )
{
    XDrawArc( _display, _window, _gc, x-xradius, y-yradius, 
                     xradius*2, yradius*2, sangle*64, eangle*64 ); 
    XFlush( _display );
    current_x = x;
    current_y = y;
}

void fillellipse( int x, int y, int sangle, int eangle, 
                                      int xradius, int yradius )
{
    XFillArc( _display, _window, _gc, x-xradius, y-yradius, 
                     xradius*2, yradius*2, sangle*64, eangle*64 ); 
    XFlush( _display );
    current_x = x;
    current_y = y;
}


/* ============================================================= */
/*  Move Current                                                 */

void moveto( int x1, int y1 )
{
    current_x = x1;
    current_y = y1;
}

void moverel( int dx, int dy )
{
    current_x += dx;
    current_y += dy;
}

int getx( void )
{
    return current_x;
}

int gety( void )
{
    return current_y;
}

/* ===== End of Graphics.h ===== */
