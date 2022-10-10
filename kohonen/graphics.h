
#define grOk 0

enum graphics_drivers { 	/* define graphics drivers */
	DETECT, 		/* requests autodetection */
	CGA, MCGA, EGA, EGA64, EGAMONO, IBM8514,	/* 1 - 6 */
	HERCMONO, ATT400, VGA, PC3270,			/* 7 - 10 */
	CURRENT_DRIVER = -1
};

enum graphics_modes {		/* graphics modes for each driver */
    CGAC0      = 0,  /* 320x200 palette 0; 1 page	*/
    CGAC1      = 1,  /* 320x200 palette 1; 1 page	*/
    CGAC2      = 2,  /* 320x200 palette 2: 1 page	*/
    CGAC3      = 3,  /* 320x200 palette 3; 1 page	*/
    CGAHI      = 4,  /* 640x200 1 page			*/
    MCGAC0     = 0,  /* 320x200 palette 0; 1 page	*/
    MCGAC1     = 1,  /* 320x200 palette 1; 1 page	*/
    MCGAC2     = 2,  /* 320x200 palette 2; 1 page	*/
    MCGAC3     = 3,  /* 320x200 palette 3; 1 page	*/
    MCGAMED    = 4,  /* 640x200 1 page			*/
    MCGAHI     = 5,  /* 640x480 1 page			*/
    EGALO      = 0,  /* 640x200 16 color 4 pages	*/
    EGAHI      = 1,  /* 640x350 16 color 2 pages	*/
    EGA64LO    = 0,  /* 640x200 16 color 1 page 	*/
    EGA64HI    = 1,  /* 640x350 4 color  1 page 	*/
    EGAMONOHI  = 0,  /* 640x350 64K on card, 1 page - 256K on card, 4 pages */
    HERCMONOHI = 0,  /* 720x348 2 pages 		*/
    ATT400C0   = 0,  /* 320x200 palette 0; 1 page	*/
    ATT400C1   = 1,  /* 320x200 palette 1; 1 page	*/
    ATT400C2   = 2,  /* 320x200 palette 2; 1 page	*/
    ATT400C3   = 3,  /* 320x200 palette 3; 1 page	*/
    ATT400MED  = 4,  /* 640x200 1 page			*/
    ATT400HI   = 5,  /* 640x400 1 page			*/
    VGALO      = 0,  /* 640x200 16 color 4 pages	*/
    VGAMED     = 1,  /* 640x350 16 color 2 pages	*/
    VGAHI      = 2,  /* 640x480 16 color 1 page 	*/
    PC3270HI   = 0,  /* 720x350 1 page			*/
    IBM8514LO  = 0,  /* 640x480 256 colors		*/
    IBM8514HI  = 1   /*1024x768 256 colors		*/
};

void detectgraph (int *pdriver, int *pmode);

void initgraph (int *pdriver, int *pmode, char *s);

int graphresult(void);

void restorecrtmode(void);

void putpixel (int x, int y, int c);

void drawline (int x1, int y1, int x2, int y2, int c);

void clear (void);

void endgraph (void); 


