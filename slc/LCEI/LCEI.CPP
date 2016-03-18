//---------------------------------------------------------------------------
#ifdef V98
#include <vcl\condefs.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <conio.h>

#ifdef V98
#pragma hdrstop
//---------------------------------------------------------------------------
USERES("lcei.res");
USEUNIT("util.cpp");
USEUNIT("dbsubst.cpp");
USEUNIT("ext.cpp");
USEUNIT("fncarg.cpp");
USEUNIT("ftrace.cpp");
USEUNIT("global.cpp");
USEUNIT("init.cpp");
USEUNIT("lambda.cpp");
USEUNIT("lcei1.cpp");
USEUNIT("lr.cpp");
USEUNIT("mk_dem.cpp");
USEUNIT("order.cpp");
USEUNIT("print.cpp");
USEUNIT("read.cpp");
USEUNIT("red.cpp");
USEUNIT("refl.cpp");
USEUNIT("simplif.cpp");
USEUNIT("stack.cpp");
USEUNIT("step.cpp");
USEUNIT("tracedem.cpp");
USEUNIT("typ.cpp");
USEUNIT("alloc.cpp");
//---------------------------------------------------------------------------
#endif
void lcei (void);
int main(int argc, char **argv)
{
char filename[200];
FILE *f;
    printf ("Input file ? ");
    gets (filename);
    if (filename[0])
    {
        f = freopen (filename, "r", stdin);
    	if (f == NULL)
        	perror (filename);
	}
    lcei ();
    while (!kbhit ());
	return 0;
}
//---------------------------------------------------------------------------
