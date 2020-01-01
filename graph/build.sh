#!/bin/sh
cc -w -o chaos chaos.c graphics.c -lX11
cc -w -o interf interf.c graphics.c -lX11 -lm
cc -w -o diffract diffract.c graphics.c -lX11 -lm
cc -w -o intrfdif intrfdif.c graphics.c -lX11 -lm
cc -w -o intrdif1 intrdif1.c graphics.c -lX11 -lm
cc -w -o intrf4tr intrf4tr.c graphics.c -lX11 -lm
cc -w -o intrf5tr intrf5tr.c graphics.c -lX11 -lm

