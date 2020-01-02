#!/bin/sh
cc -w -g -o nlp log.c stream.c coroutin.c util.c trace.c
./nlp <<END
la muson postkuras la kato.
END

