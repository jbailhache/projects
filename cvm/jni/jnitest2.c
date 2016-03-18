
char *inptr;
char inbuf[1000];
char *outptr;
char outbuf[1000];

char inputchar (void)
{
 return *inptr++;
}

void output (char *s)
{
 strcpy (outptr, s);
 outptr += strlen(s);
}

main ()
{
 for (;;)
 {
  gets (inbuf);
  inptr = inbuf;
  cvm();
  *outptr = 0;
  printf ("%s", outbuf);
 }
}


