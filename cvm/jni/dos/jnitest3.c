
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
 printf ("Initializing...");
 initialize();
 printf ("Main loop...\n");
 for (;;)
 {
  printf ("\n? ");
  gets (inbuf);
  inptr = inbuf;
  outptr = outbuf; 
  cvm();
  *outptr = 0;
  printf ("-> %s", outbuf);
 }
}


