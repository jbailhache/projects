
#include <stdio.h>

char *stralloc (char *s)
{
char *r;
	r = malloc (strlen(s)+1);
	if (r == NULL)
	{
		fprintf (stderr, "Insufficient memory");
		exit (-1);
	}
	strcpy (r, s);
	return r;
}

int compare (char *s1, char *s2)
{
	return !strcmp (s1, s2);
}


