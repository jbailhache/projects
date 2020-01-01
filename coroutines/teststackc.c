
int g (int y)
{
int e;
	e = y;
	e = 2*e+1;
	return e;
}

int f (int x, int y)
{
int c, d;
	c = x;
	{
		char buf[c];
		d = g(y);
	}
	return d;
}

int main ()
{
int a, b, c;	
	a = 256;
	b = 123;
	c = f(a,b);
}
