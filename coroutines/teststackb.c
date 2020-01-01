
int *sp ()
{
int *a;
	a = (int *)&a;
	a += 3;
	return a;
}

int main ()
{
int *a;
	a = sp();
}
