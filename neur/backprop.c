// Backpropagation
// See https://www.miximum.fr/blog/introduction-au-deep-learning-2/
// Build : cc -o backprop backprop.c -lm 

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <time.h>

typedef long double real;
/*
real sampleNormal() {
    real u = ((real) rand() / (RAND_MAX)) * 2 - 1;
    real v = ((real) rand() / (RAND_MAX)) * 2 - 1;
    real r = u * u + v * v;
    if (r == 0 || r > 1) return sampleNormal();
    real c = sqrt(-2 * log(r) / r);
    return u * c;
}
*/

int randomLessThan (int n)
{
	return rand() % n;
}

// return a uniformly distributed random number
real RandomGenerator()
{
  return ( (real)(rand()) + 1. )/( (real)(RAND_MAX) + 1. );
}

// return a normally distributed random number
real normalRandom()
{
  real y1=RandomGenerator();
  real y2=RandomGenerator();
  return cos(2*3.1415926*y2)*sqrt(-2.*log(y1));
}

real sigma (real x)
{
	return 1 / (1 + exp(-x));
}

real sigmaprime (real x)
{
	return sigma(x) * (1 - sigma(x));
}

#define nl 5 			// Number of layers
#define npl 6 			// Number of neurons per layer
#define n (nl * npl) 	// Total number of neurons
#define p 10
#define alpha 3			// Learning rate
#define nX 3			// Number of inputs

real W[n][n];		    // Matrix of connection weights
					    // Element at i-th line and j-th column = weight of connection from neuron j to neuron i 
real B[n];		    // Biases
real X[n][nX];	    // Inputs, i-th column = vector representing the i-th input
real T[n][nX];	    // Expected outputs
real Z[n][nX];	    // Aggregation
real A[n][nX];	    // Activations
real delta[n][nX];
real delta1[n][nX];
real avgdelta[n];
real GW[n][n];		// Gradient of weights
real GB[n];			// Gradient of biases

void init (void) 
{
	srand(time(NULL));
	int l, i, j;
	// for (i=0; i<10; i++) printf("%d\n", randomLessThan(p));
	// for (i=0; i<10; i++) printf("%Lf\n", normalRandom());
	
	for (i=0; i<n; i++)
		for (j=0; j<n; j++)
			W[i][j] = 0;
	for (l=0; l<nl-1; l++)
		for (i=0; i<npl; i++)
			for (j=0; j<npl; j++)
				W[(l+1)*npl+i][l*npl+j] = normalRandom();
	/*
	printf ("W :\n");
	for (i=0; i<n; i++)
	{
		for (j=0; j<n; j++)
			printf(" %4.1Lf", W[i][j]);
		printf("\n");
	}
	*/	
	for (i=0; i<n; i++)
		B[i] = 0;
	for (l=1; l<nl; l++)
		for (i=0; i<npl; i++)
			B[l*npl+i] = normalRandom();
	/*
	printf("B :\n");
	for (i=0; i<n; i++)
		printf(" %4.1Lf", B[i]);
	printf("\n");
	*/
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
			X[i][j] = 0;
	for (i=0; i<npl; i++)
		for (j=0; j<nX; j++)
			X[i][j] = (real)randomLessThan(p) / (real)p;
	/*
	printf("X :\n");
	for (i=0; i<n; i++)
	{
		for (j=0; j<nX; j++)
			printf(" %4.1Lf", X[i][j]);
		printf("\n");
	}
	*/
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
			T[i][j] = 0;
	for (i=0; i<npl; i++)
		for (j=0; j<nX; j++)
			T[(nl-1)*npl+i][j] = (real)randomLessThan(p) / (real)p;	
	/*
	printf("T :\n");
	for (i=0; i<n; i++)
	{
		for (j=0; j<nX; j++)
			printf(" %4.1Lf", T[i][j]);
		printf("\n");
	}
	*/
}

void step (void)
{
	int i, j, k;
	// Aggregation : add biases and matrix product of weights by activations
	// Z =: B + W +/ . * A 
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
		{
			Z[i][j] = 0;
			for (k=0; k<n; k++)
				Z[i][j] += W[i][k] * A[k][j];
		}
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
			Z[i][j] += B[i];		
	// Activation : fixed values X for input neurons, sigma applied to aggregation for others
	// A =: (maskX * X) + (1-maskX) * sigma Z
	for (i=0; i<npl; i++)
		for (j=0; j<nX; j++)
			A[i][j] = X[i][j];
	for (i=npl; i<n; i++)
		for (j=0; j<nX; j++)
			A[i][j] = sigma(Z[i][j]);
}

// One step of backpropagation
// delta^L_i = A - T
// delta^l_i = sigma'(z^l_i) * sum_j(w^{l+1}_{ji} delta^{l+1}_j
void stepdelta (void)
{
	int i, j, k;
	// delta =: (maskO * A - T) + (sigmaprime Z) * (|: W) +/ . * delta
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
		{
			delta1[i][j] = 0;
			for (k=0; k<n; k++)
				delta1[i][j] += W[k][i] * delta[k][j];
		}
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
			delta1[i][j] *= sigmaprime(Z[i][j]);
	for (i=(nl-1)*npl; i<n; i++)
		for (j=0; j<nX; j++)
			delta1[i][j] += A[i][j] - T[i][j];
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
			delta[i][j] = delta1[i][j];
}

// Step of learning
void steplearn (void)
{
	int i, j, k, l, s;
	// Initialize activation with input
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
			A[i][j] = X[i][j];
	// Repeat aggregation and activation nl-1 times
	for (s=0; s<nl-1; s++)
		step();
	// delta = 0
	for (i=0; i<n; i++)
		for (j=0; j<nX; j++)
			delta[i][j] = 0;
	// Repeat backpropagation nl times
	for (s=0; s<nl; s++)
		stepdelta();
	// Average delta
	// avgdelta =: (+/ |: delta) % nX
	for (i=0; i<n; i++)
	{
		avgdelta[i] = 0;
		for (j=0; j<nX; j++)
			avgdelta[i] += delta[i][j];
		avgdelta[i] /= nX;
	}
	// Average gradient of weights for nX inputs
	// dC/dw^l_{ij} = a^{l-1}_j delta^l_i
	// GW =: maskW * delta +/ . * |: A % nX
	for (i=0; i<n; i++)
		for (j=0; j<n; j++)
			GW[i][j] = 0;
	for (l=1; l<nl-1; l++)
		for (i=0; i<npl; i++)
			for (j=0; j<npl; j++)
				for (k=0; k<nX; k++)
					GW[(l+1)*npl+i][l*npl+j] += delta[(l+1)*npl+i][k] * A[l*npl+j][k] / nX;
	// Average gradient of biases for nX inputs
	// dC/db_i = delta^l_i
	for (i=0; i<npl; i++)
		GB[i] = 0;
	for (i=npl; i<n; i++)
		GB[i] = avgdelta[i];
	// Modifiy weights and biases
	for (i=0; i<n; i++)
		for (j=0; j<n; j++)
			W[i][j] -= alpha * GW[i][j];
	for (i=0; i<n; i++)
		B[i] -= alpha * GB[i];
}

void main (void)
{
	int i, j, s;
	init();
	for (s=0; s<10000; s++)
		steplearn();
	for (i=(nl-1)*npl; i<n; i++)
	{
		for (j=0; j<nX; j++)
			printf (" %9.6Lf ", A[i][j] - T[i][j]);
		printf("\n");
	}
}

