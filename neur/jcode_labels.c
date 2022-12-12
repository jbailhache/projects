// Usage : ./jcode_labels data_filename variable_name n > j_source_filename.ijs

#include <stdio.h>
#include <stdlib.h>
#include <byteswap.h>

void main (int argc, char *argv[])
{
    FILE *f;
    int magic;
    int n;
    int i;
    unsigned char x;
    f = fopen(argv[1], "rb");
    fread(&magic, 4, 1, f);
    magic = __bswap_32(magic);
    fread(&n, 4, 1, f);
    n = __bswap_32(n);
    // printf("magic=%d n=%d\n", magic, n);
    printf("%s =: ", argv[2]);
    for (i=0; i<n && (argc<4 || i<atoi(argv[3])); i++) {
        fread(&x, 1, 1, f);
        printf (" %d", x);
    }
    printf("\n");
    fclose(f);
}
