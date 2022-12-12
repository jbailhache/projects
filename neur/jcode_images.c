// Usage : ./jcode_images data_filename variable_name n > j_source_filename.ijs

#include <stdio.h>
#include <stdlib.h>
#include <byteswap.h>

void main (int argc, char *argv[])
{
    FILE *f;
    int magic;
    int n;
    int nr;
    int nc;
    int i, r, c;
    unsigned char x;
    f = fopen(argv[1], "rb");
    fread(&magic, 4, 1, f);
    magic = __bswap_32(magic);
    fread(&n, 4, 1, f);
    n = __bswap_32(n);
    fread(&nr, 4, 1, f);
    nr = __bswap_32(nr);
    fread(&nc, 4, 1, f);
    nc = __bswap_32(nc);
    // printf("magic=%d n=%d nr=%d nc=%d\n", magic, n, nr, nc);
    printf("%s =: 0 0 $ 0\n", argv[2]);
    for (i=0; i<n && (argc<4 || i<atoi(argv[3])); i++) {
        // printf("Image %d\n", i);
        printf("%s =: %s ,", argv[2], argv[2]);
        for (r=0; r<nr; r++) {
            for (c=0; c<nc; c++) {
                fread(&x, 1, 1, f);
                //printf(" %02X ", x);
                printf(" %d", x);
            }
            //printf("\n");
        }
        printf("\n");
    }
    fclose(f);
}
