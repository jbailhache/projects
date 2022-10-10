# Output to screen
cc -o kohonen kohonen.c graphics.c -lX11 -lm
# Output to PPM file image.ppm
cc -o kohonen-ppm kohonen.c graphics-ppm.c ppm.c -lm
