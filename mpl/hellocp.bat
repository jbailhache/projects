rem compile labels
mplc_labels.pl helloc.mps helloc.mpi
rem compile identifiers
mplc_ids.pl helloc.mpi helloc.mpo
rem create executable
copy /b mpli.com+helloc.mpo helloc.com
rem run
helloc.com
