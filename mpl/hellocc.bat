rem compile labels
mplc_lab.com <helloc.mps >helloc.mpi
rem compile identifiers
mplc_ids.com <helloc.mpi >helloc.mpo
rem create executable
copy /b mpli.com+helloc.mpo helloc.com
rem run
helloc.com
