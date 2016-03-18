rem compile labels
mplc_lab.com <testgo5.mps >testgo5.mpi
rem compile identifiers
mplc_ids.com <testgo5.mpi >testgo5.mpo
rem create executable
copy /b mpli.com+testgo5.mpo testgo5.com
rem run
testgo5.com
