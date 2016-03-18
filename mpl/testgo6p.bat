rem compile labels
mplc_labels.pl testgo6.mps testgo6.mpi
rem compile identifiers
mplc_ids.pl testgo6.mpi testgo6.mpo
rem create executable
copy /b mpli.com+testgo6.mpo testgo6.com
rem run
testgo6.com
