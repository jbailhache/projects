rem test for dosbox
rem create labels compiler
copy /b mpli.com+mplc_lab.mpo mplc_lab.com
rem create identifiers compiler
copy /b mpli.com+mplc_ids.mpo mplc_ids.com
rem add eof character
echo õ >eof
copy hello.mps+eof hello1.mps
rem compile labels
mplc_lab.com <hello1.mps >hello.mpi
rem add eof character
copy hello.mpi+eof hello1.mpi
rem compile identifiers
mplc_ids.com <hello1.mpi >hello.mpo
rem create hello executable
copy /b mpli.com+hello.mpo hello.com
rem run
hello.com

