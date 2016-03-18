rem create labels compiler
copy /b mpli.com+mplc_labels.mplo mplc_lab.com
rem create identifiers compiler
copy /b mpli.com+mplc_ids.mplo mplc_ids.com
rem compile labels
mplc_lab.com <hello.mpls >hello.mpli
rem compile identifiers
mplc_ids.com <hello.mpli >hello.mplo
rem create hello executable
copy /b mpli.com+hello.mplo hello.com
rem run
hello.com

