echo Build MPL object code
./mplc_labels.pl forth.mpls forth.mpli
./mplc_ids.pl forth.mpli forth.mplo
echo Build MPL interpreter
cc -o mpli mpli.c
echo To run Forth compiler with MPL interpreter in Perl :
echo ./mpli.pl forth.mplo
echo To run Forth compiler with MPL interpreter in C :
echo ./mpli forth.mplo
