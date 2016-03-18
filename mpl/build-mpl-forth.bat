echo off
echo Build MPL object code
mplc_labels.pl forth.mpls forth.mpli
mplc_ids.pl forth.mpli forth.mplo
echo Create Forth compiler with MPLI.COM interpreter
copy /b mpli.com+forth.mplo forth.com
echo To run Forth compiler with MPL interpreter in Perl :
echo mpli.pl forth.mplo
echo To run Forth compiler with MPLI.COM interpreter :
echo forth.com
