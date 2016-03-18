echo MPL test script

echo Clean
rm mplc_ids.mpli
rm mplc_ids.mplo
rm mplc_labels.mpli
rm mplc_labels.mplo
rm hello.mpli
rm hello.mplo

echo Build mplc_ids MPL object code
./mplc_labels.pl mplc_ids.mpls mplc_ids.mpli
./mplc_ids.pl mplc_ids.mpli mplc_ids.mplo

echo Build mplc_labels MPL object code
./mplc_labels.pl mplc_labels.mpls mplc_labels.mpli
./mplc_ids.pl mplc_labels.mpli mplc_labels.mplo

echo Build hello MPL object code
./mpli.pl mplc_labels.mplo hello.mpls hello.mpli
./mpli.pl mplc_ids.mplo hello.mpli hello.mplo

echo Run hello
./mpli.pl hello.mplo

