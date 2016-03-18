echo MPL test script

echo Clean
rm hello.mpli
rm hello.mplo

echo Build hello MPL object code
./mpli mplc_labels.mplo hello.mpls hello.mpli
./mpli mplc_ids.mplo hello.mpli hello.mplo

echo Run hello
./mpli.pl hello.mplo

