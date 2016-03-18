echo compiling labels
./mplc_labels.pl $1.mpls $1.mpli
echo compiling identifiers
./mplc_ids.pl $1.mpli $1.mplo
echo running
./mpli.pl $1.mplo

