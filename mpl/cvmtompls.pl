#!/usr/bin/perl

my $wordsize = 8;

my $inf;
if ($ARGV[0]) { $inf = $ARGV[0]; }
else {
 print "Input file ? ";
 $inf = <STDIN>;
 chomp $inf;
}
open IN, $inf or die "$inf: $!\n";

my $outf;
if ($ARGV[1]) { $outf = $ARGV[1]; }
else {
 print "Output file ? ";
 $outf = <STDIN>;
 chomp $outf;
}
open OUT, ">$outf" or die "$outf: $!\n";

print OUT "[ZERO*A00] #6000H\n";
print OUT "

( hexadecimal digits )
h,[digits]W
{0123456789ABCDEF}

( coding of loading of R0 )
h,[code_load_R0]W
{[code_load_R0_ret]W
#23_
#1C,[load_value]R>,#F&,[digits]R+r_
#18,[load_value]R>,#F&,[digits]R+r_
#14,[load_value]R>,#F&,[digits]R+r_
#10,[load_value]R>,#F&,[digits]R+r_
#C,[load_value]R>,#F&,[digits]R+r_
#8,[load_value]R>,#F&,[digits]R+r_
#4,[load_value]R>,#F&,[digits]R+r_
[load_value]R,#F&,[digits]R+r_
#,[code_load_R0_ret]R?}

(print hexadecimal)
h,[print_hex]W
{[print_hex_ret]W
#1C,[print_hex_nbr]R>,#F&,[digits]R+rP
#18,[print_hex_nbr]R>,#F&,[digits]R+rP
#14,[print_hex_nbr]R>,#F&,[digits]R+rP
#10,[print_hex_nbr]R>,#F&,[digits]R+rP
#C,[print_hex_nbr]R>,#F&,[digits]R+rP
#8,[print_hex_nbr]R>,#F&,[digits]R+rP
#4,[print_hex_nbr]R>,#F&,[digits]R+rP
[print_hex_nbr]R,#F&,[digits]R+rP
#,[print_hex_ret]R?}

(scan hexadecimal)
h,[scanhex]W
{[scanhex_ret]W
#,[scanhex_res]W
:scanhex_loop:
G,[scanhex_char]W
[scanhex_char]R,#30-,$scanhex_0$?
[scanhex_char]R,#31-,$scanhex_1$?
[scanhex_char]R,#32-,$scanhex_2$?
[scanhex_char]R,#33-,$scanhex_3$?
[scanhex_char]R,#34-,$scanhex_4$?
[scanhex_char]R,#35-,$scanhex_5$?
[scanhex_char]R,#36-,$scanhex_6$?
[scanhex_char]R,#37-,$scanhex_7$?
[scanhex_char]R,#38-,$scanhex_8$?
[scanhex_char]R,#39-,$scanhex_9$?
[scanhex_char]R,#41-,$scanhex_A$?
[scanhex_char]R,#42-,$scanhex_B$?
[scanhex_char]R,#43-,$scanhex_C$?
[scanhex_char]R,#44-,$scanhex_D$?
[scanhex_char]R,#45-,$scanhex_E$?
[scanhex_char]R,#46-,$scanhex_F$?
#,[scanhex_ret]R?
:scanhex_0:#4,[scanhex_res]R<,[scanhex_res]W#,$scanhex_loop$?
:scanhex_1:#4,[scanhex_res]R<,#1+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_2:#4,[scanhex_res]R<,#2+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_3:#4,[scanhex_res]R<,#3+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_4:#4,[scanhex_res]R<,#4+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_5:#4,[scanhex_res]R<,#5+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_6:#4,[scanhex_res]R<,#6+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_7:#4,[scanhex_res]R<,#7+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_8:#4,[scanhex_res]R<,#8+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_9:#4,[scanhex_res]R<,#9+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_A:#4,[scanhex_res]R<,#A+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_B:#4,[scanhex_res]R<,#B+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_C:#4,[scanhex_res]R<,#C+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_D:#4,[scanhex_res]R<,#D+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_E:#4,[scanhex_res]R<,#E+,[scanhex_res]W#,$scanhex_loop$?
:scanhex_F:#4,[scanhex_res]R<,#F+,[scanhex_res]W#,$scanhex_loop$?
}

h,[START]W {
";

while (<IN>)
{
 chomp $_;
 print OUT "($_) " . " " x (20 - length $_);
 if (($_ =~ /^(.*)@(.*)$/) and not ($_ =~ /defword/))
 {
  $_ = "$1\$$2\$";
 }
 if ($_ =~ /^\s*rem (.*)$/)
 {
 }
 elsif ($_ =~ /^\s*:(.*)/)
 {
  print OUT ":$1:";
 }
 elsif ($_ =~ /^\s*res ([0-9A-F]*)/)
 {
  print OUT "}h,#$1+H{";
 }
 elsif ($_ =~ /^\s*align 4\s*$/)
 {
  print OUT "}h,#3+,[ADR]W#2,[ADR]R><H{";
 }
 elsif ($_ =~ /^\s*defword (.*)\s*$/)
 {
  print OUT "(defword $1)";

 }
 elsif ($_ =~ /^\s*r([0123ABC])=r([0123ABC])\s*$/)
 {
  print OUT "[R$2]R,[R$1]W";
 }
 elsif ($_ =~ /^\s*code r([01A])=\{r0\}\s*$/)
 {
  print OUT "[R0]R,[load_value]W#,[code_load_R0]R?{,[R$1]W}}{";
 }
 elsif ($_ =~ /^\s*r([0123ABC])=\[r([0123ABC])\]\s*$/)
 {
  print OUT "[R$2]RR,[R$1]W";
 }
 elsif ($_ =~ /^\s*r([0123ABC])=byte\[r([0123ABC])\]\s*$/)
 {
  print OUT "[R$2]Rr,[R$1]W";
 }
 elsif ($_ =~ /^\s*\[r([0123ABC])\]=r([0123ABC])\s*$/)
 {
  print OUT "[R$2]R,[R$1]RW";
 }
 elsif ($_ =~ /^\s*byte\[r([0123ABC])\]=r([0123ABC])\s*$/)
 {
  print OUT "[R$2]R,[R$1]Rw";
 }
 elsif ($_ =~ /^\s*r([0123ABC])=\[r([0123ABC])\+([0-9A-F]*)\]\s*$/)
 {
  print OUT "#$3,[R$2]R+R,[R$1]W";
 }
 elsif ($_ =~ /^\s*\[r([0123ABC])\+([0-9A-F]*)\]=r([0123ABC])\s*$/)
 {
  print OUT "#$2,[R$1]R+,[ADR]W[R$3]R,[ADR]RW";
 }
 elsif ($_ =~ /^\s*r([0123ABC])=\[r([0123ABC])\+\+\]\s*$/)
 { 
  print OUT "[R$2]RR,[R$1]W#4,[R$2]R+,[R$2]W";
 }
 elsif ($_ =~ /^\s*\[r([0123ABC])\+\+\]=r([0123ABC])\s*$/)
 { 
  print OUT "[R$2]R,[R$1]RW#$wordsize,[R$1]+,[R$1]W";
 }
 elsif ($_ =~ /^\s*\[--r([0123ABC])\]=r([0123ABC])\s*$/)
 {
  print OUT "#$wordsize,[R$1]R-,[R$1]W[R$2]R,[R$1]RW";
 } 
 elsif ($_ =~ /^\s*r0=r0(\+|\*|[-&])r1\s*$/)
 {
  print OUT "[R1]R,[R0]R$1,[R0]W";
 }
 elsif ($_ =~ /^\s*bz (.*)\s*$/)
 {
  print OUT ";;;;;;;;;;;;[R0]R,#$1?";
 }
 elsif ($_ =~ /^\s*bp (.*)\s*$/)
 {
  print OUT "#80000000,[R0]R&~,#$1?";
 }
 elsif ($_ =~ /^\s*call r([0123ABC])\s*$/)
 {
  print OUT "#,[R$1]R?";
 }
 elsif ($_ =~ /^\s*call (.*)\s*$/)
 {
  print OUT "#,#$1?";
 }
 elsif ($_ =~ /^\s*getchar\s*$/)
 {
  print OUT "G,[R0]W";
 }
 elsif ($_ =~ /^\s*putchar\s*$/)
 {
  print OUT "[R0]RP";
 }
 elsif ($_ =~ /^\s*code\s*$/)
 {
  print OUT "[RC]RH{";
 }
 elsif ($_ =~ /^\s*endcode\s*$/)
 {
  print OUT "}}{h,[RC]W";
 }
 elsif ($_ =~ /^\s*beginf\s*$/)
 {
  print OUT "[ADR]W#$wordsize,[RS]R+,[RS]W[ADR],[RS]RW";
 }
 elsif ($_ =~ /^\s*endf\s*$/)
 {
  print OUT "[RS]RR,[ADR]W#$wordsize,[RS]R-,[RS]W#,[ADR]R?";
 }
 elsif ($_ =~ /^\s*scanhex\s*$/)
 {
  print OUT "#,[scanhex]R?[scanhex_res]R,[R0]W";
 }
 elsif ($_ =~ /^\s*setbradr\s*$/)
 {
  print OUT "[RA]R,#1E+H[R0]R,[load_value]W#,[code_load_R0]R?";
 }
 elsif ($_ =~ /^\s*initcvm\s*$/)
 {
 }
 elsif ($_ =~ /^\s*asr\s*r([0123ABC])\s*$/)
 {
  print OUT "#1,[R$1]R>,[R$1]W";
 }
 elsif ($_ =~ /^\s*dummyprint\s*$/)
 {
 }
 elsif ($_ =~ /^\s*resetdraw\s*$/)
 {
 }
 elsif ($_ =~ /^\s*invalidate\s*$/)
 {
 }
 elsif ($_ =~ /^\s*draw\s*$/)
 {
 } 
 elsif ($_ =~ /^\s*dumpcode\s*$/)
 {
 }
 elsif ($_ =~ /^\s*unicode (.*)$/)
 {
  my @a = split //, $1;
  foreach $c (@a)
  {
   print OUT "$c}#_{";
  }
  print OUT "}#_#_{";
 }
 elsif ($_ =~ /^\s*fopen\s*$/)
 {
  print OUT "[R0]R,#1<,#10+,[FN]W[R1]R,[FN]RS[R0]W";
 }
 elsif ($_ =~ /^\s*fclose\s*$/)
 {
  print OUT "[R0]R,#1FS#,[R0]W";
 }
 elsif ($_ =~/^\s*fgetc\s*$/)
 {
  print OUT "[R0]R,[FH]W#,[CHAR]W[FH],#21S[CHAR]R,[R0]W";
 }
 elsif ($_ =~ /^\s*printhex\s*$/)
 {
  print OUT "[R0]R,[print_hex_nbr]W#,[print_hex]R?";
 }
 elsif ($_ =~ /^\s*exit\s*$/)
 {
  print OUT "Q";
 }
 elsif ($_ =~ /^\s*r([0123ABC])=(.*)\s*$/)
 {
  print OUT "#$2,[R$1]W";
 }
 elsif (not ($_ =~ /^\s*$/))
 {
  print OUT "(*** UNDEFINED INSTRUCTION ***)";
 }
 

 print OUT "\n";
}

print OUT "} #,[START]R?\n";

close IN;
close OUT;


