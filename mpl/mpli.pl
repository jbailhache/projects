#!/usr/bin/perl

my $wordsize = 8;

my $trace = 0;

my $nargs = @ARGV;
my $script;
my $inputf;
my $outputf;
my $input;
my $output;

if ($nargs >= 1)
{ 
 $script = $ARGV[0]; 
 $inputf = $ARGV[1];
 $outputf = $ARGV[2];
} 
else
{
 print "Script ? ";
 $script = <STDIN>;
 chomp $script;

 print "Input file ? ";
 $inputf = <STDIN>;
 chomp $inputf;
 
 print "Output file ? ";
 $outputf = <STDIN>;
 chomp $outputf;
}

open SCRIPT, $script or die "$script: $!\n";

if (($inputf eq '') or ($inputf eq '-'))
{
 $input = *STDIN;
}
else
{
 open INPUT, $inputf or die "$inputf: $!\n";
 $input = *INPUT;
}

if (($outputf eq '') or ($outputf eq '-'))
{
 $output = *STDOUT;
}
else
{
 open OUTPUT, ">$outputf" or die "$outputf: $!\n";
 $output = *OUTPUT;
}
 

my @mem = ();
my $adr = 0;
my $state = 'normal';

# print "Reading code...\n";
while (<SCRIPT>)
{
 if ($trace != 0) { print $_; }
 @chars = split //, $_;
 foreach $char (@chars)
 {
  $mem[$adr++] = ord $char;    
 }
}
# print (sprintf "program size: %X\n", $adr);

my $goon = 1;
my $pc = 0;
my $r0 = 0;
my $r1 = 0;
my $rc = $adr;
my $ru = 0;
my $t;
my $instr;
$state = 'normal';
my $fh;

sub openfile 
{
 my $mode = shift;
 my $name = "";
 my $i = 0;
 # print "\nr1=" . (sprintf "%X",$r1) . " mem[r1]=" . (sprintf "%X", $mem[$r1]) . " i=$i\n";
 while ($mem[$r1+$i]!=0)
 {
  $name = $name . chr($mem[$r1+$i]);
  $i++;
 }
 # print "open file ($name) with mode ($mode)\n";
 open $fh, "$mode$name" or die "$name: $!\n";
 $r1 = $fh;
}

# print "Running...\n";
# $mem[0x7F00] = 0x30;
while ($goon != 0)
{
 # if ($mem[0x7F00] != 0x30) { $goon = 0; }
 # if (($trace == 1) && ($mem[0x3460] != 0x4000)) { $goon = 0; }
 $instr = chr($mem[$pc++]);
 if ($trace & 1) { print $instr; }

 if ($trace & 2) { 
  print ((sprintf "\nr0=%4X\tr1=%4X\trc=%4X\tru=%4X\tpc=%4X\tinstr=%s ",$r0,$r1,$rc,$ru,$pc,$instr) . (ord $instr) . " "); 
  my $r = <STDIN>; 
 }

 if ($state eq 'code') 
 {
  if ($instr eq '}') { $state = 'normal'; }
  else { $mem[$rc++] = ord $instr; }
 }
 elsif ($instr eq ',') { $r1 = $r0; }
 elsif ($instr eq 'X') { $t = $r0; $r0 = $r1; $r1 = $t; }
 elsif ($instr eq 'p') { $r0 = $pc; }
 elsif ($instr eq 'Q') { $goon = 0; }
 elsif ($instr eq '?') { if ($r1 == 0) { $r1 = $pc; $pc = $r0; } }
 elsif ($instr eq 'R') { $r0 = $mem[$r0]; }
 elsif ($instr eq 'W') { $mem[$r0] = $r1; }
 elsif ($instr eq 'r') { $r0 = $mem[$r0]; }
 elsif ($instr eq 'w') { $mem[$r0] = $r1; }
 elsif ($instr eq '#') { $r0 = 0; }

 elsif ($instr eq '0') { $r0 = $r0*16; }
 elsif ($instr eq '1') { $r0 = $r0*16+1; }
 elsif ($instr eq '2') { $r0 = $r0*16+2; }
 elsif ($instr eq '3') { $r0 = $r0*16+3; }
 elsif ($instr eq '4') { $r0 = $r0*16+4; }
 elsif ($instr eq '5') { $r0 = $r0*16+5; }
 elsif ($instr eq '6') { $r0 = $r0*16+6; }
 elsif ($instr eq '7') { $r0 = $r0*16+7; }
 elsif ($instr eq '8') { $r0 = $r0*16+8; }
 elsif ($instr eq '9') { $r0 = $r0*16+9; }
 elsif ($instr eq 'A') { $r0 = $r0*16+10; }
 elsif ($instr eq 'B') { $r0 = $r0*16+11; }
 elsif ($instr eq 'C') { $r0 = $r0*16+12; }
 elsif ($instr eq 'D') { $r0 = $r0*16+13; }
 elsif ($instr eq 'E') { $r0 = $r0*16+14; }
 elsif ($instr eq 'F') { $r0 = $r0*16+15; }

 elsif ($instr eq '~') { $r0 = -1 ^ $r0; }
 elsif ($instr eq '+') { $r0 = $r0 + $r1; }
 elsif ($instr eq '-') { $r0 = $r0 - $r1; }
 elsif ($instr eq '*') { $r0 = $r0 * $r1; }
 elsif ($instr eq '/') { $r0 = int ($r0 / $r1); }
 elsif ($instr eq '%') { $r0 = $r0 % $r1; }
 elsif ($instr eq '&') { $r0 = $r0 & $r1; }
 elsif ($instr eq '^') { $r0 = $r0 ^ $r1; }
 elsif ($instr eq '|') { $r0 = $r0 | $r1; }
 elsif ($instr eq '<') { $r0 = $r0 << $r1; }
 elsif ($instr eq '>') { $r0 = $r0 >> $r1; }

 elsif ($instr eq 'G') { if (eof($input)) { $r0 = -1; } else { $r0 = ord getc($input); } }
 elsif ($instr eq 'P') { print $output chr($r0); }
 elsif ($instr eq 'H') { $rc = $r0; }
 elsif ($instr eq 'h') { $r0 = $rc; }
 elsif ($instr eq '{') { $state = 'code'; }
 elsif ($instr eq '}') { $mem[$rc++] = ord $instr; }
 elsif ($instr eq '_') { $mem[$rc++] = $r0; }
 elsif ($instr eq 's') { $r0 = $wordsize; }

 elsif ($instr eq 'S')
 {
  if ($r0 == 0x11) { openfile "<"; }
  elsif ($r0 == 0x12) { openfile ">"; }
  elsif ($r0 == 0x13) { openfile ">>"; }
  elsif ($r0 == 0x14) { openfile "+<"; }
  elsif ($r0 == 0x15) { openfile "+>"; }
  # elsif ($r0 == 0x1F) { close $r1; }
  elsif ($r0 == 0x1F) { close $mem[$r1]; }
  # elsif ($r0 == 0x20) { $r0 = ord getc($r1); }
  elsif ($r0 == 0x20) { $mem[$r1+$wordsize] = ord getc($mem[$r1]); }
  elsif ($r0 == 0x21) { $fh = $mem[$r1]; print $fh chr($mem[$r1+$wordsize]); }
 }

 elsif ($instr eq 'T') { $trace = 2; }
 elsif ($instr eq 't') { $trace=1; } 
 elsif ($instr eq 'e') { print "\nError\n"; $goon = 0; }

 elsif ($instr eq 'u') { $r0 = $ru; }
 elsif ($instr eq 'U') { $ru = $r0; }
 elsif ($instr eq 'J') { $t = $r0; 
                         $r0 = $mem[$t];
                         $r1 = $mem[$t+$wordsize];
                         $pc = $mem[$t+2*$wordsize]; }
 elsif (($instr eq ' ') || 
        ($instr eq "\n") ||
        ($instr eq "\r") ||
        ($instr eq "\t") ||
        ($instr eq ";")) { }
 else {
  # print (sprintf "undefined pc=%X ru=%X\n", $pc, $ru);
  $mem[$ru] = $r0;
  $mem[$ru+$wordsize] = $r1;
  $mem[$ru+2*$wordsize] = $pc;
  $pc = $ru+3*$wordsize;
  # print (sprintf "undefined pc=%X ru=%X\n", $pc, $ru);
 }

}

# print "\nDone.\n";

close SCRIPT;
close INPUT;
close OUTPUT;



