#!/usr/bin/perl

my $wordsize = 8;

my $forthf;
if ($ARGV[0])
{
 $forthf = $ARGV[0];
}
else
{
 print "Forth source ? ";
 $forthf = <STDIN>;
 chomp $forthf;
}
open FORTH, $forthf or die "$srcf: $!\n";

my $mplsf;
if ($ARGV[1])
{
 $mplsf = $ARGV[1];
}
else
{
 print "MPL source ? ";
 $mplsf = <STDIN>;
 chomp $mplf;
}
open MPLS, ">$mplsf" or die "$mplsf: $!\n";

my $i;

my %words = ();
my $lastword = '';

# print "Translating...\n";

print MPLS "[ZERO*A00]\n#6000H\n";
print MPLS "
(hexadecimal digits)
h,[digits]W
{0123456789ABCDEF}

(coding of loading of R0)
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
";

print MPLS "#2000,[sp]W\n";

my $state = 'run';

while (<FORTH>)
{
 # print "New line\n";
 my @words = split /[\s\t\r\n]/, $_;
 my $n = @words;
 for ($i=0; $i<$n; $i++)
 {
  $w = $words[$i];
  # print "$i: $w\n";
  print MPLS "($w) ";
  if ($state eq 'defword')
  {
   $worddef = $w;
   $state = 'defbody';
   print MPLS "h,[$w]W{[$w" . "_ret]W";
   $words{$w} = "#,[$w]R?";
   $lastword = $w;
  }
  elsif (($state eq 'defbody') and ($w eq ';'))
  {
    print MPLS "#,[$worddef" . "_ret]R?}";
    $state = 'run';
  }
  elsif ($state eq 'variable')
  {
   print MPLS "h,[$w]W{[$w"."_ret]W#$wordsize,[sp]R-,[sp]W[adr_$w],[sp]RW#,[$w"."_ret]R?}";
   $state = 'run';
  }
  elsif ($state eq '[compile]')
  {
   print MPLS "#,[$w]R?";
   $state = 'defbody';
  }
  elsif ($state eq 'compile')
  {
   print MPLS "{#,[$w]R?}}{";
   $state = 'defbody';
  }
  elsif ($w eq ':')
  {
   $state = 'defword';
  }
  elsif ($w eq 'VARIABLE')
  {
   $state = 'variable';
  }
  elsif ($w eq 'DROP')
  {
   print MPLS "#$wordsize,[sp]R+,[sp]W";
  }
  elsif ($w eq 'DUP')
  {
   print MPLS "[sp]RR,[st]W#$wordsize,[sp]R-,[sp]W[st]R,[sp]RW";
  }
  elsif ($w eq 'SWAP')
  {
   print MPLS "[sp]RR,[st]W#$wordsize,[sp]R+R,[su]WR,[sp]RW#$wordsize,[sp]R+,[adr]W[st]R,[adr]RW";
  }
  elsif ($w eq '@')
  {
   print MPLS "[sp]RRR,[sp]RW";
  }
  elsif ($w eq '!')
  { 
   print MPLS "[sp]RR,[adr]W#$wordsize,[sp]R+,[sp]WRR,[adr]RW#$wordsize,[sp]R+,[sp]W";
  }
  elsif ($w eq 'KEY')
  {
   print MPLS "#$wordsize,[sp]R-,[sp]WG,[sp]RW";
  }
  elsif ($w eq 'EMIT') 
  { 
   print MPLS "[sp]RRP#$wordsize,[sp]R+,[sp]W";
  }
  elsif ($w eq 'HERE')
  {
   print MPLS "#$wordsize,[sp]R-,[sp]Wh,[sp]RW";
  }
  elsif ($w eq 'SP@')
  {
   print MPLS "#$wordsize,[sp]R-,[sp]W#$wordsize,[sp]R+,[sp]RW";
  }
  elsif ($w eq '[')
  {
   print MPLS "}";
  }
  elsif ($w eq ']')
  {
   print MPLS "{";
  }
  elsif ($w eq 'IMMEDIATE')
  {
   $words{$lastword} = "}#,[$lastword]R?{";
  }
  elsif ($w eq '[COMPILE]')
  {
   $state = '[compile]'; 
  }
  elsif ($w eq 'COMPILE')
  {
   $state = 'compile';
  }
  elsif ($w eq ',')
  {
   print MPLS "[sp]RR_#$wordsize,[sp]R+,[sp]W";
  }
  elsif ($w eq 'TRACE')
  {
   print MPLS "T";
  }
  elsif ($w eq 'BYE')
  {
   print MPLS "Q";
  }
  elsif (($w eq '+') or ($w eq '-') or ($w eq '*') or ($w eq '/') or ($w eq '/') or ($w eq '%') or ($w eq '&') or ($w eq '|') or ($w eq '<') or ($w eq '>'))
  {
   print MPLS "[sp]RR,[st]W#$wordsize,[sp]R+,[sp]W[st]R,[sp]RR$w,[sp]RW";
   # print MPLS "[sp]RR,[st]W#4,[sp]R+,[sp]WRR,[st]R$w,[sp]RW";
  }
  
  elsif ($w =~ /^[0123456789][0123456789ABCDEF]*$/)
  {
   print MPLS "#$wordsize,[sp]R-,[sp]W#$w,[sp]RW";
  }
  elsif (defined ($words{$w}))
  {
   print MPLS $words{$w};
  }
  else
  {
   print MPLS "#,[$w]R?";
  }
  print MPLS "\n";
 }
}
