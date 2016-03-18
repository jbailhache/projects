#!/usr/bin/perl

my $wordsize = 8;
my $sourcef;
my $objf;
my $obj;

my $nargs = @ARGV;
if ($nargs >= 1)
{
 $sourcef = $ARGV[0];
 $objf = $ARGV[1];
}
else
{
 print "Source file ? ";
 $sourcef = <STDIN>;
 chomp $sourcef;

 print "Object file ? ";
 $objf = <STDIN>;
 chomp $objf;
}

open SRC, $sourcef or die "$sourcef: $!\n";

if ($objf eq '')
{
 $obj = *STDOUT;
}
else
{
 open OBJ, ">$objf" or die "$objf: $!\n";
 $obj = *OBJ;
}

my $goon = 1;
# my $next = hex('5000');
my $next = 0;
my %dic = ();
my $c = getc SRC;

while ($goon != 0)
{
 # print "c=$c=" . ord($c) . "\n";
 if ($c eq '\\')
 {
  if (eof SRC) {last; }
  $c = getc SRC;
  print $obj $c;
  if (eof SRC) { last; }
  $c = getc SRC;
 }
 elsif ($c eq '[')
 {
  my $id = '';
  my $size = '1';
  if (eof SRC) { last; }
  $c = getc SRC;
  while (($c ne ']') && ($c ne '*'))
  {
   $id = $id . $c;
   if (eof SRC) { last; }
   $c = getc SRC;
  }
  if ($c eq '*')
  {
   if (eof SRC) { last; }
   $c = getc SRC;
   $size = '';
   while ($c ne ']')
   {
    $size = $size . $c;
    if (eof SRC) { last; }
    $c = getc SRC;
   }
  }
  if (eof SRC) { last; }
  $c = getc SRC;
  if (!defined ($dic{$id}))
  {
   $dic{$id} = $next;
   $next += $wordsize * hex($size);
  }
  print $obj "#" . sprintf ('%X', $dic{$id});
 }
 else
 {
  print $obj $c;
  if (eof SRC) { last; }
  $c = getc SRC;
 } 
}

my %rev = ();
foreach $id(keys %dic)
{
 $rev{$dic{$id}} = $id;
}

open DIC, ">$sourcef.dic";
foreach $adr(sort keys %rev)
{
 print DIC sprintf("%04X",$adr) . " $rev{$adr}\n";
}
close DIC;

# print $obj "\n#" . sprintf ('%X', $next) . "\n";

close SRC;
close OBJ;

