#!/usr/bin/perl

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
my $next = hex('5000');
my %dic = ();
my %nrefs = ();
my %labels = ();
my $id = '';
my $nr;
my $i;

my $c = getc SRC;

while ($goon != 0)
{
 # print "c=$c=" . ord($c) . "\n";
 if ($c eq '\\')
 {
  if (eof SRC) {last; }
  $c = getc SRC;
  print $obj '\\' . $c;
  if (eof SRC) { last; }
  $c = getc SRC;
 }
 elsif ($c eq '(')
 {
  while ($c ne ')')
  {
   if (eof SRC) { last; }
   $c = getc SRC;
  }
  if (eof SRC) { last; }
  $c = getc SRC;
 }
 elsif ($c eq ':')
 {
  $id = '';
  if (eof SRC) { last; }
  $c = getc SRC;
  while ($c ne ':')
  {
   $id = $id . $c;
   if (eof SRC) { last; }
   $c = getc SRC;
  }
  if (eof SRC){ last; }
  $c = getc SRC;
  if ($labels{$id})
  {
   die "Error: label $id redefined.\n";
  }
  else
  {
   $labels{$id} = 1;
   print $obj "}h,[$id]W\n";
   if (defined($nrefs{$id}))
   {
    $nr = $nrefs{$id};
   }
   else
   {
    $nr = 0;
   }
   for ($i=1; $i<=$nr; $i++)
   {
    print $obj "[$id" . "_ref$i]RH[$id]R,[load_value]W#,[code_load_R0]R?\n";
   }
   print $obj "[$id]RH{";
  }
 }
 elsif ($c eq '$')
 {
  $id = '';
  if (eof SRC) { last; }
  $c = getc SRC;
  while ($c ne '$')
  {
   $id = $id . $c;
   if (eof SRC) { last; }
   $c = getc SRC;
  }
  if (eof SRC){ last; }
  $c = getc SRC;
  if ($labels{$id})
  {
   print $obj "}[$id]R,[load_value]W#,[code_load_R0]R?{"; 
  }
  else
  {
   if (defined($nrefs{$id}))
   {
    $nr = $nrefs{$id};
   }
   else
   {
    $nr = 0;
   }
   $nr++;
   $nrefs{$id} = $nr;
   print $obj "}h,[$id" . "_ref$nr]W{eeeeeeeee";
  }
 }
 else
 {
  print $obj $c;
  if (eof SRC) { last; }
  $c = getc SRC;
 } 
}

close SRC;
close OBJ;

