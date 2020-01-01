<?php

function range ($a, $b)
{
 $state = 0;
 switch ($state)
 {
  case 0:
   $state = 1;
   for ($i = $a; $i < $b; $i++)
   {
    return $i;
  case 1:
   }
 }
 $state = 0;
 return 0;
}

for (;;)
{
 $i = range(30,40);
 if ($i == 0)
  break;
 echo "$i\n";
} *


