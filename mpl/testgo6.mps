[ZERO*A00] ( variables start at address hexa 5000 = 1400*4 )
#6000H ( Begin of program )

( hexadecimal digits )
h,[digits]W
{0123456789ABCDEF}

#2x
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

h,[main]W
{[main_ret]W
#41,[a]W#,$l$?#42,[a]W:l:[a]RP
#,[main_ret]R?}
#,[main]R?Q

