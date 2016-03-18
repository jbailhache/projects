[ZERO*A00] 
#6000H ( Begin of program )

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

( string to display, terminated by null )
h,[hello]W
{Hello World !
}#_

( display a string )
h,[display]W 
{[display_ret]W ( store return address )
:display_loop:
[display_ptr]Rr,$display_end$?
[display_ptr]RrP
[display_ptr]R,#1+,[display_ptr]W
#,$display_loop$?
:display_end:
#,[display_ret]R?} ( return )

( main function )
h,[main]W
{[main_ret]W
[hello]R,[display_ptr]W
#,[display]R?
#,[main_ret]R?}

( call main function )
#,[main]R?
Q


