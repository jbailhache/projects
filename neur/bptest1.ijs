
init 0
0 0 0 gives 0 0 0
0 1 0 gives 0 0 0
1 0 0 gives 0 0 0
1 1 0 gives 1 1 1
term 0

brain =: learn inputs ; outputs ; 5
echo 'Test1 : Errors :'
echo (> 2 { brain apply inputs) - outputs

init 0
0 0 1 gives 0 0 0
0 1 1 gives 0 0 0
1 0 1 gives 0 0 0
1 1 1 gives 0 0 0
term 0

echo 'Test1 : new outputs :'
echo (> 2 { brain apply inputs)
