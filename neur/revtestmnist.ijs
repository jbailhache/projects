echo 'Test with MNIST data'
load 'plot'
load 'bp.ijs'
echo 'Load data'
load 'labels.ijs'
load 'images.ijs'
echo 'Data loaded'

ntrain =: 8000
ntest =: 1000

NB. Train with 80 first items
outputs =: |: (ntrain {. labels) =/ i. 10
inputs =: |: (ntrain {. images) % 256

NB. Train
NB. echo 'Learning ...'
NB. brain =: learn inputs ; outputs ; (3 # 15) ; 7 ; 3000 ; 10 ; 0.00001
learning =: DefaultLearning
learning =: learning LearningInputs  inputs
learning =: learning LearningOutputs outputs
learning =: learning LearningLayers  3 # 15
learning =: learning LearningRate    8
learning =: learning LearningSteps   3000 
learning =: learning LearningError   ntrain * 0.1
NB. brain =: learn learning

NB. echo 'Saving ...'
NB. (3!:1 brain) 1!:2 < 'brain.jdata'

echo 'Load pretrained brain'
brain =: 3!:2 (1!:1 < 'brain8000.jdata')
echo 'Brain loaded'

NB. Test with training data
result =: brain apply inputs
got =: result OutputsGot learning
echo 'Errors with training data : ', ": +/ +/ 0.1 < | got - outputs

NB. Test data : items 100 - 119
outtest =: |: (ntest {. ntrain }. labels) =/ i. 10
intest =: |: (ntest {. ntrain }. images) % 256
result =: brain apply intest
got =: result OutputsGot learning
echo 'Errors with test data : ', ": +/ +/ 0.1 < | got - outtest
echo 'Expected : ', ": +/ outtest * i. 10
echo 'Got      : ', ": +/ (got = (10 # 1) */ >./ got) * i. 10
echo 'Success  : ', ": +/ (+/ outtest * i. 10 ) = +/ (got = (10 # 1) */ >./ got) * i. 10

W =: > 0 { brain
B =: > 1 { brain
nl =: > 2 { brain

ninputs =: # inputs
noutputs =: # outputs
ntotal =: # B

NB. Permutation : outputs at the beginning and inputs at the end
permute =: ((ntotal-noutputs) + i. noutputs) , (ninputs + i. ntotal-ninputs+noutputs) , (i. ninputs)

revW =: permute { permute {"1 |: W
revB =: permute { B
revnl =: nl

revbrain =: revW ; revB ; revnl

revinputs =: (i. 10) =/ i. 10
revresult =: revbrain apply revinputs
 
A =: > 1 { revresult
n =: # A
no =: ninputs
revgot =: ((no $ n-no) + i. no) { A
avg =: (+/ |: revgot) % 10

digit =: 3 : 0
 pd 'reset'
 pd 'type density'
 pd |: |. 28 28 $ y { |: revgot - avg
 pd 'show'
)

