echo 'Test with MNIST data'
load 'bp.ijs'
echo 'Load data'
load 'labels.ijs'
load 'images.ijs'
echo 'Data loaded'

ntrain =: 500
ntest =: 100

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
brain =: 3!:2 (1!:1 < 'brain.jdata')
echo 'Brain loaded'

W =: > 0 { brain
B =: > 1 { brain
nl =: > 2 { brain

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

ni =: # inputs
no =: # outputs
nn =: # B

NB. Random input image
ingen =: (ni,1) $ (? ni $ 256) % 256
resgeninit =: brain apply ingen
gotgeninit =: resgeninit OutputsGot learning

nstep =: 0

digit =: 7 

stepgen =: 3 : 0
 nstep =: nstep + 1
 echo nstep

 resgen =: brain apply ingen
 gotgen =: resgen OutputsGot learning
 Z =: > 0 { resgen
 A =: > 1 { resgen

 NB. Matrix of partial derivatives of outputs with respect to inputs
 D =: ({{ (sigmaprime ,Z) * W +/ . * y }} ^: (nl-2)) (sigmaprime ,Z) * W 
 D1 =: ni ({."1) ((nn-no) + i. no) { D
 
 coefs =: _1 + 2 * digit = i. 10
 var =: 784 1 $ +/ coefs * D1
 ingen =: ingen + 10 * var
)

(stepgen ^: 10) 0

resgenterm =: brain apply ingen
gotgenterm =: resgenterm OutputsGot learning

echo (0.5 < 28 28 $ , ingen) { 1 88

echo gotgenterm - gotgeninit


