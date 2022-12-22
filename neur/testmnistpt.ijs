echo 'Test with MNIST data'
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

