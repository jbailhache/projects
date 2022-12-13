echo 'Test with MNIST data'
load 'bp.ijs'
echo 'Load data'
load 'labels.ijs'
load 'images.ijs'
echo 'Data loaded'

ntrain =: 100
ntest =: 100

NB. Train with 80 first items
outputs =: |: (ntrain {. labels) =/ i. 10
inputs =: |: (ntrain {. images) % 256

NB. Train
echo 'Learning ...'
brain =: learn inputs ; outputs ; (3 # 15) ; 7 ; 3000 ; 10 ; 0.00001
echo 'Saving ...'
(3!:1 brain) 1!:2 < 'newbrain.jdata'

NB. Load pretrained brain
NB. brain =: 3!:2 (1!:1 < 'brain.jdata')

NB. Test with training data
result =: brain apply inputs
A =: > 1 { result
n =: # A
npl =: # outputs
got =. ((npl $ n-npl) + i. npl) { A
echo 'Errors with training data : ', ": +/ +/ 0.1 < | got - outputs

NB. Test data : items 100 - 119
outtest =: |: (ntest {. ntrain }. labels) =/ i. 10
intest =: |: (ntest {. ntrain }. images) % 256
result =: brain apply intest
A =: > 1 { result
n =: # A
npl =: # outtest
got =. ((npl $ n-npl) + i. npl) { A
echo 'Errors with test data : ', ": +/ +/ 0.1 < | got - outtest
echo 'Expected : ', ": +/ outtest * i. 10
echo 'Got      : ', ": +/ (got = (10 # 1) */ >./ got) * i. 10
echo 'Success  : ', ": +/ (+/ outtest * i. 10 ) = +/ (got = (10 # 1) */ >./ got) * i. 10

