echo 'Test with MNIST data'
load 'bptransp.ijs'
echo 'Load data'
load 'labels.ijs'
load 'images.ijs'
echo 'Data loaded'

ntrain =: 100
ntest =: 100

NB. Train with 80 first items
NB. outputs =: |: (ntrain {. labels) =/ i. 10
outputs =: (ntrain {. labels) =/ i. 10
NB. inputs =: |: (ntrain {. images) % 256
inputs =: (ntrain {. images) % 256

NB. Train
echo 'Learning ...'
brain =: learn inputs ; outputs ; (3 # 15) ; 7 ; 3000 ; 10 ; 0.00001
echo 'Saving ...'
(3!:1 brain) 1!:2 < 'braintransp.jdata'

NB. Load pretrained brain
NB. brain =: 3!:2 (1!:1 < 'braintransp.jdata')

NB. Test with training data
result =: brain apply inputs
A =: > 1 { result
NB. n =: # A
n =: 1 { $ A
NB. npl =: # outputs
npl =: 1 { $ outputs  NB. number of output neurons
NB. got =. ((npl $ n-npl) + i. npl) { A
got =. ((npl $ n-npl) + i. npl) {"1 A
echo 'Errors with training data : ', ": +/ +/ 0.1 < | got - outputs

NB. Test data : items 100 - 119
NB. outtest =: |: (ntest {. ntrain }. labels) =/ i. 10
outtest =: (ntest {. ntrain }. labels) =/ i. 10
NB. intest =: |: (ntest {. ntrain }. images) % 256
intest =: (ntest {. ntrain }. images) % 256
result =: brain apply intest
A =: > 1 { result
# n =: # A
n =: 1 { $ A
# npl =: # outtest
npl =: 1 { $ outtest
NB. got =. ((npl $ n-npl) + i. npl) { A
got =. ((npl $ n-npl) + i. npl) {"1 A
echo 'Errors with test data : ', ": +/ +/ 0.1 < | got - outtest
NB. echo 'Expected : ', ": +/ outtest * i. 10
echo 'Expected : ', ": +/"1 outtest *"1 i. 10
NB. echo 'Got      : ', ": +/ (got = (10 # 1) */ >./ got) * i. 10
echo 'Got      : ', ": +/"1 (got = (>./"1 got) */ 10 # 1) *"1 i. 10
NB. echo 'Success  : ', ": +/ (+/ outtest * i. 10 ) = +/ (got = (10 # 1) */ >./ got) * i. 10
echo 'Success  : ', ": +/ (+/"1 outtest *"1 i. 10) = +/"1 (got = (>./"1 got) */ 10 # 1) *"1 i. 10

