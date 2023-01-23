echo 'Test with MNIST data'
load 'bp.ijs'
echo 'Load data'
load 'labels.ijs'
load 'images.ijs'
echo 'Data loaded'

ntrain =: 2000
ntest =: 100

nrtrain =: 200
nrtest =: 10

NB. Train with 80 first items
outputs =: |: (ntrain {. labels) =/ i. 10
inputs =: |: (ntrain {. images) % 256

outputs =: (outputs,0) ,. ((10#0),1) */ nrtrain#1
inputs =: inputs ,. (? ((#inputs),nrtrain) $ 256) % 256

NB. Train
NB. echo 'Learning ...'
NB. brain =: learn inputs ; outputs ; (3 # 15) ; 7 ; 3000 ; 10 ; 0.00001
learning =: DefaultLearning
learning =: learning LearningInputs  inputs
learning =: learning LearningOutputs outputs
learning =: learning LearningLayers  3 # 15
learning =: learning LearningRate    8
learning =: learning LearningSteps   3000 
learning =: learning LearningError   (ntrain+nrtrain) * 0.1
NB. brain =: learn learning

NB. echo 'Saving ...'
NB. (3!:1 brain) 1!:2 < 'brainrnd.jdata'

echo 'Load pretrained brain'
brain =: 3!:2 (1!:1 < 'brainrnd.jdata')
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

outtest =: (outtest,0) ,. ((10#0),1) */ nrtest#1
intest =: intest ,. (? ((#intest),nrtest) $ 256) % 256

result =: brain apply intest
got =: result OutputsGot learning
echo 'Errors with test data : ', ": +/ +/ 0.1 < | got - outtest
echo 'Expected : ', ": +/ outtest * i. 11
echo 'Got      : ', ": +/ (got = (11 # 1) */ >./ got) * i. 11
echo 'Success  : ', ": +/ (+/ outtest * i. 11 ) = +/ (got = (11 # 1) */ >./ got) * i. 11

ni =: # inputs
no =: # outputs
nn =: # B

NB. Random input image
ingen =: (ni,1) $ (? ni $ 256) % 256
resgeninit =: brain apply ingen
gotgeninit =: resgeninit OutputsGot learning

nstep =: 0
digit =: 7
rate =: 1
b =: _1
a =: 2

NB. Computation of the partial derivatives of outputs with respect to inputs
NB. Example with one input larer (i), 3 intermediate layers (j,k,l) and ono output layer (m)
NB. Notation : Sl = sum over l
NB. dam/dai = dam/dzm dzm/dai = s'(zm) dzm/dai
NB. dzm/dai = Sl dzm/dal dal/dai = Sl wml dal/dai
NB. dam/dai = s'(zm) Sl wml dal/dai
NB. dal/dai = dal/dzl dzl/dai = s'(zl) dzl/dai
NB. dzl/dai = Sk dzl/dak dak/dai = Sk wlk dak/dai
NB. dal/dai = s'(zl) Sk wlk dak/dai
NB. dam/dai = s'(zm) Sl wml s'(zl) Sk wlk dak/dai
NB. dak/dai = dak/dzk dzk/dai = s'(zk) dzk/dai
NB. dzk/dai = Sj dzk/daj daj/dai = Sj wkj daj/dai
NB. dak/dai = s'(zk) Sj wkj daj/dai
NB. dam/dai = s'(zm) Sl wml s'(zl) Sk wlk s'(zk) Sj wkj daj/dai
NB. daj/dai = daj/dzj dzj/dai = s'(zj) dzj/dai
NB. dzj/dai = wji
NB. daj/dai = s'(zj) wji
NB. dam/dai = s'(zm) Sl wml s'(zl) Sk wlk s'(zk) Sj wkj s'(zj) wji
NB. Matrix of dam/dai = (sigmaprime ,Z) * W +/ . * (sigmaprime ,Z) * W +/ . * (sigmaprime ,Z) * W +/ . * (sigmaprime ,Z) * W 
NB.                   = ({{ (sigmaprime ,Z) * W +/ . * y }} ^: 3) (sigmaprime ,Z) * W 

NB. Check for pixel p if calculated and experiemental gradients are almost the same

p =: 12 

NB. Calculated gradient
resgen =: brain apply ingen
gotgen =: resgen OutputsGot learning
Z =: > 0 { resgen
D =: ({{ (sigmaprime ,Z) * W +/ . * y }} ^: (nl-2)) (sigmaprime ,Z) * W
D1 =: ni ({."1) ((nn-no) + i. no) { D
calc =: 11 1 $ p {"1 D1  NB. Calculated gradient

epsilon =: 0.001

NB. Experimental gradient
NB. ingen gp p = gradient for pixel p
gp =: 4 : 0
 in =. x
 p =. y
 res =. brain apply in
 got =. res OutputsGot learning
 in1 =. (ni,1) $ (,in) + epsilon * p = i. ni
 res1 =. brain apply in1
 got1 =. res1 OutputsGot learning
 (1 % epsilon) * got1 - got
)

exp =: ingen gp p    NB. Experimental gradient

echo 'Difference between calculated and experimantal gradient'
echo calc - exp      NB. Difference

NB. stepgen =: 3 : 0
loopgen =: 3 : 0
for. i. y do.
 nstep =: nstep + 1
 NB. echo nstep

 resgen =: brain apply ingen
 gotgen =: resgen OutputsGot learning
 value =: +/ (,gotgen) * b + a * digit = i. 11
 NB. echo 'Step ', (": nstep), ': value = ', (": value)

 ringen =: (ni,1) $ (? ni $ 256) % 256
 rresgen =: brain apply ringen
 rgotgen =: rresgen OutputsGot learning
 rvalue =: +/ (,rgotgen) * b + a * digit = i. 11
 NB. echo 'Step ', (": nstep), ' : value = ', (": value), ' ; rvalue = ', (": rvalue)
 if. rvalue > value do.
  ingen =: ringen
  resgen =: rresgen
  gotgen =: rgotgen
  value =: rvalue
 end.
 
 Z =: > 0 { resgen
 A =: > 1 { resgen

 NB. Matrix of partial derivatives of outputs with respect to inputs
 D =: ({{ (sigmaprime ,Z) * W +/ . * y }} ^: (nl-2)) (sigmaprime ,Z) * W 
 D1 =: ni ({."1) ((nn-no) + i. no) { D
 
 coefs =: b + a * digit = i. 11
 var =: 784 1 $ +/ coefs * D1
 ningen =: ingen + rate * var

 nresgen =: brain apply ningen
 ngotgen =: nresgen OutputsGot learning
 nvalue =: +/ (,ngotgen) * b + a * digit = i. 11
 echo 'Step ', (": nstep), ' : rate = ', (": rate),  ' ; value = ', (": value), ' ; rvalue = ', (": rvalue), ' ; nvalue = ',  (": nvalue)
 
 if. nvalue > value do.
  ingen =: ningen
  rate =: rate * 2
 else.
  rate =: rate % 2
 end.
 
end.
)

echo 'rate = ', ": rate
echo 'digit = ', ": digit

NB. (stepgen ^: 20) 0
loopgen 20

resgenterm =: brain apply ingen
gotgenterm =: resgenterm OutputsGot learning

echo 'Difference between final and initial outputs'
echo gotgenterm - gotgeninit
echo ' '
echo 'Final outputs'
echo gotgenterm
termvalue =: +/ (,gotgenterm) * b + a * digit = i. 11
echo 'Final value : ', (": termvalue)
echo ' '
echo (0.7 < 28 28 $ , ingen) { 1 88

(3!:1 ingen) 1!:2 < 'digit.jdata'
