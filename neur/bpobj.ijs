
NB. brain = learn inputs ; outputs ; nnl ; alpha ; nls ; er ; de

DefaultLearning =: (0 0 $ 0) ; (0 0 $ 0) ; (0 # 0) ; 1 ; 1 ; 1 ; 0.000001

LearningInput =: 3 : 0
 > 0 { y
:
 (< x) 0 } y
)

LearningOutput =: 3 : 0
 > 1 { y
:
 (< x) 1 } y
)

LearningLayers =: 3 : 0
 > 2 { y
:
 (< x) 2 } y
)

LearningRate =: 3 : 0
 > 3 { y
:
 (< x) 3 } y
)

LearningSteps =: 3 : 0
 > 4 { y
:
 (< x) 4 } y
)

LearningError =: 3 : 0
 > 5 { y
:
 (< x) 5 } y
)

LearningVariation =: 3 : 0
 > 6 { y
:
 (< x) 6 } y
)

NB. Test with logical and
NB. a b c -> d d d where d = a and b
NB. c is not significant
NB. learn with c = 0
NB. test with c = 1

testand =: 3 : 0

 init 0
 0 0 0 gives 0 
 0 1 0 gives 0 
 1 0 0 gives 0 
 1 1 0 gives 1 
 
 NB. brain =: learn inputs ; outputs ; (3 # 3) ; 16 ; 3000 ; 0.001 ; 0.000001
 brain =: learn inputs LearningInput outputs LearningOutput (3 # 3) LearningLayers 16 LearningRate 3000 LearningSteps 0.001 LearningError DefaultLearning
 NB. brain =: learn inputs ; outputs ; (3 # 3) ; 16 ; 3000 ; 0.1 ; 0.000001
 echo ' '
 echo 'Test with logical and :'
 result =: brain apply inputs
 A =: > 1 { result
 n =: # A
 npl =: # outputs  NB. number of output neurons
 got =. ((npl $ n-npl) + i. npl) { A
 echo 'Expected :'
 echo outputs
 echo 'Got :'
 echo got
 echo 'Errors :'
 echo got - outputs
 
 init 0
 0 0 1 gives 0 
 0 1 1 gives 0 
 1 0 1 gives 0 
 1 1 1 gives 0 
 
 echo ' '
 echo 'Test with logical and : outputs ='
 echo (> 1 { brain apply inputs)
 echo ' '
)
