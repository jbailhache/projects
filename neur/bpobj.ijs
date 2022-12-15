
NB. brain = learn inputs ; outputs ; nnl ; alpha ; nls ; er ; de

DefaultLearning =: (0 0 $ 0) ; (0 0 $ 0) ; (0 # 0) ; 1 ; 1 ; 1 ; 0.000001
LearningInputs    =: (3 : '> 0 { y') : (4 : '(< y) 0 } x')
LearningOutputs   =: (3 : '> 1 { y') : (4 : '(< y) 1 } x')
LearningLayers    =: (3 : '> 2 { y') : (4 : '(< y) 2 } x')
LearningRate      =: (3 : '> 3 { y') : (4 : '(< y) 3 } x')
LearningSteps     =: (3 : '> 4 { y') : (4 : '(< y) 4 } x')
LearningError     =: (3 : '> 5 { y') : (4 : '(< y) 5 } x')
LearningVariation =: (3 : '> 6 { y') : (4 : '(< y) 6 } x')


NB. OuptutsGot result ; learning
OutputsGot =: 4 : 0
 result =. x
 learning =. y
 A =. > 1 { result
 outputs =. LearningOutputs learning
 n =. # A
 no =. # outputs
 got =. ((no $ n-no) + i. no) { A
 got
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
 NB. brain =: learn inputs LearningInput outputs LearningOutput (3 # 3) LearningLayers 16 LearningRate 3000 LearningSteps 0.001 LearningError DefaultLearning
 learning =: DefaultLearning
 learning =: learning LearningInputs inputs
 learning =: learning LearningOutputs outputs
 learning =: learning LearningLayers (3 # 3)
 learning =: learning LearningRate 16 
 learning =: learning LearningSteps 3000 
 learning =: learning LearningError 0.001 
 brain =: learn learning
 NB. brain =: learn inputs ; outputs ; (3 # 3) ; 16 ; 3000 ; 0.1 ; 0.000001
 echo ' '
 echo 'Test with logical and :'
 result =: brain apply inputs
 NB. A =: > 1 { result
 NB. n =: # A
 NB. npl =: # outputs  NB. number of output neurons
 NB. got =. ((npl $ n-npl) + i. npl) { A
 got =: result OutputsGot learning
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
