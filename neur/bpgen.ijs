NB. Backpropagation
NB. See https://www.miximum.fr/blog/introduction-au-deep-learning-2/

load 'stats'

sigma =: 3 : '1 % 1 + ^(-y)'
sigmaprime =: 3 : '(sigma y) * (1 - sigma y)'  NB. derivative

alpha =: 3     NB. Learning rate

NB. brain = W ; B
NB. W = > 0 { brain
NB. B = > 1 { brain

NB. Z ; A = brain apply inputs
apply =: 4 : 0
 brain =. x
 W =. > 0 { brain               NB. Matrix of connection weights
 B =. > 1 { brain               NB. Array of biases
 inputs =. y
 n =. $ B                       NB. Total number of neurons
 npl =. 0 { $ inputs            NB. Number of neurons of input layer
 nX =. 1 { $ inputs             NB. Number of inputs
 X =. inputs, ((n-npl),nX) $ 0
 maskX =. (npl#1),((n-npl)#0)   NB. Mask of inputs : only the first layer
 A =. X
 for. i. nl-1 do.
  Z =. B + W +/ . * A                     NB. Aggregation : add biases and matrix product of weights by activations
  A =. (maskX * X) + (1-maskX) * sigma Z  NB. Activation : fixed values X for input neurons, sigma applied to aggregation for others
 end.
 NB. outputs =. ((npl $ n-npl) + i. npl) { A
 Z ; A  NB. ; outputs
)
 
NB. brain = learn inputs ; outputs ; nnl ; alpha ; ns
learn =: 3 : 0

 inputs  =. > 0 { y
 outputs =. > 1 { y
 nnl     =. > 2 { y  NB. Number of neurons in the layers
 NB. npl =. > 3 { y  NB. Number of neurons per intermediate layer
 alpha   =. > 3 { y  NB. Learning rate
 nls     =. > 4 { y  NB. Number of learning steps
 
 NB. npl =. 0 { $ inputs  NB. Number of neurons per layers
 ni =. # inputs
 no =. # outputs
 NB. n =. nl * npl        NB. Total number of neurons
 NB. nil =. nl - 2
 nl =. # nnl
 nil =. +/nnl
 NB. n =. ni + no + nil * npl
 nil =. # nnl
 nl =. nil + 2
 n =. ni + no + +/nnl
 nX =. 1 { $ inputs   NB. Number of inputs

 NB. Masks with 1 for non-zero values
 NB. maskW =. (<. (i. n) % npl) =/ (1 + <. (i. n) % npl)  NB. Mask of connections : each neuron is connected only to the neurons of next layer
 NB. ln =. (ni # 0) , (1 + <.(i. nil*npl) % npl), (no # nil+1)  NB. Layer number of each neuron
 ln =. (ni # 0) , (nnl # 1 + i. nil) , (no # nil+1)
 maskW =. ln =/ 1 + ln
 NB. maskB =. (npl#0),(((nl-1)*npl)#1)                    NB. Mask of biases : no biases for input neurons
 NB. maskX =. (npl#1),(((nl-1)*npl)#0)                    NB. Mask of inputs : only the first layer
 NB. maskO =. (((nl-1)*npl)#0),(npl#1)                    NB. Mask of outputs : only the last layer
 maskB =. (ni#0),(n-ni)#1
 maskX =. (ni#1),(n-ni)#0
 maskO =. ((n-no)#0),no#1

 while. 0=0 do.  NB. Loop while error is too big

  W =. maskW * (n,n) $ normalrand n^2  NB. Matrix of connection weights
                                       NB. Element at i-th line and j-th column = weight of connection from neuron j to neuron i 
  B =. maskB * normalrand n            NB. biases
  X =. inputs, ((n-ni),nX) $ 0
  T =. (((n-no),nX) $ 0), outputs
  
  s =. 0
  e =. 0
 
  for. i. nls do.  NB. Repeat learning
 
   ZA =. (W;B) apply inputs
   Z =. > 0 { ZA
   A =. > 1 { ZA
   NB. Y =. > 2 { ZA
   Y =. ((no $ n-no) + i. no) { A
 
   e1 =. e
   e =. +/ +/ *: Y - outputs
   NB. echo s, e
   if. 0.000001 > | e - e1 do. break. end.
 
   NB. A =. (((n-npl),nX) $ 0), out
   delta =. (n,nX) $ 0
   for. i. nl do.  NB. Repeat backpropagation nl times
    NB. One step of backpropagation
    NB. delta^L_i = sigma'(z^l_i) * (A - T)
    NB. delta^l_i = sigma'(z^l_i) * sum_j(w^{l+1}_{ji} delta^{l+1}_j
    delta =. (sigmaprime Z) * (maskO * A - T) + (|: W) +/ . * delta
   end.
 
   avgdelta =. (+/ |: delta) % nX  NB. Average delta
   NB. Average gradient of weights for nX inputs
   NB. dC/dw^l_{ij} = a^{l-1}_j delta^l_i
   GW =. maskW * delta +/ . * |: A % nX 
   NB. Average gradient of biases for nX inputs
   NB. dC/db_i = delta^l_i
   GB =. maskB * avgdelta
   NB. Modifiy weights and biases
   W =. W - alpha * GW
   B =. B - alpha * GB
 
   s =. s+1
 
  end.
 
  echo ' '
  echo nl, alpha, e
 
  if. e < 0.001 do. break. end.  NB. Stop if error is small enough

 end.

 W ; B
)


NB. Test with random inputs and expected outputs
p =: 10
nl =: 5        NB. Number of layers
inputs =: (? (8,3) $ p) % p
outputs =: (? (5,3) $ p) % p

brain =: learn inputs ; outputs ; ((nl-2) # 4) ; 16 ; 3000

echo ' '
echo 'Test with random inputs and expected outputs :'
NB. echo (> 2 { brain apply inputs) - outputs
result =: brain apply inputs
A =: > 1 { result
n =: # A
npl =: # outputs  NB. number of output neurons
got =. ((npl $ n-npl) + i. npl) { A
echo 'Expected :'
echo outputs
echo 'Got :'
NB. echo > 2 { result
echo got
echo 'Errors :'
NB. echo (> 2 { result) - outputs
echo got - outputs

NB. initialisation of inputs and expected outputs

init =: 3 : 0
 inputs =: 0 0 $ 0
 outputs =: 0 0 $ 0
)

gives =: 4 : 0
 inputs =: |: (|: inputs) , (1,$x) $ x
 outputs =: |: (|: outputs) , (1,$y) $ y
)


NB. Test with logical and
NB. a b c -> d d d where d = a and b
NB. c is not significant
NB. learn with c = 0
NB. test with c = 1

init 0
0 0 0 gives 0 
0 1 0 gives 0 
1 0 0 gives 0 
1 1 0 gives 1 

NB. brain =: learn inputs ; outputs ; 5 ; 20 ; 4000
brain =: learn inputs ; outputs ; (3 # 3) ; 16 ; 3000
echo ' '
NB. echo 'Test with logical and : Errors ='
NB. echo (> 2 { brain apply inputs) - outputs
echo 'Test with logical and :'
result =: brain apply inputs
A =: > 1 { result
n =: # A
npl =: # outputs  NB. number of output neurons
got =. ((npl $ n-npl) + i. npl) { A
echo 'Expected :'
echo outputs
echo 'Got :'
NB. echo > 2 { result
echo got
echo 'Errors :'
NB. echo (> 2 { result) - outputs
echo got - outputs

init 0
0 0 1 gives 0 
0 1 1 gives 0 
1 0 1 gives 0 
1 1 1 gives 0 

echo ' '
echo 'Test with logical and : outputs ='
NB. echo (> 2 { brain apply inputs)
echo (> 1 { brain apply inputs)
echo ' '

