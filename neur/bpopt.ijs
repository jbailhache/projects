NB. Backpropagation
NB. See https://www.miximum.fr/blog/introduction-au-deep-learning-2/

load 'stats'

sigma =: 3 : '1 % 1 + ^(-y)'
sigmaprime =: 3 : '(sigma y) * (1 - sigma y)'  NB. derivative

alpha =: 3     NB. Learning rate

NB. brain = W ; B
NB. W = > 0 { brain
NB. B = > 1 { brain

NB. Z ; A ; outputs = brain apply inputs
apply =: 4 : 0
 brain =. x
 W =. > 0 { brain               NB. Matrix of connection weights
 B =. > 1 { brain               NB. Array of biases
 inputs =. y
 n =. $ B                       NB. Total number of neurons
 npl =. 0 { $ inputs            NB. Number of neurons per layer
 nX =. 1 { $ inputs             NB. Number of inputs
 X =. inputs, ((n-npl),nX) $ 0
 maskX =. (npl#1),((n-npl)#0)   NB. Mask of inputs : only the first layer
 A =. X
 for. i. nl-1 do.
  Z =. B + W +/ . * A                     NB. Aggregation : add biases and matrix product of weights by activations
  A =. (maskX * X) + (1-maskX) * sigma Z  NB. Activation : fixed values X for input neurons, sigma applied to aggregation for others
 end.
 outputs =. ((npl $ n-npl) + i. npl) { A
 Z ; A ; outputs
)

NB. initW inputs ; outputs ; nl ; ns
initW =: 3 : 0

 inputs  =. > 0 { y
 outputs =. > 1 { y
 nl      =. > 2 { y  NB. Number of layers
 ns      =. > 3 { y

 npl =. 0 { $ inputs  NB. Number of neurons per layers
 n =. nl * npl        NB. Total number of neurons
 nX =. 1 { $ inputs   NB. Number of inputs

 NB. Masks with 1 for non-zero values
 maskW =. (<. (i. n) % npl) =/ (1 + <. (i. n) % npl)  NB. Mask of connections : each neuron is connected only to the neurons of next layer
 maskB =. (npl#0),(((nl-1)*npl)#1)                    NB. Mask of biases : no biases for input neurons
 maskX =. (npl#1),(((nl-1)*npl)#0)                    NB. Mask of inputs : only the first layer
 maskO =. (((nl-1)*npl)#0),(npl#1)                    NB. Mask of outputs : only the last layer

 X =. inputs, ((n-npl),nX) $ 0
 T =. (((n-npl),nX) $ 0), outputs

 for. i. ns do.
  W =. maskW * (n,n) $ normalrand n^2  NB. Matrix of connection weights
                                       NB. Element at i-th line and j-th column = weight of connection from neuron j to neuron i 
  B =. maskB * normalrand n            NB. biases

  ZAY =. (W;B) apply inputs
  Z =. > 0 { ZAY
  A =. > 1 { ZAY
  Y =. > 2 { ZAY
  e =. +/ +/ *: Y - outputs
  echo e
 end.

)
 
NB. brain = learn inputs ; outputs ; nl ; alpha ; ns
learn =: 3 : 0

 inputs  =. > 0 { y
 outputs =. > 1 { y
 nl      =. > 2 { y  NB. Number of layers
 alpha   =. > 3 { y  NB. Learning rate
 nls     =. > 4 { y  NB. Number of learning steps

 npl =. 0 { $ inputs  NB. Number of neurons per layers
 n =. nl * npl        NB. Total number of neurons
 nX =. 1 { $ inputs   NB. Number of inputs

 NB. Masks with 1 for non-zero values
 maskW =. (<. (i. n) % npl) =/ (1 + <. (i. n) % npl)  NB. Mask of connections : each neuron is connected only to the neurons of next layer
 maskB =. (npl#0),(((nl-1)*npl)#1)                    NB. Mask of biases : no biases for input neurons
 maskX =. (npl#1),(((nl-1)*npl)#0)                    NB. Mask of inputs : only the first layer
 maskO =. (((nl-1)*npl)#0),(npl#1)                    NB. Mask of outputs : only the last layer

 while. 0=0 do.

  W =. maskW * (n,n) $ normalrand n^2  NB. Matrix of connection weights
                                       NB. Element at i-th line and j-th column = weight of connection from neuron j to neuron i 
  B =. maskB * normalrand n            NB. biases
  X =. inputs, ((n-npl),nX) $ 0
  T =. (((n-npl),nX) $ 0), outputs
  
  s =. 0
 
  e =. 0
 
  for. i. nls do.  NB. Repeat learning
 
   ZA =. (W;B) apply inputs
   Z =. > 0 { ZA
   A =. > 1 { ZA
   Y =. > 2 { ZA
 
   e1 =. e
   e =. +/ +/ *: Y - outputs
   NB. echo s, e
   if. 0.000001 > | e - e1 do. break. end.
   NB. echo 'expected :'
   NB. echo outputs
   NB. echo 'got :'
   NB. echo Y
   NB. echo 'difference :'
   NB. echo Y - outputs
   NB. echo 'squares :'
   NB. echo *: Y - outputs
   NB. echo ' '
 
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
 
  if. e < 0.001 do. break. end.

 end.

 W ; B
)


NB. Test with random inputs and expected outputs
p =: 10
nl =: 5        NB. Number of layers
inputs =: (? (6,3) $ p) % p
outputs =: (? (6,3) $ p) % p

NB. initW inputs ; outputs ; 5 ; 30

brain =: learn inputs ; outputs ; nl ; 16 ; 3000

testalpha =: 3 : 0
 alpha =. 1
 for. i. 30 do. 
  brain =: learn inputs ; outputs ; nl ; alpha ; 800
  alpha =. alpha + 1
 end.
)

echo ' '
NB. testalpha 0

testnl =: 3 : 0
 nl =. 3
 for. i. 8 do. 
  brain =: learn inputs ; outputs ; nl ; 20 ; 800
  nl =. nl + 1
 end.
)

NB. testnl 0

echo ' '
echo 'Test with random inputs and expected outputs :'
NB. echo (> 2 { brain apply inputs) - outputs
result =: brain apply inputs
echo 'Expected :'
echo outputs
echo 'Got :'
echo > 2 { result
echo 'Errors :'
echo (> 2 { result) - outputs

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
0 0 0 gives 0 0 0
0 1 0 gives 0 0 0
1 0 0 gives 0 0 0
1 1 0 gives 1 1 1

NB. brain =: learn inputs ; outputs ; 5 ; 20 ; 4000
brain =: learn inputs ; outputs ; 5 ; 16 ; 3000
echo ' '
NB. echo 'Test with logical and : Errors ='
NB. echo (> 2 { brain apply inputs) - outputs
echo 'Test with logical and :'
result =: brain apply inputs
echo 'Expected :'
echo outputs
echo 'Got :'
echo > 2 { result
echo 'Errors :'
echo (> 2 { result) - outputs

init 0
0 0 1 gives 0 0 0
0 1 1 gives 0 0 0
1 0 1 gives 0 0 0
1 1 1 gives 0 0 0

echo ' '
echo 'Test with logical and : outputs ='
echo (> 2 { brain apply inputs)
echo ' '

