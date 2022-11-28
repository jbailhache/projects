NB. initialisation of inputs and expected outputs

init =: 3 : 0
 inputs =: 0 0 $ 0
 outputs =: 0 0 $ 0
)

gives =: 4 : 0
 inputs =: |: (|: inputs) , (1,$x) $ x
 outputs =: |: (|: outputs) , (1,$y) $ y
)

