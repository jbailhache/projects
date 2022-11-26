NB. initialisation of inputs and expeeted outputs

init =: 3 : 0
 tinputs =: 0 0 $ 0
 toutputs =: 0 0 $ 0
)

gives =: 4 : 0
 tinputs =: tinputs , (1,$x) $ x
 toutputs =: toutputs , (1,$y) $ y
)

term =: 3 : 0
 inputs =: |: tinputs
 outputs =: |: toutputs
)
