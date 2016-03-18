
execfile('indics.py')
execfile('rlm.py')
execfile('select.py')
execfile('optim.py')
p=params([])
t1=40
p.srlm=0.012
# testcorlm(sel4,cours,p)
execfile('coefsrlm4.py')
lp=[sel3,cours,p]
print moyrlmc(lp,coefsrlm)
# v1=optim(moyrlmc,lp,coefsrlm)
