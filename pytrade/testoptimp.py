
execfile('load.py')
cours=lirecourslf(lnfh)
execfile('indics.py')
execfile('select.py')
execfile('rlm.py')
execfile('optim.py')
p=params([])
execfile('coefsrlmb1.py')
t1=40
print moyrlm(sel3,cours,p)
po1=optimp(sel3,cours,p,3)
print po1.vect()
vpco=optimpc(sel3,cours,po1,4)
print vpco
po=params(vpco[0])
coefsrlm=vpco[1]





