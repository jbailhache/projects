
execfile('load.py')
cours=lirecourslf(lnfh)
# execfile('indics.py')
# execfile('select.py')
# execfile('rlm.py')
# execfile('optim.py')
execfile('indicsn.py')
execfile('rlmn.py')
p=params([],[])
execfile('coefsrlmb1.py')
t1=40
# print moyrlm(sel3,cours,p)
c3=courslval(cours,sel3)
po1=optimp(c3,p,3)
print po1.vect()
vpco=optimpc(c3,po1,4)
print vpco
# po=params(vpco[0])
# coefsrlm=vpco[1]
po = params(vpco[0], vpco[1])






