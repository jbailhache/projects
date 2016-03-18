
import random
import math

random.seed(12)

def varscal(a):
  return a*math.exp(random.gauss(0,1))

def varvect(x,n):
  xs=[x]
  for i in range(n):
    y = []
    for a in x:
      b = varscal(a)
      y = y + [b]
    xs = xs + [y]
  return xs

def valeurs(lvpvc,sel,cours1,cours2,p):
  global cours
  global coefsrlm
  vs=[]
  i=0
  for vpvc in lvpvc:
    i=i+1
    # print vpvc
    np=len(params([]).vect())
    vp=vpvc[0:np]
    p=params(vp)
    coefsrlm=vpvc[np:len(vpvc)]
    cours=cours1
    v1=moyrlm(sel,cours1,p)[0]
    cours=cours2
    v2=moyrlm(sel,cours2,p)[0]
    if i==1:
      vs=vs+[[v1,v2,1]]
    else:
      vs=vs+[[v1,v2,0]]
  return vs

def testco():
  global cours
  global cours0, cours1, cours2
  global coefsrlm, po1, lvpvc
  cours1=[x[0:200] for x in cours0]
  cours2=[x[200:400] for x in cours0]
  cours=cours1
  p=params([])
  print 'p=', p.vect()
  testcorlm(['ALTEN'],cours1,p)
  print 'coefsrlm=', coefsrlm
  po1=optimp(['ALTEN'],cours1,p,1)
  print 'po1=',po1.vect()
  testcorlm(['ALTEN'],cours1,po1)
  print 'coefsrlm=',coefsrlm
  vpvc=po1.vect()+coefsrlm
  print 'vpvc=',vpvc
  lvpvc=varvect(vpvc,1000)
  print 'valeurs'
  lv=valeurs(lvpvc,['ALTEN'],cours1,cours2,po1)
  print 'graphe'
  graphxyz(lv,600,600)
  
def valeurs210(lvpvc,sel,cours1,cours2,cours3,p):
  global cours
  global coefsrlm
  vs=[]
  i=0
  for vpvc in lvpvc:
    i=i+1
    # print vpvc
    np=len(params([]).vect())
    vp=vpvc[0:np]
    p=params(vp)
    coefsrlm=vpvc[np:len(vpvc)]
    cours=cours1
    v1=moyrlm(sel,cours1,p)[0]
    cours=cours2
    v2=moyrlm(sel,cours2,p)[0]
    cours=cours3
    v3=moyrlm(sel,cours3,p)[0]
    if i==1:
      vs=vs+[[min(v1,v2),v3,1]]
    else:
      vs=vs+[[min(v1,v2),v3,0]]
  return vs

def testco210():
  global cours
  global cours0, cours1, cours2
  global coefsrlm, po1, lvpvc
  cours1=[x[0:200] for x in cours0]
  cours2=[x[200:400] for x in cours0]
  cours3=[x[400:600] for x in cours0]
  cours=cours1
  p=params([])
  print 'p=', p.vect()
  testcorlm(['ALTEN'],cours1,p)
  print 'coefsrlm=', coefsrlm
  po1=optimp(['ALTEN'],cours1,p,1)
  print 'po1=',po1.vect()
  testcorlm(['ALTEN'],cours1,po1)
  print 'coefsrlm=',coefsrlm
  vpvc=po1.vect()+coefsrlm
  print 'vpvc=',vpvc
  lvpvc=varvect(vpvc,1000)
  print 'valeurs'
  lv=valeurs210(lvpvc,['ALTEN'],cours1,cours2,cours3,po1)
  print 'graphe'
  graphxyz(lv,600,600)

def valeurs210sd(lvpvc,sel1,cours1,sel2,cours2,sel3,cours3,p):
  global cours
  global coefsrlm
  vs=[]
  i=0
  for vpvc in lvpvc:
    i=i+1
    # print vpvc
    np=len(params([]).vect())
    vp=vpvc[0:np]
    p=params(vp)
    coefsrlm=vpvc[np:len(vpvc)]
    cours=cours1
    v1=moyrlm(sel1,cours1,p)[0]
    cours=cours2
    v2=moyrlm(sel2,cours2,p)[0]
    cours=cours3
    v3=moyrlm(sel3,cours3,p)[0]
    if i==1:
      vs=vs+[[min(v1,v2),v3,1]]
    else:
      vs=vs+[[min(v1,v2),v3,0]]
  return vs

def testco210sd():
  global cours
  global cours0, cours1, cours2
  global coefsrlm, po1, lvpvc
  cours1=[x[0:200] for x in cours0]
  cours2=[x[200:400] for x in cours0]
  cours3=[x[400:600] for x in cours0]
  cours=cours1
  p=params([])
  print 'p=', p.vect()
  testcorlm(['ALTEN'],cours1,p)
  print 'coefsrlm=', coefsrlm
  po1=optimp(['ALTEN'],cours1,p,1)
  print 'po1=',po1.vect()
  testcorlm(['ALTEN'],cours1,po1)
  print 'coefsrlm=',coefsrlm
  vpvc=po1.vect()+coefsrlm
  print 'vpvc=',vpvc
  lvpvc=varvect(vpvc,1000)
  print 'valeurs'
  lv=valeurs210sd(lvpvc,['ALTEN'],cours1,['ILIAD'],cours2,['PPR'],cours3,po1)
  print 'graphe'
  graphxyz(lv,600,600)


def valeurs220(lvpvc,sel,cours1,cours2,cours3,cours4,p):
  global cours
  global coefsrlm
  vs=[]
  i=0
  for vpvc in lvpvc:
    i=i+1
    # print vpvc
    np=len(params([]).vect())
    vp=vpvc[0:np]
    p=params(vp)
    coefsrlm=vpvc[np:len(vpvc)]
    cours=cours1
    v1=moyrlm(sel,cours1,p)[0]
    cours=cours2
    v2=moyrlm(sel,cours2,p)[0]
    cours=cours3
    v3=moyrlm(sel,cours3,p)[0]
    cours=cours4
    v4=moyrlm(sel,cours4,p)[0]
    if i==1:
      vs=vs+[[min(v1,v2),min(v3,v4),1]]
    else:
      vs=vs+[[min(v1,v2),min(v3,v4),0]]
  return vs

def testco220():
  global cours
  global cours0, cours1, cours2
  global coefsrlm, po1, lvpvc
  cours1=[x[0:200] for x in cours0]
  cours2=[x[200:400] for x in cours0]
  cours3=[x[400:600] for x in cours0]
  cours4=[x[600:800] for x in cours0]
  cours=cours1
  p=params([])
  print 'p=', p.vect()
  testcorlm(['ALTEN'],cours1,p)
  print 'coefsrlm=', coefsrlm
  po1=optimp(['ALTEN'],cours1,p,1)
  print 'po1=',po1.vect()
  testcorlm(['ALTEN'],cours1,po1)
  print 'coefsrlm=',coefsrlm
  vpvc=po1.vect()+coefsrlm
  print 'vpvc=',vpvc
  lvpvc=varvect(vpvc,1000)
  print 'valeurs'
  lv=valeurs220(lvpvc,['ALTEN'],cours1,cours2,cours3,cours4,po1)
  print 'graphe'
  graphxyz(lv,600,600)


