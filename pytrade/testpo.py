
def minindc(cours,ind,p):
  m = 100000000.0
  m2 = 100000000.0
  # lv=titrescours(cours)
  #for val in lv:
  #  cv = coursval (cours, val)
  for cv in cours:
    k = ind (cv, p)
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    m = min (m, k)
    m2 = min (m2, k2)
    # print str(k) + '\t' + str(k2) + '\t' + val
  return [m,m2]

def mmmindc(cours,ind,p):
  mo=moyindc(cours,ind,p)
  mi=minindc(cours,ind,p)
  return [(mo[0]+mo[1])/2.0,(mi[0]+mi[1])/2.0]

combindc = minindc

def combrlm(cours,p):
  return combindc (cours, repetegsc, [init_indics, etape_indics, graphe_indics, p])

def paramoptc(c,n1,n2):
  p=params([],[])
  po1=optimp(c,p,n1)
  vpco=optimpc(c,po1,n2)
  po=params(vpco[0],vpco[1])
  return po

lt = [0,200,400,600]

def test1(cours,lt,n1,n2):
  s=0
  for cv in cours:
    c=[]
    for i in range(len(lt)-2):
      c=c+[cv[lt[i]:lt[i+1]]]
    po=paramoptc(c,n1,n2)
    ct=[cv[lt[len(lt)-2]:lt[len(lt)-1]]]
    r=moyrlm(ct,po)
    s=s+r[0]
  return s/float(len(cours))

def test2(cours1,cours2,n1,n2):
  po=paramoptc(cours1,n1,n2)
  r=moyrlm(cours2,po)
  return r

def test3(cours,n1,n2):
  s0=0
  s1=0
  for i in range(len(cours)):
    cours1 = cours[0:i]+cours[i+1:len(cours)]
    cours2=[cours[i]]
    print len(cours1), len(cours2)
    r=test2(cours1,cours2,n1,n2)
    s0=s0+r[0]
    s1=s1+r[1]
  return [s0/len(cours),s1/len(cours)]

def test4(cours,n1,n2):
  global combindc
  combindc = moyindc
  rmoy = test3(cours,n1,n2)
  combindc = minindc
  rmin = test3(cours,n1,n2)
  combindc = mmmindc
  rmmm = test3(cours,n1,n2)
  return [rmoy,rmin,rmmm]


