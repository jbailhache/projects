
def lfc(nf):
  lcs=lirecours1(nf)[0]
  n=len(lcs)
  return lcs

wd=900
hg=600

def mme(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  s = 0
  for cs in lcs:
    c = cs[6]
    m = a * c + (1-a) * m
    s = c - m
    if s<0:
      acte = -nt
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0]]
  print k
  courbes(d,['black','red','green','blue'],wd,hg,' ')
  return k

def mme2(lcs,p,p2):
  a = 2 / float(p+1)
  a2 = 2 / float (p2+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = c0
  m2 = c0
  s = 0
  for cs in lcs:
    c = cs[6]
    m = a * c + (1-a) * m
    m2 = a2 * c + (1-a2) * m2 
    s = m - m2
    if s<0:
      acte = -nt
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,m/c0,m2/c0,nt*c0/l0*0.2+0.2,k/l0]]
  print k
  courbes(d,['black','red','yellow','green','blue'],wd,hg,' ')
  return k

def macd(lcs,p,p2,p3):
  a = 2 / float(p+1)
  a2 = 2 / float (p2+1)
  a3 = 2 / float(p3+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = c0
  m2 = c0
  ld = c0
  s = 0
  for cs in lcs:
    c = cs[6]
    m = a * c + (1-a) * m
    m2 = a2 * c + (1-a2) * m2 
    macd = m - m2
    ld = a3 * macd + (1-a3) * ld
    s = macd - ld
    if s<0:
      acte = -nt
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,m/c0,m2/c0,nt*c0/l0*0.2+0.2,k/l0]]
  print k
  courbes(d,['black','red','yellow','green','blue'],wd,hg,' ')
  return k

def mme3(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  mp = m
  s = 0
  for cs in lcs:
    c = cs[6]
    mp = m
    m = a * c + (1-a) * m
    s = m - mp
    if s<0:
      acte = -nt
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0]]
  print k
  courbes(d,['black','red','green','blue'],wd,hg,' ')
  return k

def calculind(lcs,mi,mt):
  c0=lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  x = [lcs[0][i+3] for i in range(5)]
  q = prodmat (mi, [1] + x)
  print q
  for cs in lcs:
    c = cs[6]
    x = [cs[i+3] for i in range(5)]
    q = prodmat (mt, q+x)
    if q[0]>0 and q[1]<0:
      acte = int (l/float(c))
    elif q[0]<0 and q[1]>0:
      acte = -nt
    else:
      acte = 0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    d = d + [[c/c0,q[2]/c0,nt*c0/l0*0.2+0.2,k/l0]]
  print k
  courbes(d,['black','red','green','blue'],wd,hg,' ')
  return k

mimme = [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0]]
mimme2 = [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]

p = 25
a = 2 / float(p+1)
def mtmme(p):
  a = 2 / float(p+1)
  return [[0, 0, a-1, 0, 0, 0, 1-a, 0], [0, 0, 1-a, 0, 0, 0, a-1, 0], [0, 0, 1-a, 0, 0, 0, a, 0]]

mimacd = [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,1,0], [0,0,0,0,1,0], [0,0,0,0,1,0]]

def mtmacd(p1,p2,p3):
  a1 = 2/float(p1+1)
  a2 = 2/float(p2+1)
  a3 = 2/float(p3+1)
  mt =  [[0, 0, (1-a1)*(1-a3), (a2-1)*(1-a3), a3-1, 0, 0, 0, (a1-a2)*(1-a3), 0]]
  mt=mt+[[0, 0, (a1-1)*(1-a3), (1-a2)*(1-a3), 1-a3, 0, 0, 0, (a2-a1)*(1-a3), 0]]
  mt=mt+[[0, 0, 1-a1,          0,             0,    0, 0, 0, a1,             0]]
  mt=mt+[[0, 0, 0,             1-a2,          0,    0, 0, 0, a2,             0]]
  mt=mt+[[0, 0, (1-a1)*a3,     (a2-1)*a3,     1-a3, 0, 0, 0, (a1-a2)*a3,     0]]
  return mt

mimacds = mimacd + [[0,0,0,0,1,0]]

def mtmacds(p1,p2,p3):
  a1 = 2/float(p1+1)
  a2 = 2/float(p2+1)
  a3 = 2/float(p3+1)
  mt =  [[0, 0, 0   , 0   , 1   , -1  , 0, 0, 0, 0   , 0]]
  mt=mt+[[0, 0, 0   , 0   , -1  , 1   , 0, 0, 0, 0   , 0]]
  mt=mt+[[0, 0, 1-a1, 0   , 0   , 0   , 0, 0, 0, a1  , 0]]
  mt=mt+[[0, 0, 0   , 1-a2, 0   , 0   , 0, 0, 0, a2  , 0]]
  mt=mt+[[0, 0, 1   , -1  , 0   , 0   , 0, 0, 0, 0   , 0]]
  mt=mt+[[0, 0, 0   , 0   , a3  , 1-a3, 0, 0, 0, 0   , 0]]
  return mt


  

  



      