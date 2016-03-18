
nq = 9
ny = 7
ne = 2
sizemt = nq * (nq + ny)
nd = nq + ne * sizemt

def qilmt(x):
  if len(x) != nd:
    print '*** erreur : len(x)=', len(x), ' x=', x
  qi = [x[i] for i in range(nq)]
  lmt = [[[x[nq+e*sizemt+i*(nq+ny)+j] for j in range(nq+ny)] for i in range(nq)] for e in range(ne)]
  return [qi,lmt]

def f(q):
  if q[3] == 0:
    r1 = 0
  else:
    r1 = q[2]/q[3]
  if q[4]<q[5]:
    r2 = q[0]
  else:
    r2 = q[7]
  return [r1, r2]

def calculind3(lcs,p):
  qi=p[0]
  lmt=p[1]
  # if len(lcs)<=0 or len(lcs[0])<=6:
  #   return [0,[]]
  # print ' len(lcs)=', len(lcs), ' lcs[0]=', lcs[0]
  # print 'lcs=',lcs
  c0=lcs[0][6]
  l = l0
  nt = 0
  d = []
  q = qi
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    # x = [cs[6] / float(c0)]
    x = [cs[i] /float(c0) for i in [3,4,5,6]]
    for e in range(len(lmt)):
      r = f(q) 
      q = prodmat (lmt[e], q+x+[1]+r)
    sa=q[0]
    sv=q[1]
    if sa<0 and sv>0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif sa>0 and sv<0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    if acte > 0:
      l = l - fraisa
    if acte < 0:
      l = l - fraisv
    k = l + nt * c
    # print 't=', t, ' s=',s, ' k=', k, ' l=',l
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,d,sa,sv]

def calculind4(lcs,p):
  kd = calculind3(lcs,p)
  return kd[0]

def valeurc(x,c):
  p = qimt(x)
  r1 = moyindc (c, calculind4, p)
  r2 = minindc (c, calculind4, p)
  res = (r1[0] + r2[0]) / 2
  f = open('valeurc.txt','a')
  f.write(str(res) + ' ' + str(x) + '\n')
  f.close()
  return res

def randvect(n):
  x = []
  for i in range(n):
    x = x + [uniform(-1.0,1.0)]
  return x

def popinitr(n,c):
  pop = []
  for i in range(n):
    x = randvect(nd)
    v = valeurc(x,c)
    pop = pop + [[v,x]]
  return pop

  

