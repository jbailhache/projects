
def lfc(nf):
  lcs=lirecours1(nf)[0]
  n=len(lcs)
  return lcs

# wd=240
# hg=160

wd=900
hg=600

afc=0

t1=25

vd = 0

fraisa = 7.5
fraisv = 7.5

l0 = 1000

def achat(lcs):
  c0 = lcs[0][6]
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  s = 0
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    s = 1
    if s<0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
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
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc>0:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return k

def mme(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  s = 0
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    m = a * c + (1-a) * m
    s = c - m
    if s<0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc>0:
    print k
    courbes(d,['black','red','green','blue'],wd,hg,' ')
  return [k,s]

def ph(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  mh = lcs[0][6]
  mb = lcs[0][6]
  s = 0
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    if c > mh :
      mh = c
    else:
	mh = a * c + (1-a) * mh
    if c < mb :
      mb = c
    else:
      mb = a * c + (1-a) * mb
    s = mh + mb - 2*c
    if s<0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,mh/c0,mb/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc>0:
    print k
    courbes(d,['black','red','orange','green','blue'],wd,hg,' ')
  return [k,s]


def mme1(lcs,p):
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
    mp = m
    m = a * c + (1-a) * m
    sp = s
    s = c - m
    if s<0 and sp>0 and m<=mp :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0 and sp<0 and m>=mp :
      acte = int(l/float(c))
    else:
      acte = 0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc>0:
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
      acte = -nt - vd * int((l+c*nt)/float(c))
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

def macd(lcs,lp):
  p=lp[0]
  p2=lp[1]
  p3=lp[2]
  a = 2 / float(p+1)
  a2 = 2 / float (p2+1)
  a3 = 2 / float(p3+1)
  c0 = lcs[0][6]
  l = l0
  nt = 0
  d = []
  m = c0
  m2 = c0
  ld = 0
  # tester avec ld = 0 ou ld = c0 
  s = 0
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    m = a * c + (1-a) * m
    m2 = a2 * c + (1-a2) * m2 
    macd = m - m2
    ld = a3 * macd + (1-a3) * ld
    s = macd - ld
    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
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
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,m/c0,m2/c0,macd/20.0,ld/20.0]]
    # print str(c) + '\t' + str(nt) + '\t' + str(k)
    # raw_input('...')
  if afc>0:
    print k
    courbes(d,['black','green','blue','red','green','orange','purple'],wd,hg,lcs[0][1])
  return [k,s]

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
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    mp = m
    m = a * c + (1-a) * m
    s = m - mp
    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','red','green','blue'],wd,hg,lcs[0][1])
  return k

def mme4(lcs,lp):
  # exemple: lp=[190,40,0,2,-3]
  p = lp[0]
  pac = lp[1]
  sa=lp[2]
  cm = lp[3]
  cmp = lp[4]
  # cmpp = lp[5]
  cmpp = -cm-cmp
  a = 2 / float(p+1)
  aac = 2 / float(pac+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  mp = m
  s = 0
  t=-1
  mac=0
  for cs in lcs:
    t=t+1
    c = cs[6]
    mpp = mp
    mp = m
    m = a * c + (1-a) * m
    # ac = m - 2 * mp + mpp
    # ac = 2*m - 3*mp + mpp
    ac = cm * m + cmp * mp + cmpp * mpp
    mac = aac * ac + (1-aac) * mac
    s = mac-sa
    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,nt,k/10.0,m,ac]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,m/c0,mac*2+0.5,0.5]]
  if afc:
    print k
    courbes(d,['black','green','blue','red','orange','black'],wd,hg,lcs[0][1])
  return k

def mme5(lcs,lp):
  p = lp[0]
  pac = lp[1]
  sa=lp[2]
  a = 2 / float(p+1)
  aac = 2 / float(pac+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  mp = m
  s = 0
  t=-1
  mac=0
  for cs in lcs:
    t=t+1
    c = cs[6]
    mpp = mp
    mp = m
    m = a * c + (1-a) * m
    # ac = m - 2 * mp + mpp
    ac = 2*m - 3*mp + mpp
    macp = mac
    mac = aac * ac + (1-aac) * mac
    s = mac-macp-sa
    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,nt,k/10.0,m,ac]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,m/c0,mac*2+0.5,0.5]]
  if afc:
    print k
    courbes(d,['black','green','blue','red','orange','black'],wd,hg,lcs[0][1])
  return k

def emv(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  h = lcs[0][4]
  b = lcs[0][5]
  mmemv = 0
  t=-1
  for cs in lcs:
    t=t+1
    hp = h
    bp = b
    c = cs[6]
    h = cs[4]
    b = cs[5]
    v = cs[7]
    emv = ( (h+b)/2.0 - (hp+bp)/2.0 ) / float (v) * float(h-b)
    mmemv = a * emv + (1-a) * mmemv
    s = mmemv
    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,emv*1000]]
  if afc>0:
    print k
    courbes(d,['black','green','blue','red'],wd,hg,' ')
  return [k,s]

def cci(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  c = lcs[0][6]
  h = lcs[0][4]
  b = lcs[0][5]
  cmm = (h+b+c)/3.0
  dm = 0
  cci = 0
  t=-1
  for cs in lcs:
    t=t+1
    ccip = cci
    c = cs[6]
    h = cs[4]
    b = cs[5]
    cm = (h + b + c) / 3.0
    cmm = a * cm + (1-a) * cmm
    ecart = abs (cm - cmm)
    dm = a * ecart + (1-a) * dm
    if dm != 0:
      cci = (cm - cmm) / float(dm * 1.5)
    else:
      cci = 0
    if cci<1 and cci>-1 and ccip>1:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif cci<1 and cci>-1 and ccip<-1:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc>0:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,acte]


def slowsto(lcs,p):
  a = 2/float(3+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  t=-1
  hp = lcs[0][4]
  h = lcs[0][4]
  bp = lcs[0][5]
  b = lcs[0][5]
  pcd = h / float(b)
  for cs in lcs:
    t=t+1
    c = cs[6]
    hpp = hp
    hp = h
    h = cs[4]
    bpp = bp
    bp = b
    b = cs[5]
    h3 = max(h,max(hp,hpp))
    b3 = min(b,min(bp,bpp))
    pck = h3 / float(b3)
    pcd = a * pck + (1-a) * pcd
    s = pck - pcd
    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc>0:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,s]

def rsiinv(lcs,lp):
  p0 = lp[0]
  p1 = lp[1]
  p2 = lp[2]
  p = max(p0,max(p1,p2))
  c0 = lcs[0][6]
  l = l0
  nt = 0
  d = []
  c = lcs[0][6]
  s = 0
  lc = [0 for i in range(p0)]
  lrsi = [0 for i in range(p2)]
  mm1 = 0
  mm2 = 0
  for cs in lcs:
    c = cs[6]
    for i in range(p0-1):
      lc[i+1]=lc[i]
    lc[0]=c  
    sh=0
    sb=0
    for i in range(p0-1):
      var = lc[i] - lc[i+1]
      if var > 0:
        sh = sh + var
      elif var < 0:
        sb = sb - var
    mh = sh / float(p0-1)
    mb = sb / float(p0-1)
    if mb != 0:
      rs = mh / float(mb)
      rsi = 1 - (1 / float(1 + rs))
    elif mh == 0:
      rs = 1
      rsi = 0.5
    else:
      rsi = -1
    for i in range(p2-1):
      lrsi[i+1]=lrsi[i]
    lrsi[0]=rsi
    s1=0
    for i in range(p1):
      s1 = s1 + lrsi[i]
    mm1p = mm1
    mm1 = s1 / p1
    s2 = 0
    for i in range(p2):
      s2 = s2 + lrsi[i]
    mm2p = mm2
    mm2 = s2 / p2
    s = mm2 - mm1
    if s<0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc>0:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,s]

def template(lcs,p):

  c0 = lcs[0][6]
  l = l0
  nt = 0
  d = []
  s = 0
  t=-1

  for cs in lcs:
    t=t+1
    c = cs[6]
    
    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
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
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
    # print str(c) + '\t' + str(nt) + '\t' + str(k)
    # raw_input('...')
  if afc>0:
    print k
    courbes(d,['black','green','blue'],wd,hg,lcs[0][1])
  return k

def baulet1(lcs,p):
  p1 = 20
  p2 = 50
  a1 = 2 / float(p1+1)
  a2 = 2 / float(p2+1)

  c0 = lcs[0][6]
  l = l0
  nt = 0
  d = []
  s = 0
  t=-1

  mm1 = c0
  mm2 = c0

  for cs in lcs:
    t=t+1
    c = cs[6]

    mm1 = a1 * c + (1-a1) * mm1
    mm2 = a2 * c + (1-a2) * mm2

    if s<0:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
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
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
    # print str(c) + '\t' + str(nt) + '\t' + str(k)
    # raw_input('...')
  if afc>0:
    print k
    courbes(d,['black','green','blue'],wd,hg,lcs[0][1])
  return [k,s]



def calculind(lcs,mi,mt):
  c0=lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  x = [lcs[0][i+3] for i in range(5)]
  q = prodmat (mi, [1] + x)
  print q
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    x = [cs[i+3] for i in range(5)]
    q = prodmat (mt, q+x)
    if q[0]>0 and q[1]<0:
      acte = int (l/float(c))
    elif q[0]<0 and q[1]>0:
      acte = -nt
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    d = d + [[c/c0,q[2]/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','red','green','blue'],wd,hg,' ')
  return k

def calculind2(lcs,mi,mt):
  c0=lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  x = [lcs[0][i+3] for i in range(5)]
  q = prodmat (mi, x+[1])
  print q
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    x = [cs[i+3] for i in range(5)]
    q = prodmat (mt, q+x+[1])
    s=q[0]
    if s<0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
      acte = int(l/float(c))
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return k

l0 = 10000

def calculind3(lcs,p):
  qi=p[0]
  mt=p[1]
  c0=lcs[0][6]
  l = l0
  nt = 0
  d = []
  q = qi
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    x = [cs[6] / float(c0)]
    q = prodmat (mt, q+x+[1])
    s=q[0]
    if s<0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0:
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
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,s,d]

def calculind4(lcs,p):
  ksd = calculind3(lcs,p)
  return [ksd[0],ksd[1]]

def calculindnl(lcs,mi,lmt):
  c0=lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  x = [lcs[0][i+3] for i in range(5)]
  q = prodmat (mi, x+[1])
  print q
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    x = [cs[i+3] for i in range(5)]
    for mt in lmt:
      q = prodmat (mt, q+x+[1])
      r1 = q[2]
      r2 = q[3]
      r3 = q[4]
      q[2] = max(sign(r1)*r2,r3)
      q[3] = r1 * (r2 ** r3)
      if r3 != 0:
        q[4] = log(abs(r3))
    if q[0]>0 and q[1]<0:
      acte = int (l/float(c))
    elif q[0]<0 and q[1]>0:
      acte = -nt
    else:
      acte = 0
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    k = l + nt * c
    d = d + [[c/c0,q[2]/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','red','green','blue'],wd,hg,' ')
  return k

miemv = [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,0,0],[0,1,0,0,0,0],[0,0,1,0,0,0]]

def lmtemv(p):
  a = 2/float(p+1)
  lmt = [[[0 for i in range(13)] for j in range(7)] for k in range(3)]
  isa=0
  isv=1 
  ir1=2
  ir2=3
  ir3=4
  ihp=5
  ibp=6
  io=7
  ih=8
  ib=9
  ic=10
  iv=11
  i1=12
  # sa=sa, r1=(h+b-hp+bp)/2, r2=v, r3=-1
  lmt[0][isa][isa] = 1
  lmt[0][ir1][ih] = 0.5
  lmt[0][ir1][ib] = 0.5
  lmt[0][ir1][ihp] = -0.5
  lmt[0][ir1][ibp] = -0.5
  lmt[0][ir2][iv] = 1
  lmt[0][ir3][i1] = -1
  # sa=sa, r1=r2, r2=h-b, r3=1, hp=0, bp=0
  lmt[1][isa][isa] = 1
  lmt[1][ir1][ir2] = 1
  lmt[1][ir2][ih] = 0.5
  lmt[1][ir2][ib] = -0.5
  lmt[1][ir3][i1] = 1
  # sa=a*r2+(1-a)*sa, sv=-a*r2+(a-1)*sa, hp=h, bp=b
  lmt[2][isa][ir2] = a
  lmt[2][isa][isa] = 1-a
  lmt[2][isv][ir2] = -a
  lmt[2][isv][isa] = a-1
  lmt[2][ihp][ih] = 1
  lmt[2][ibp][ib] = 1
  return lmt

def emvn(lcs,p):
  mi = miemv
  lmt = lmtemv(p)
  k = calculindnl(lcs,mi,lmt)
  return k

mimme = [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0]]
mimme2 = [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0]]


p = 25
a = 2 / float(p+1)
def mtmme(p):
  a = 2 / float(p+1)
  return [[0, 0, a-1, 0, 0, 0, 1-a, 0], [0, 0, 1-a, 0, 0, 0, a-1, 0], [0, 0, 1-a, 0, 0, 0, a, 0]]

mi2mme = [[0,0,0,0,0,0],[0,0,0,1,0,0]]

def mt2mme(p):
  a=2/float(p+1)
  return [[0,a-1,0,0,0,1-a,0,0],[0,1-a,0,0,0,a,0,0]]

qi3mme = [0,1]

def mt3mme(p):
  a=2/float(p+1)
  return [[0,a-1,1-a,0],[0,1-a,a,0]]

mimacd = [[0,0,0,0,0,0], [0,0,0,0,0,0], [0,0,0,0,1,0], [0,0,0,0,1,0], [0,0,0,0,0,0]]

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

mimme3 = [[0,0,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,1,0]]

def mtmme3(p):
  a=2/float(p+1)
  mt =	[[	0,	0,	-a,	0,	0,	0,	a,	0	]]
  mt = mt +	[[	0,	0,	a,	0,	0,	0,	-a,	0	]]
  mt = mt + [[	0,	0,	1-a,	0,	0,	0,	a,	0	]]
  return mt

qi3macd = [0, 1, 1, 0]

def mt3macd(p1,p2,p3):
  a1 = 2/float(p1+1)
  a2 = 2/float(p2+1)
  a3 = 2/float(p3+1)
  mt = []
  mt = mt + [[0, (1-a1)*(1-a3), -(1-a2)*(1-a3), a3-1, (a1-a2)*(1-a3), 0]]
  mt = mt + [[0, 1-a1, 0, 0, a1, 0]]
  mt = mt + [[0, 0, 1-a2, 0, a2, 0]]
  mt = mt + [[0, (1-a1)*a3, -(1-a2)*a3, 1-a3, (a1-a2)*a3, 0]]
  return mt  

def moymacd(lv):
  s = 0
  s2 = 0
  for val in lv:
    cv = coursval (cours, val)
    k = macd (cv, [12, 26, 9])
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(lv))
  moy2 = s2/float(len(lv))
  return [moy,moy2]

def moyemv(lv):
  s = 0
  s2 = 0
  for val in lv:
    cv = coursval (cours, val)
    k = emv (cv, 14)
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(lv))
  moy2 = s2/float(len(lv))
  return [moy,moy2]

def moycci(lv):
  s = 0
  s2 = 0
  for val in lv:
    cv = coursval (cours, val)
    k = cci (cv, 14)
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(lv))
  moy2 = s2/float(len(lv))
  return [moy,moy2]

def moymme3(lv,p):
  s = 0
  s2 = 0
  for val in lv:
    cv = coursval (cours, val)
    k = mme3 (cv, p)
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(lv))
  moy2 = s2/float(len(lv))
  return [moy,moy2]

def moyind(lv,ind,p):
  s = 0
  s2 = 0
  for val in lv:
    cv = coursval (cours, val)
    ks = ind (cv, p)
    k = ks[0]
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(lv))
  moy2 = s2/float(len(lv))
  return [moy,moy2]

def listevaleurs(cours):
  vals=[]
  for lcs in cours:
    if len(lcs[0])>1:
      val = lcs[0][1]
      vals=vals+[val]
  return vals

def meilleurmacd(cours):
  valeurs=listevaleurs(cours)
  mv=' '
  mk=0
  for v in valeurs:
   if v != 'EDF ENERGIES NOUV':
    print v
    k = macd (coursval(cours,v),[12,26,9])
    if k>mk:
      mk=k
      mv=v
  return [mv, mk]

def testmacd(valeurs):
  # valeurs=listevaleurs(cours)
  lvxy = []
  for v in valeurs:
    print v
    cv = coursval (cours, v)
    n = len(cv)
    cv1 = cv[0:n/2]
    cv2 = cv[n/2:n]
    x = macd (cv1, [12, 26, 9]) - 1000
    y = macd (cv2, [12, 26, 9]) - 1000
    lvxy = lvxy + [[v,x,y]]
  graphtxy(lvxy,750,750)

def testemv(valeurs):
  # valeurs=listevaleurs(cours)
  lvxy = []
  for v in valeurs:
    print v
    cv = coursval (cours, v)
    n = len(cv)
    cv1 = cv[0:n/2]
    cv2 = cv[n/2:n]
    x = emv (cv1, 14) - 1000
    y = emv (cv2, 14) - 1000
    lvxy = lvxy + [[v,x,y]]
  graphtxy(lvxy,750,750)

def testcci(valeurs):
  # valeurs=listevaleurs(cours)
  lvxy = []
  for v in valeurs:
    print v
    cv = coursval (cours, v)
    n = len(cv)
    cv1 = cv[0:n/2]
    cv2 = cv[n/2:n]
    x = cci (cv1, 14) - 1000
    y = cci (cv2, 14) - 1000
    lvxy = lvxy + [[v,x,y]]
  graphtxy(lvxy,750,750)

def testind (valeurs,ind,p):
  # valeurs=listevaleurs(cours)
  lvxy = []
  for v in valeurs:
    print v
    cv = coursval (cours, v)
    n = len(cv)
    cv1 = cv[0:n/2]
    cv2 = cv[n/2:n]
    x = ind (cv1, p)[0] - 1000
    y = ind (cv2, p)[0] - 1000
    lvxy = lvxy + [[v,x,y]]
  graphtxy(lvxy,750,750)

def testmacdp(valeurs):
  # valeurs=listevaleurs(cours)
  lxy = []
  for v in valeurs:
    print v
    cv = coursval (cours, v)
    n = len(cv)
    cv1 = cv[0:n/2]
    cv2 = cv[n/2:n]
    x = macd (cv1, [12, 26, 9]) - 1000
    y = macd (cv2, [12, 26, 9]) - 1000
    lxy = lxy + [[x,y,x+y]]
  graphxyz(lxy,160,160)

def libelles(c):
  l = []
  for a in c:
    if len(a)>0 and len(a[0])>1:
      l = l + [a[0][1]]
  return l

indicateurs = [ 
 [ macd, [12,26,9] ],
 [ emv, 14],
 [ cci, 14],
 [ slowsto, 0],
 [ baulet1, 0] ]

def testindn (c, i):
  fd = open ('testind.txt','w')
  vs = libelles(c)
  for v in vs:
    print
    print v,';',
    fd.write(v+';')
    lks = []
    for fp in i:
      ks = fp[0](coursval(cours,v),fp[1])
      k = ks[0]
      s = ks[1]
      w = s * (k/l0 - 1.0)
      lks = lks + [ks]
      print k,';',s,';',
      fd.write(("%s"%k).replace('.',',')+';'+("%s"%s).replace('.',',')+';')
    fd.write('\n')
  fd.close()


    


  


  



      