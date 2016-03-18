
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
  return k

def emvcci(lcs,p):
  aemv = 2 / float(p[0]+1)
  acci = 2 / float(p[1]+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  h = lcs[0][4]
  b = lcs[0][5]
  c = lcs[0][6]
  mmemv = 0
  cmm = (h+b+c)/3.0
  dm = 0
  cci = 0
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
    mmemv = aemv * emv + (1-aemv) * mmemv
    s = mmemv

    ccip=cci
    cm = (h + b + c) / 3.0
    cmm = acci * cm + (1-acci) * cmm
    ecart = abs (cm - cmm)
    dm = acci * ecart + (1-acci) * dm
    if dm != 0:
      cci = (cm - cmm) / float(dm * 1.5)
    else:
      cci = 0

    if s<0 and cci<1 and cci>-1 and ccip>1:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0 and cci<1 and cci>-1 and ccip<-1:
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
  return k
