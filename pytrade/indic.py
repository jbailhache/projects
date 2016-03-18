
import math

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
# t1 = 0

vd = 0

fraisa = 7.5
fraisv = 7.5

tracind=0

def achat(lcs):
  # if len(lcs)<=0 or len(lcs[0])<=6:
  #  return 0
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
  l0 = 1000
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
    s = (c - m)/m
    # print t,c,m,s
    if s<0 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>0 :
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
    d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
  if afc>0:
    print k, lcs[0][1]
    courbes(d,['black','red','green','blue','purple'],wd,hg,' ')
  return k

def mmes(lcs,p):
  a = 2 / float(p[0]+1)
  c0 = lcs[0][6]
  l0 = 1000
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
    s = (c - m)/m
    if s<p[1] :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>p[2] :
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
    if tracind:
      print t,c,m,s,k
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[0,c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
  if afc>0:
    print k, lcs[0][1]
    courbes(d,['black','black','red','green','blue','purple'],wd,hg,' ')
  return k


def mmes2(lcs,p):
  a = 2 / float(p[0]+1)
  a2 = 2 / float(p[1]+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  m2 = lcs[0][6]
  s = 0
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    m = a * c + (1-a) * m
    #m2 = a2 * c + (1-a2) * m
    m2 = a2 * c + (1-a2) * m2
    s = (m2 - m)/m
    if s<p[2] :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>p[3] :
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
    if tracind:
      print t,k,l,c,m,s
    # d = d + [[c,m,nt,k/10.0]]
    # d = d + [[0,c/c0,(c-cs[3])/c0*4,m/c0,m*(1+p[2])/c0,m*(1+p[3])/c0,m2/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    d = d + [[0,c/c0,m/c0,m*(1+p[2])/c0,m*(1+p[3])/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]

  if afc>0:
    print k, lcs[0][1]
    # courbes(d,['black','black','brown','red','red','red','green','blue','purple'],wd,hg,' ')
    courbes(d,['black','black','red','red','red','green','blue','orange','blue','purple'],wd,hg,' ')
  return k


def signal_mmes(lcs,p):
  a = 2 / float(p[0]+1)
  c0 = lcs[0][6]
  l0 = 1000
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
    s = (c - m)/m
    if s<p[1] :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>p[2] :
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
    if tracind:
      print t,k,l,c,m,s,s/p[2]
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[0,c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
  if afc>0:
    print k, lcs[0][1]
    courbes(d,['black','black','red','green','blue','purple'],wd,hg,' ')
  return s


def signal_mmes2(lcs,p):
  a = 2 / float(p[0]+1)
  a2 = 2 / float(p[1]+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  m = lcs[0][6]
  m2 = lcs[0][6]
  s = 0
  t=-1
  for cs in lcs:
    t=t+1
    c = cs[6]
    m = a * c + (1-a) * m
    m2 = a2 * c + (1-a2) * m2
    s = (m2 - m)/m
    if s<p[2] :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>p[3] :
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
    if tracind:
      #print t,c,m,s,k
      print t,k,l,s/p[2],m,m2
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[0,c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
  if afc>0:
    print k, lcs[0][1]
    courbes(d,['black','black','red','green','blue','purple'],wd,hg,' ')
  return s


def init_mme (cs, p):
  s = 0
  m = cs[6]
  q = [s, m]
  return q

def etape_mme (q, cs, p):
  a = 2 / float(p+1)
  c = cs[6]
  q[1] = a * c + (1-a) * q[1]
  q[0] = c - q[1]

def init_mmes2 (cs, p):
  s = 0
  m = cs[6]
  m2 = cs[6]
  q = [s,m,m2]
  return q
  
def etape_mmes2 (q, cs, p):
  a = 2 / float(p[0]+1)
  a2 = 2 /float(p[1]+1)
  c = cs[6]
  q[1] = a * c + (1-a) * q[1]
  q[2] = a2 * c + (1-a2) * q[2]
  q[0] = (q[2] - q[1]) / q[1] / p[2]
  
  
def init_mmee (cs, p):
  s = 0
  m = cs[6]
  mm = 0
  q = [s, m, mm, mm]
  return q

def etape_mmee (q, cs, p):
  a1 = 2 / float (p[0]+1)
  a2 = 2 / float (p[1]+1)
  c = cs[6]
  q[1]= a1 * c + (1-a1) * q[1]
  q[2] = q[3]
  q[3] = a2 * (c - q[1]) + (1-a2) * q[3]
  q[0] = q[3] - q[2]

def graphe_mmee (q,cs,p,c0):
  return [[q[1]/c0, (cs[6]-q[1])/c0, q[3]/c0],['purple','brown','red']]

def init_rsi(cs,p):
 c=cs[6]
 q=[0,c,c,c]
 return q
 
def etape_rsi(q,cs,p):
 a=2/float(p[0]+1)
 c=cs[6]
 if c>q[1]: 
  q[2]=a*c+(1-a)*q[2]
 if c<q[1]:
  q[3]=a*c+(1-a)*q[3]
 q[0]=4*(1-2/(1+q[2]/q[3]))
 q[1]=c
 # print q
 
def graphe_rsi(q,cs,p,c0):
 return [[q[0]],['red']]
 
def init_sk(cs,p):
 k=(cs[6]-cs[5])/(cs[4]-cs[5])
 return [k,cs[4],cs[5],k]
 
def etape_sk(q,cs,p):
 a=2/float(p[0]+1)
 b=2/float(p[1]+1)
 if cs[4]>q[1]:
  q[1]=cs[4]
 else:
  q[1]=a*cs[4]+(1-a)*q[1]
 if cs[5]<q[2]:
  q[2]=cs[5]
 else:
  q[2]=a*cs[5]+(1-a)*q[2]
 q[3]=(cs[6]-q[2])/(q[1]-q[2])/4
 q[0]=b*q[3]+(1-b)*q[0]
 
def graphe_sk(q,cs,p,c0):
 return [[q[0]],['red']]
 
def init_rl (cs, p):
  c = cs[6]
  return [0, 0, 0, 0, c, 0, 0, c, c, c, 0, 0, 0]

def graphe_rl (q, cs, p, c0):
  # return [[0, q[6], q[8]/c0, 10*(q[8]/q[9]-1), q[6]-q[10] ], ['black','purple','red','orange','brown']]   
  # return [[0, q[6], q[8]/c0, 4*(q[6]-q[10]) ], ['black','purple','red','orange']]   
  if q[1]>10:
    y=q[10]
    z=q[11]
  else:
    y=0
    z=0
  # return [[0, q[6], q[8]/c0, 10*(q[8]/q[9]-1),-10*p[1],10*p[1],math.atan(y)], ['black','purple','red','orange','black','black','brown']]
  # rl2:   
  # return [[0, q[6], q[8]/c0, -math.atan(p[1]),math.atan(p[1]),math.atan(y)], ['black','purple','red','black','black','brown']]   
  # return [[0, q[6], q[8]/c0, -0.1, 0.1, 0.1*q[0]], ['black','purple','red','black','black','brown']]   
  return [[0, q[6], q[8]/c0, -p[1], p[1]], ['black','purple','red','black','black']]   

def etape_rl (q, cs, p):
  a=2/float(p[0]+1)
  q[2]=a*q[1]+(1-a)*q[2]
  q[3]=a*(q[1]**2)+(1-a)*q[3]
  q[4]=a*cs[6]+(1-a)*q[4]
  q[5]=a*(q[1]*cs[6])+(1-a)*q[5]
  v=float(q[3]-q[2]**2)
  q[10]=q[6]
  if v != 0:
    q[6]=(q[5]-q[2]*q[4])/v
    q[7]=(q[4]*q[3]-q[2]*q[5])/v
  q[9]=q[8]
  q[8]=q[6]*q[1]+q[7]
  drl=q[8]-q[9]
  q[10]=q[6]*drl**2
  q[11]=q[6]**2*drl
  q[1]=q[1]+1
  q[0]=(q[8]/q[9]-1)/p[1]
  # if q[10]!=0:
  #   q[0]=(q[6]/q[10]-1)/p[1]
  # q[0]=(q[6]-q[10])/p[1]
  # q[0]=-q[10]/p[1]

def etape_rlt (q, cs, p):
  a=2/float(p[0]+1)
  q[2]=a*q[1]+(1-a)*q[2]
  q[3]=a*(q[1]**2)+(1-a)*q[3]
  q[4]=a*cs[6]+(1-a)*q[4]
  q[5]=a*(q[1]*cs[6])+(1-a)*q[5]
  v=float(q[3]-q[2]**2)
  q[10]=q[6]
  if v != 0:
    q[6]=(q[5]-q[2]*q[4])/v
    q[7]=(q[4]*q[3]-q[2]*q[5])/v
  q[9]=q[8]
  q[8]=q[6]*q[1]+q[7]
  drl=q[8]-q[9]
  q[10]=q[6]*drl**2
  q[11]=q[6]**2*drl
  q[1]=q[1]+1
  # q[0]=(q[8]/q[9]-1)/p[1]
  # if q[10]!=0:
  #   q[0]=(q[6]/q[10]-1)/p[1]
  # q[0]=(q[6]-q[10])/p[1]
  # rl2:
  # q[0]=-q[10]/p[1]
  q[0] = -q[6]/p[1]

class indic_rlc():
  def __init__ (self,c):
    self.s = 0
    self.t = 0
    self.mt = 0
    self.mt2 = 0
    self.mc = c
    self.mtc = 0
    self.a = 0
    self.ap = 0
    self.b = c
    self.rl = c
    self.rlp = c

def init_rlc(cs,p):
  q = indic_rlc(cs[6])
  return q

def graphe_rlc(q,cs,p,c0):
  return [[0, q.a, q.rl/c0, -p[1], p[1]], ['black','purple','red','black','black']]   

def etape_rlc (q, cs, p):
  a = 2/float(p[0]+1)
  q.mt = a*q.t+(1-a)*q.mt
  q.mt2 = a*q.t**2+(1-a)*q.mt2
  q.mc = a*cs[6]+(1-a)*q.mc
  q.mtc = a*(q.t*cs[6])+(1-a)*q.mtc
  v = float(q.mt2-q.mt**2)
  q.ap = q.a
  if v != 0:
    q.a = (q.mtc-q.mt*q.mc)/v
    q.b = (q.mc*q.mt2-q.mt*q.mtc)/v
  q.rlp = q.rl
  q.rl = q.a * q.t + q.b
  drl = q.rl - q.rlp
  q.s = (q.rl / q.rlp - 1) / p[1]
  q.t = q.t + 1

def repete1 (init, etape, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    s = q[0]
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[0, c/c0, q[0], nt*c0/l0*0.2+0.2, k/l0]]  
  if afc>0:
    print k
    courbes(d,['black','black','red','green','blue','purple','brown','orange','yellow'],wd,hg,' ')
  return k

def repete (lcs, p):
  k = repete1 (p[0], p[1], lcs, p[2])
  return k

def repeteg (lcs, p):
  k = repete1g (p[0], p[1], p[2], lcs, p[3])
  return k

def repete1g (init, etape, graphe, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    s = q[0]
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[0, c/c0, nt*c0/l0*0.2+0.2, k/l0] + graphe(q,cs,p,c0)[0]]  
  if afc>0:
    print k, cs[1]
    courbes(d,['black','black','green','blue']+graphe(q,cs,p,c0)[1],wd,hg,' ')
  return k

def repetegs (lcs, p):
  k = repete1gs (p[0], p[1], p[2], lcs, p[3])
  return k

def repetegsc (lcs, p):
  k = repete1gsc (p[0], p[1], p[2], lcs, p[3])
  return k

def repete1gs (init, etape, graphe, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    s = q[0]
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
    if s<-1 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>1:
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[0, c/c0, nt*c0/l0*0.2+0.2, k/l0] + graphe(q,cs,p,c0)[0]]  
  if afc>0:
    print k, cs[1]
    courbes(d,['black','black','green','blue']+graphe(q,cs,p,c0)[1],wd,hg,' ')
  return k

def repete1gsc (init, etape, graphe, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    # s = q[0]
    s = q.s
    # print s
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
    if s<=-1 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>=1:
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[0, c/c0, nt*c0/l0*0.2+0.2, k/l0] + graphe(q,cs,p,c0)[0]]  
  if afc>0:
    print k, cs[1]
    courbes(d,['black','black','blue','blue']+graphe(q,cs,p,c0)[1],wd,hg,' ')
  return k

def q_repete1gsc (init, etape, graphe, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  # l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    # s = q[0]
    s = q.s
    # print s
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
    if s<=-1 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>=1:
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[0, c/c0, nt*c0/l0*0.2+0.2, k/l0] + graphe(q,cs,p,c0)[0]]  
  if afc>0:
    print k, cs[1]
    courbes(d,['black','black','blue','blue']+graphe(q,cs,p,c0)[1],wd,hg,' ')
  return q

def q_repete1 (init, etape, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    s = q[0]
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[c/c0, q[0], nt*c0/l0*0.2+0.2, k/l0]]
    # print q[0]
  if afc>0:
    print k
    courbes(d,['black','red','green','blue'],wd,hg,' ')
  return q

def q_repete1class (init, etape, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    s = q.s
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[c/c0, q.s, nt*c0/l0*0.2+0.2, k/l0]]
    # print q[0]
  if afc>0:
    print k
    courbes(d,['black','red','green','blue'],wd,hg,' ')
  return q

def q_repete1s (init, etape, lcs, p):
  # print ('p='+str(p))
  # a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  cs = lcs[0]
  q = init (cs, p)
  # m = lcs[0][6]
  # s = 0
  t=-1
  # q = [s, m]
  for cs in lcs:
    t=t+1
    # print('avant: q='+str(q))
    etape (q, cs, p)
    # print('apres: q='+str(q))
    s = q[0]
    c = cs[6]
    # m = a * c + (1-a) * m
    # s = c - m
    if s<-1 :
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>1:
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
    # d = d + [[c/c0,m/c0,nt*c0/l0*0.2+0.2,k/l0,(c-m)/c0]]
    # d = d + [[c/c0, q[1]/c0, nt*c0/l0*0.2+0.2, k/l0, (c-q[1])/c0]]
    d = d + [[c/c0, q[0], nt*c0/l0*0.2+0.2, k/l0]]
    # print q[0]
    if tracind:
      print t,k,l,q
  if afc>0:
    print k
    courbes(d,['black','red','green','blue'],wd,hg,' ')
  return q


# q = [s, q1, q2]
# p = [i1, e1, p1, i2, e2, p2, comb]

def comb_init (cs, p):
  i1 = p[0]
  p1 = p[2]
  i2 = p[3]
  p2 = p[5]
  comb = p[6]
  q1 = i1 (cs, p1)
  q2 = i2 (cs, p2)
  s1 = q1[0]
  s2 = q2[0]
  s = comb(s1,s2)
  q = [s, q1, q2]
  return q

def comb_etape (q, cs, p):
  e1 = p[1]
  p1 = p[2]
  e2 = p[4]
  p2 = p[5]
  comb = p[6]
  q1 = q[1]
  q2 = q[2]
  e1(q1,cs,p1)
  e2(q2,cs,p2)
  q[0] = comb(q1[0],q2[0])

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
  # print 'macd'
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
    # print t,c,m,m2,macd,ld,s
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

def macds(lcs,lp):
  # print 'macd'
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
    # print t,c,m,m2,macd,ld
    # if macd - ld == 0:
    #  s = 0
    # else:
    s = (macd - ld) / m2
    # s = (macd - ld) / c
    if s<lp[3]:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>lp[4]:
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
    if tracind:
      print t,c,m,m2,macd,ld,s,k
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,m/c0,m2/c0,macd/20.0,ld/20.0]]
    # print str(c) + '\t' + str(nt) + '\t' + str(k)
    # raw_input('...')
  if afc>0:
    print k
    courbes(d,['black','green','blue','red','green','orange','purple'],wd,hg,lcs[0][1])
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
  l0 = 1000
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
    if acte > 0:
      l = l - fraisa
    if acte < 0:
      l = l - fraisv
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,mmemv*1000000,0]]
  if afc>0:
    print k
    courbes(d,['black','green','blue','red','black'],wd,hg,' ')
  return k


def emvs(lcs,p):
  a = 2 / float(p[0]+1)
  c0 = lcs[0][6]
  l0 = 1000
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
    if s<p[1]:
      acte = -nt - vd * int((l+c*nt)/float(c))
    elif s>p[2]:
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
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,mmemv*1000000,0]]
  if afc>0:
    print k
    courbes(d,['black','green','blue','red','black'],wd,hg,' ')
  return k


def cci(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
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
    if acte != 0:
      print "%4d %6.3f %6.3f %3d" % (t, ccip, cci, acte)
    if t<t1: acte=0
    nt = nt + acte
    l = l - c * acte
    if acte > 0:
      l = l - fraisa
    if acte < 0:
      l = l - fraisv
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,cm/c0,cmm/c0,cci/10.0,0.1,-0.1]]
  if afc>0:
    print k
    courbes(d,['black','green','blue','red','orange','purple','black','black'],wd,hg,' ')
  return k

def init_cci (cs, p):
  c = cs[6]
  h = cs[4]
  b = cs[5]
  cmm = (h+b+c)/3.0
  dm = 0
  cci = 0
  q = [0, 0, 0, cmm, 0, dm, cci]
  return q

def etape_cci (q, cs, p):
    # print ('q='+str(q))
    a = 2 / float(p+1)
    cmm = q[3]
    dm = q[5]
    cci = q[6]
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
      s = -1
    elif cci<1 and cci>-1 and ccip<-1:
      s = 1
    else:
      s = 0
    q[0] = s
    q[1] = ccip
    q[2] = cm
    q[3] = cmm
    q[4] = ecart
    q[5] = dm
    q[6] = cci
  
def init_ccia (cs, p):
  c = cs[6]
  h = cs[4]
  b = cs[5]
  cmm = (h+b+c)/3.0
  dm = 0
  cci = 0
  mmecci = 0
  q = [0, 0, 0, cmm, 0, dm, cci, mmecci, mmecci]
  return q

def etape_ccia (q, cs, p):
    # print ('q='+str(q))
    a = 2 / float(p[0]+1)
    a2 = 2 / float(p[1]+1)
    cmm = q[3]
    dm = q[5]
    cci = q[6]
    mmecci = q[7]
    ccip = cci
    mmeccip = mmecci
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
    mmecci = a2 * cci + (1-a2) * mmecci
    # print b, cci, mmecci
    # if mmecci<p[3] and mmecci>p[2] and mmeccip>p[3]:
    if mmecci<p[3] and mmeccip>p[3]:
      s = -1
    # elif mmecci<p[3] and mmecci>p[2] and mmeccip<p[2]:
    elif mmecci>p[2] and mmeccip<p[2]:
      s = 1
    # elif mmecci<p[2]:
    #   s = -1
    # elif mmecci>p[3]:
    #   s = 1
    else:
      s = 0
    q[0] = s
    q[1] = ccip
    q[2] = cm
    q[3] = cmm
    q[4] = ecart
    q[5] = dm
    q[6] = cci
    q[7] = mmecci
    q[8] = mmeccip
  
def graphe_ccia(q,cs,p,c0):
 return [[q[7]/10.0,p[2]/10.0,p[3]/10.0], ['purple','black','black']]

sel3 = ['ALTEN', 'ILIAD', 'BOUYGUES', 'LVMH MOET HENNESSY', 'PPR', 'GDF SUEZ', 'CHRISTIAN DIOR']

def testi(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
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
    if acte > 0:
      l = l - fraisa
    if acte < 0:
      l = l - fraisv
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,cm/c0,cmm/c0,cci/10.0,0.1,-0.1]]
  if afc>0:
    print k
    courbes(d,['black','green','blue','red','orange','purple','black','black'],wd,hg,' ')
  return k

def comb1(s1,s2):
  if s1>0 and s2>0:
    return s1+s2
  elif s1<0 and s2<0:
    return s1+s2
  else:
    return 0

def init_comb_mme_cci (cs, p):
  p_mme = p[0]
  p_cci = p[1]
  q_mme = init_mme (cs, p_mme)
  q_cci = init_cci (cs, p_cci)
  s = comb1 (q_mme[0], q_cci[0])
  q = [s, q_mme, q_cci]
  return q

def etape_comb_mme_cci (q, cs, p):
  q_mme = q[1]
  q_cci = q[2]
  p_mme = p[0]
  p_cci = p[1]
  etape_mme (q_mme, cs, p_mme)
  etape_cci (q_cci, cs, p_cci)
  s = comb1 (q_mme[0], q_cci[0])
  q[0] = s
      
def mmecci(lcs,p):
  a = 2 / float(p+1)
  c0 = lcs[0][6]
  l0 = 1000
  l = l0
  nt = 0
  d = []
  c = lcs[0][6]
  m = c
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
    m = a * c + (1-a) * m
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
    if acte > 0:
      l = l - fraisa
    if acte < 0:
      l = l - fraisv
    k = l + nt * c
    # d = d + [[c,m,nt,k/10.0]]
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0,cm/c0,cmm/c0,cci/10.0,0.1,0,-0.1,(c-m)/c0]]
  if afc>0:
    print k
    courbes(d,['black','green','blue','red','orange','purple','black','black','black','brown'],wd,hg,' ')
  return k



def slowsto(lcs,p):
  a = 2/float(3+1)
  c0 = lcs[0][6]
  l0 = 1000
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
  return k

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
  return k

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

ohbc = 0
av = 0

def calculind3c(lcs,p):
  qi=p[0]
  mt=p[1]
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
    # print 't=', t, ' s=',s, ' k=', k, ' l=',l
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,d,s]

def calculind3cav(lcs,p):
  qi=p[0]
  mt=p[1]
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
    x = [cs[6] / float(c0)]
    q = prodmat (mt, q+x+[1])
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

def calculind3ohbc(lcs,p):
  qi=p[0]
  mt=p[1]
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
    c = float(cs[6])
    x = [float(cs[i]) / float(c0) for i in [3,4,5,6]]
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
    # print 't=', t, ' s=',s, ' k=', k, ' l=',l
    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
  if afc:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,d,s]


def calculind3ohbcav(lcs,p):
  qi=p[0]
  mt=p[1]
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
    q = prodmat (mt, q+x+[1])
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

def f1(q):
  if q[3] == 0:
    r1 = 0
  else:
    r1 = q[2]/q[3]
  if q[4]<q[5]:
    r2 = q[0]
  else:
    r2 = q[7]
  return [r1, r2]

def calculind3ohbcavnl(lcs,p,f):
  qi=p[0]
  mt=p[1]
  # if len(lcs)<=0 or len(lcs[0])<=6:
  #   return [0,[]]
  # print ' len(lcs)=', len(lcs), ' lcs[0]=', lcs[0]
  # print 'lcs=',lcs
  c0=float(lcs[0][6])
  l = l0
  nt = 0
  d = []
  q = qi
  t=-1
  for cs in lcs:
    t=t+1
    c = float(cs[6])
    # x = [cs[6] / float(c0)]
    x = [float(cs[i]) /float(c0) for i in [3,4,5,6]]
    r = f(q) 
    q = prodmat (mt, q+x+[1]+r)
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
    # d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
    d1 = c/c0
    d2 = nt * c0/l0 * 0.2 + 0.2
    d3 = k/l0
    d = d + [[d1,d2,d3]]
  if afc:
    print k
    courbes(d,['black','green','blue'],wd,hg,' ')
  return [k,d,sa,sv]

def calculind3ohbcavnlpe(lcs,p,f):
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

def calculind3(lcs,p):
  if ohbc:
    return calculind3ohbc(lcs,p)
  elif av:
    return calculind3cav(lcs,p)
  elif nl:
    return calculind3ohbcavnl(lcs,p,f1)
  else:
    return calculind3c(lcs,p)

def calculind4(lcs,p):
  kd = calculind3(lcs,p)
  return kd[0]

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
    # print ('cv='+str(cv))
    k = ind (cv, p)
    # print ('k='+str(k))
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    # print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(lv))
  moy2 = s2/float(len(lv))
  return [moy,moy2]

def moyindc(c,ind,p):
  s = 0
  s2 = 0
  for cv in c:
    # print ('cv='+str(cv))
    k = ind (cv, p)
    # print ('k='+str(k))
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    # print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(c))
  moy2 = s2/float(len(c))
  return [moy,moy2]

def titrescours(c):
  # return [a[0][1] for a in c]
  r = []
  for a in c:
    if len(a)>0:
      if len(a[0])>1:
        r = r + [a[0][1]]
  return r

def moyindc1(cours,ind,p):
  s = 0
  s2 = 0
  lv=titrescours(cours)
  for val in lv:
    cv = coursval (cours, val)
    k = ind (cv, p)
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    s = s + k
    s2 = s2 + k2
    print str(k) + '\t' + str(k2) + '\t' + val
  moy = s/float(len(lv))
  moy2 = s2/float(len(lv))
  return [moy,moy2]

def minindc(cours,ind,p):
  m = 100000000.0
  m2 = 100000000.0
  lv=titrescours(cours)
  for val in lv:
    cv = coursval (cours, val)
    k = ind (cv, p)
    k2 = k*cv[0][6]/cv[len(cv)-1][6]
    m = min (m, k)
    m2 = min (m2, k2)
    print str(k) + '\t' + str(k2) + '\t' + val
  return [m,m2]

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
    x = ind (cv1, p) - 1000
    y = ind (cv2, p) - 1000
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




  


  



      
