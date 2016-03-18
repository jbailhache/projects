
# coefsrlm = [0.0069206829266800479, -0.0025026015718270156, 0.0023652245589585587, 0.0011616079232574762, 0.0014440198520964565, 21189.413761958382, 0.016385963443315905, 0.0056393326983923808, -0.00019842694088381555, -0.0076384189679683167]

class params1:
  def __init__(p):
    p.pl = 28
    p.pc = 14
    p.pmacd = 9
    p.pcci = 18
    p.pmcci = 5
    p.pemv = 85
    # p.prsi = 5
    p.prsi = 50
    p.psk = 14
    p.pmsk = 5
    # p.pmsk = 6
    p.lbrle=1.0
    p.dt = 3
    p.da = 0.11
    # p.srlm = 0.005
    # pour cours normalises :
    # p.srlm = 0.09
    # pour cours normalises et corl :
    p.srlm = 0.018
    p.u = []
    p.sclip = 0.0
    p.coefsip = []

nparam=13

flagim = 0

class params:
  def __init__(p,vp,vc):
   if len(vp)==0:
    p.pl = 27
    p.pc = 15
    p.pmacd = 10
    p.pcci = 18
    p.pmcci = 5
    p.pemv = 85
    # p.prsi = 5
    p.prsi = 51
    p.psk = 14
    p.pmsk = 5
    # p.pmsk = 6
    p.lbrle=1.0
    p.dt = 3
    p.da = 0.11
    # p.srlm = 0.005
    # pour cours normalises :
    # p.srlm = 0.09
    # pour cours normalises et corl :
    p.srlm = 0.019
    p.coefsrlm = vc
    p.u = []
    p.sclip = 0.0
    p.coefsip = []
    if flagim:
      p.qi = qi3macd
      p.mt = mt3macd(12,26,9)
    else:
      p.qi = []
      p.mt = [[]]
   else:
    print 'vp=',vp
    p.srlm = vp[0]
    p.pl = vp[1]
    p.pc = vp[2]
    p.pmacd = vp[3]
    p.pcci = vp[4]
    p.pmcci = vp[5]
    p.pemv = vp[6]
    p.prsi = vp[7]
    p.psk = vp[8]
    p.pmsk = vp[9]
    p.lbrle = vp[10]
    p.dt = vp[11]
    p.da = vp[12]
    p.coefsrlm = vc
    p.u = []
    p.sclip = 0.0
    p.coefsip = []
    if len(vp)>nparam:
      vqimt = vp[nparam:len(vp)]
      qm = qimt (vqimt)
      p.qi = qm[0]
      p.mt = qm[1]
    else:
      p.qi = []
      p.mt = [[]]
  def vect(p):
    vqimt = vecteurqimt (p.qi, p.mt)
    return [ [ p.srlm, p.pl, p.pc, p.pmacd, p.pcci, p.pmcci, p.pemv, p.prsi, p.psk, p.pmsk, p.lbrle, p.dt, p.da ] + vqimt, p.coefsrlm ]
    

def valvp (cours, vp):
  # v = moyrlm (lp[0], lp[1], params(vp)) [0]
  v = testcorlm (cours, params(vp,[])) [0]
  print v, vp
  return v

def optimp (cours, p, n):
  vp = p.vect()[0]
  optim (valvp, cours, vp, n)
  return params(vp,p.coefsrlm)

def valvpvc (cours, vpvc):
  # global coefsrlm
  np = len(params([],[]).vect()[0])
  vp = vpvc[0:np]
  vc = vpvc[np:len(vpvc)]
  # coefsrlm = vc
  # p = params(vp,vc)
  # val = moyrlm (cours, params(vp,vc)) [0]
  val = combrlm (cours, params(vp,vc)) [0]
  # print val, vp, vc
  print 'val=',val
  return val

def optimpc (cours, p, n):
  # global coefsrlm
  r = testcorlm (cours, p)
  print 'testcorlm -> ', r
  # vpvc = p.vect() + coefsrlm
  vpvc1 = p.vect()
  vpvc = vpvc1[0] + vpvc1[1]
  optim (valvpvc, cours, vpvc, n)
  np = len(params([],[]).vect()[0])
  vp = vpvc[0:np]
  vc = vpvc[np:len(vpvc)]
  return [vp, vc]
  # return vpvc1

class indics():
  def __init__(q,cs):
    o = cs[3]
    h = cs[4]
    b = cs[5]
    c = cs[6]
    v = cs[7]
    q.s = 0
    q.dt = 0
    q.c0 = c
    q.histind = []
    q.histip=[]
    q.maxip=[]
    q.minip=[]
# moyennes mobiles et MACD
    q.mlc = c
    q.elc = 0
    q.mcc = c
    q.macd = 0
    q.ld = 0
# CCI
    q.cm = (h+b+c)/3.0
    q.mcm = (h+b+c)/3.0
    q.ecm = 0
    q.vaecm = 0
    q.dm = 0
    q.cci = 0
    q.mcci = 0
# EMV
    q.hp = h
    q.bp = b
    q.emv = 0
    q.memv = 0
# RSI
    q.cp = c
    q.mh = c
    q.mb = c
    q.rsi = 0.5
# SK
    q.hsk = h
    q.bsk = b
    if h-b != 0:
      q.sk = (c-b)/float(h-b)
      q.msk = (c-b)/float(h-b)
    else:
      q.sk = 0.0
      q.msk = 0.0
# RLE
    q.t = 0
    q.mlt = 0
    q.mlt2 = 0
    q.mltc = 0
    q.a = 0
    q.ap = 0
    q.app = 0
    q.amin = 0
    q.amax = 0
    q.b = c
    q.rle = c
    q.rlep = c
    q.mle2 = 0
    q.hbrle = c
    q.bbrle = c
# RLM
    q.rlm = 0
# IM
    q.qim = qi3macd
# IP
    q.ip = [0.0, 0.0, 0.0]

def cmme(m,x,p):
  a = 2/float(p+1)
  return a*x + (1-a)*m

def vectindics (q, cs):
  # return [cs[6], q.mlc, q.ld, q.mcci, q.memv, q.rsi, q.msk, q.rle, q.a]
  # return [cs[6], q.mlc, q.ld, q.mcci, q.rsi, q.msk, q.rle, q.a]
  # return [ cs[6], cs[7], q.mlc, q.ld, q.mcci, q.cp, q.mh, q.mb, q.rsi, q.sk, q.msk, q.rle, q.a]
  # return [ cs[6], cs[7], q.mlc, q.ld, q.cp, q.mh, q.mb, q.rsi, q.sk, q.msk, q.rle, q.a ]
  # cours normalises :
  # return [ cs[6]/q.c0, cs[7], q.mlc/q.c0, q.ld/q.mlc, q.cp/cs[6], q.mh/q.c0, q.mb/q.c0, q.rsi, q.sk, q.msk, q.rle/q.c0, q.a ]
  # return [ cs[6]/q.c0, cs[7], q.mlc/q.c0, q.ld/q.mlc, q.cp/cs[6], q.mh/q.c0, q.mb/q.c0, q.rsi, q.sk, q.msk, q.rle/q.c0, q.a, cs[4]/q.c0, cs[5]/q.c0, q.mcc/q.c0, q.hsk/q.c0, q.bsk/q.c0, q.dm/q.mcm ]
  # return [ cs[6]/q.mlc, q.ld/q.mlc, cs[6]/q.cp, cs[6]/q.mh, cs[6]/q.mb, q.rsi, q.sk, q.msk, cs[6]/q.rle, q.a, cs[6]/cs[4], cs[6]/cs[5], cs[6]/q.mcc, cs[6]/q.hsk, cs[6]/q.bsk, q.dm/q.mcm ]
  if not flagim:
    return [ cs[6]/q.mlc, q.ld/q.mlc, cs[6]/q.cp, cs[6]/q.mh, cs[6]/q.mb, q.rsi, q.msk, cs[6]/q.rle, q.a, cs[6]/cs[4], cs[6]/cs[5], cs[6]/q.mcc, cs[6]/q.hsk, cs[6]/q.bsk, q.dm/q.mcm , q.mcci ]
  else:
    return [ cs[6]/q.mlc, q.ld/q.mlc, cs[6]/q.cp, cs[6]/q.mh, cs[6]/q.mb, q.rsi, q.msk, cs[6]/q.rle, q.a, cs[6]/cs[4], cs[6]/cs[5], cs[6]/q.mcc, cs[6]/q.hsk, cs[6]/q.bsk, q.dm/q.mcm , q.mcci ] + q.qim
  
def init_indics (cs, p):
  q = indics(cs)
  return q

def graphe_indics (q, cs, p, c0):
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, q.memv*1000000,(q.rsi-0.4)*3, 0.1+q.msk/4.0, q.rle/c0, q.a],['cyan','brown','purple','orange','orange','cyan','red', 'red']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.a, 10*q.rlm, -10*p.srlm, 10*p.srlm],['cyan','black','purple','green','black','cyan','red', 'red', 'green','black','black']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.a, 0.1*q.s, -0.1, 0.0, 0.1],['cyan','black','purple','green','black','cyan','red', 'red', 'green','black','black','black']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.a, -0.5+0.1*q.s, -0.6, -0.5, -0.4],['cyan','black','purple','green','black','cyan','red', 'red', 'blue','black','black','black']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.hbrle/c0, q.bbrle/c0, q.a, -0.5+0.1*q.s, -0.6, -0.5, -0.4],['cyan','black','purple','green','black','cyan','red', 'red','red', 'red', 'blue','black','black','black']]
  return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.5)*10-1, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.hbrle/c0, q.bbrle/c0, q.a, -0.5+0.1*q.s, -0.6, -0.5, -0.4, q.ip[0], q.ip[1]],['cyan','black','purple','green','black','cyan','red', 'red','red', 'red', 'blue','black','black','black','brown','orange']]
flagrlm = 1

def etape_indics (q, cs, p):
  o = cs[3]
  h = cs[4]
  b = cs[5]
  c = cs[6]
  v = float(cs[7])
  # q.s = 0
# MME et MACD
  q.mlc = cmme(q.mlc,c,p.pl)
  q.elc = c - q.mlc
  q.mcc = cmme(q.mcc,c,p.pc)
  q.macd = q.mcc - q.mlc
  q.ld = cmme(q.ld,q.macd,p.pmacd)
# CCI
  q.cm = (h+b+c)/3.0
  q.mcm = cmme(q.mcm,q.cm,p.pcci)
  q.ecm = q.cm - q.mcm
  q.vaecm = abs(q.ecm)
  q.dm = cmme(q.dm,q.vaecm,p.pcci)
  if q.dm != 0:
    q.cci = q.ecm / (1.5 * q.dm)
  q.mcci = cmme(q.mcci,q.cci,p.pmcci)
# EMV
  # q.emv = (h+b)/2.0-(q.hp+q.bp)/v*(h-b)
  q.emv = ((h+b)/2.0 - (q.hp+q.bp)/2.0) / v*(h-b)
  q.memv = cmme(q.memv,q.emv,p.pemv)
# RSI
  if c>q.cp:
    q.mh = cmme(q.mh,c,p.prsi)
  if c<q.cp:
    q.mb = cmme(q.mb,c,p.prsi)
  q.rsi = 1-1/(1+q.mh/q.mb)
# SK
  if h>q.hsk:
    q.hsk = h
  else:
    q.hsk = cmme(q.hsk,h,p.psk)
  if b<q.bsk:
    q.bsk = b
  else:
    q.bsk = cmme(q.bsk,b,p.psk)
  if q.hsk-q.bsk != 0:
    q.sk = (c-q.bsk)/float(q.hsk-q.bsk)
  q.msk = cmme(q.msk,q.sk,p.pmsk)
# RLE
  q.mlt = cmme(q.mlt,q.t,p.pl)
  q.mlt2 = cmme(q.mlt2,q.t**2,p.pl)
  q.mltc = cmme(q.mltc,q.t*c,p.pl)
  v = float(q.mlt2-q.mlt**2)
  q.app = q.ap
  q.ap = q.a
  if v!=0:
    q.a = (q.mltc-q.mlt*q.mlc)/v
    q.b = (q.mlc*q.mlt2-q.mlt*q.mltc)/v
  if q.a < q.amin: q.amin = q.a
  if q.a > q.amax: q.amax = q.a
  q.rlep = q.rle
  q.rle = q.a * q.t + q.b
  q.mle2 = cmme(q.mle2,(c-q.rle)**2,p.pl)
  if q.mle2>=0:
    q.hbrle=q.rle+p.lbrle*q.mle2**0.5
    q.bbrle=q.rle-p.lbrle*q.mle2**0.5
  # if q.dt>=p.dt and q.app>q.ap and q.ap<q.a: 
  #   q.s = 2.0
  #   q.dt = 0
  # elif q.dt>=p.dt and q.app<q.ap and q.ap>q.a: 
  #   q.s = -2.0
  #   q.dt = 0
  # else: 
  #   q.s = 0.0
  if q.s<=0 and q.a>q.amin+p.da:
    q.s = 2.0
    q.amax = q.a
    # q.amin = q.a
  elif q.s>=0 and q.a<q.amax-p.da:
    q.s = -2.0
    q.amin = q.a
    # q.amax = q.a
  # else:
  #   q.s = 0
  # print q.s, q.app, q.ap, q.a, q.amin, q.amax
# IM
  # x = [c/float(q.c0)]
  if len(p.mt[0])>0:
    x = [q.rlm]  
    q.qim = prodmat (p.mt, q.qim + x + [1.0])
# RLM
  # x = [1.0, cs[6], q.mlc, q.ld, q.mcci, q.memv, q.rsi, q.msk, q.rle, q.a]
  if flagrlm and p.coefsrlm != []:
    x = [1.0] + vectindics (q, cs)
    q.rlm = prodmat (transpose(p.coefsrlm), x) [0]
    q.s = q.rlm / p.srlm
  else:
    q.rlm = 0
    # q.s = 0
# indicateurs principaux
  if p.u != []:
    vi = vectindics(q,cs)
    # print 'vi=', vi
    q.ip = prodmat ([vi] , transpose(p.u)) [0]
    # print 'q.ip=', q.ip
    x = [1.0] + q.ip
    # print 'x=',x
    if p.sclip != 0:
      q.clip = prodmat(transpose(p.coefsip),x) [0]
      # print 'q.clip=', q.clip
      q.s = q.clip / float(p.sclip)
# precedents et temps
  q.hp = h
  q.bp = b
  q.cp = c
  q.t = q.t + 1
  q.dt = q.dt + 1
# historique
  q.histind = q.histind + [vectindics(q,cs)]
  q.histip=q.histip+[q.ip]
  if q.minip==[]:
    q.minip=[x for x in q.ip]
  else:
    for i in range(len(q.minip)):
      if q.ip[i]<q.minip[i]:
        q.minip[i]=q.ip[i]
  if q.maxip==[]:
    q.maxip=[x for x in q.ip]
  else:
    for i in range(len(q.maxip)):
      if q.ip[i]>q.maxip[i]:
        q.maxip[i]=q.ip[i]
  
def matrind (cours,p):
  ind = []
  for cv in cours:
    q = q_repete1gsc (init_indics, etape_indics, graphe_indics, cv, p)
    ind = ind + q.histind
  return ind
  
def moyrlm (cours, p):
  return moyindc (cours, repetegsc, [init_indics, etape_indics, graphe_indics, p])

combindc = moyindc

def combrlm (cours, p):
  return combindc (cours, repetegsc, [init_indics, etape_indics, graphe_indics, p])

def moyrlmc(lp,c):
 # global coefsrlm
 # coefsrlm=c
 lp[1].coefsrlm = c
 return moyrlm(lp[0],lp[1])[0]


