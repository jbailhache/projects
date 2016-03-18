
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

class params:
  def __init__(p,vp):
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
   else:
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
  def vect(p):
    return [ p.srlm, p.pl, p.pc, p.pmacd, p.pcci, p.pmcci, p.pemv, p.prsi, p.psk, p.pmsk, p.lbrle, p.dt, p.da ]

def valvp (lp, vp):
  # v = moyrlm (lp[0], lp[1], params(vp)) [0]
  v = testcorlm (lp[0], lp[1], params(vp)) [0]
  print v, vp
  return v

def optimp (sel, cours, p, n):
  vp = p.vect()
  optim (valvp, [sel, cours], vp, n)
  return params(vp)

def valvpvc (lp, vpvc):
  global coefsrlm
  np = len(params([]).vect())
  vp = vpvc[0:np]
  vc = vpvc[np:len(vpvc)]
  coefsrlm = vc
  val = moyrlm (lp[0], lp[1], params(vp)) [0]
  # print val, vp, vc
  print 'val=',val
  return val

def optimpc (sel, cours, p, n):
  global coefsrlm
  r = testcorlm (sel, cours, p)
  print 'testcorlm -> ', r
  vpvc = p.vect() + coefsrlm
  optim (valvpvc, [sel, cours], vpvc, n)
  np = len(params([]).vect())
  vp = vpvc[0:np]
  vc = vpvc[np:len(vpvc)]
  return [vp, vc]

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
    q.sk = (c-b)/(h-b)
    q.msk = (c-b)/(h-b)
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
  return [ cs[6]/q.mlc, q.ld/q.mlc, cs[6]/q.cp, cs[6]/q.mh, cs[6]/q.mb, q.rsi, q.msk, cs[6]/q.rle, q.a, cs[6]/cs[4], cs[6]/cs[5], cs[6]/q.mcc, cs[6]/q.hsk, cs[6]/q.bsk, q.dm/q.mcm ]

def init_indics (cs, p):
  q = indics(cs)
  return q

def graphe_indics (q, cs, p, c0):
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, q.memv*1000000,(q.rsi-0.4)*3, 0.1+q.msk/4.0, q.rle/c0, q.a],['cyan','brown','purple','orange','orange','cyan','red', 'red']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.a, 10*q.rlm, -10*p.srlm, 10*p.srlm],['cyan','black','purple','green','black','cyan','red', 'red', 'green','black','black']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.a, 0.1*q.s, -0.1, 0.0, 0.1],['cyan','black','purple','green','black','cyan','red', 'red', 'green','black','black','black']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.a, -0.5+0.1*q.s, -0.6, -0.5, -0.4],['cyan','black','purple','green','black','cyan','red', 'red', 'blue','black','black','black']]
  # return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.4)*3, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.hbrle/c0, q.bbrle/c0, q.a, -0.5+0.1*q.s, -0.6, -0.5, -0.4],['cyan','black','purple','green','black','cyan','red', 'red','red', 'red', 'blue','black','black','black']]
  return [[q.mlc/c0, q.ld/10.0, q.mcci/10.0, (q.rsi-0.5)*10-1, (0.5-0.4)*3, q.msk/4.0, q.rle/c0, q.hbrle/c0, q.bbrle/c0, q.a, -0.5+0.1*q.s, -0.6, -0.5, -0.4],['cyan','black','purple','green','black','cyan','red', 'red','red', 'red', 'blue','black','black','black']]
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
  q.sk = (c-q.bsk)/(q.hsk-q.bsk)
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
# RLM
  # x = [1.0, cs[6], q.mlc, q.ld, q.mcci, q.memv, q.rsi, q.msk, q.rle, q.a]
  if flagrlm:
    x = [1.0] + vectindics (q, cs)
    q.rlm = prodmat (transpose(coefsrlm), x) [0]
    q.s = q.rlm / p.srlm
  else:
    q.rlm = 0
    # q.s = 0
# precedents et temps
  q.hp = h
  q.bp = b
  q.cp = c
  q.t = q.t + 1
  q.dt = q.dt + 1
  
def moyrlm (sel, cours, p):
  return moyind (sel, repetegsc, [init_indics, etape_indics, graphe_indics, p])

def moyrlmc(lp,c):
 global coefsrlm
 coefsrlm=c
 return moyrlm(lp[0],lp[1],lp[2])[0]


