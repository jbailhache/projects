
nq = 4
nd = 1 + nq * (nq + 3)

aft = 0

def qimts(x):
  # print 'len(x)=', len(x)
  s = x[0]
  qi = [x[1+i] for i in range(nq)]
  mt = [[x[1+nq+(nq+2)*i+j] for j in range(nq+2)] for i in range(nq)]
  # suppression des termes constants
  # for i in range(nq):
  #   mt[i][nq+1] = 0
  return [qi,mt,s]

def calculind3r(cours,p):
  nv=len(cours)
  qi=p[0]
  mt=p[1]
  seuil=p[2]
  # if len(lcs)<=0 or len(lcs[0])<=6:
  #   return [0,[]]
  # print ' len(lcs)=', len(lcs), ' lcs[0]=', lcs[0]
  # print 'lcs=',lcs
  lc0=[lcs[0][6] for lcs in cours]
  l = l0
  # nt = 0
  lnt = [0 for i in range(nv)]
  d = []
  # q = qi
  lq = [qi for i in range(nv)]
  t=-1
  #for cs in lcs:

  k = l

  ld = [[] for a in cours]

  for t in range(len(cours[0])):
  # for t in range(8):
 
    #t=t+1

    # print ' '

    # print 't=', t, '\tl=', l
    # for nt in lnt: print nt,
    # print ' '

    # c = cs[6]
    # lc = [cours[i][t][6] for i in range(nv)]
    lc = [0 for i in range(nv)]
    for i in range(nv):
      # print 't=', t, ' i=', i
      lc[i] = cours[i][t][6]
    # print 'lc=', lc

    # x = [cs[6] / float(c0)]
    lx = [[lc[i]/lc0[i]] for i in range(nv)]
    # print 'lx=', lx

    # valorisation totale
    vt = 0.0
    for i in range(nv):
      vt = vt + lnt[i] * lc[i] 

    k = l + vt
    # print 'k=', k

    # liste des signaux
    ls = [0 for i in range(nv)]
    # somme des signaux
    ss = 0.0
    # somme des signaux positifs
    ssp = 0
    for i in range(nv):
      x = lx[i]
      # print 'q = ', q
      # print 'x = ', x
      # q = prodmat (mt, q+x+[1])
      lq[i] = prodmat (mt, lq[i]+x+[1.0])
      # s=q[0]
      s = lq[i][0]
      ls[i] = s
      ss = ss + s
      if s>0: ssp = ssp + s
    # print 'ss=', ss, ' ls=', ls

    # liste des coefficients de repartition 
    lr = [ 0 for i in range(nv) ]
    for i in range(nv):
      if ls[i] <= 0: 
        lr[i] = 0
      else: 
        lr[i] = ls[i] / ssp
    # print 'ss=', ss, ' ssp=', ssp, ' lr=', lr

    # a partir de la liste des coefficients de repartition calculer la repartition optimale
    ro = [0 for i in range(nv)]
    for i in range(nv):
      # ro[i] = int(total * ls[i] / ss / lc[i])
      ro[i] = int (k * lr[i] / lc[i])
    # print 'ro=', ro

    # garde = nombre de titres pour les valeurs conservees
    garde = [0 for i in range(nv)]
    for i in range(nv):
      if (ro[i]-lnt[i]) * lc[i] < seuil:
        garde[i] = lnt[i]
    # print 'garde=', garde

    # valeur totale des titres conserves
    vgarde = 0
    for i in range(nv):
      vgarde = vgarde + garde[i] * lc[i]
    # print 'vgarde=', vgarde

    # liquidites potentiellement disponibles si on vendait tout ce qu'on ne conserve pas
    # dispo = l - vgarde
    dispo = k - vgarde
    # print 'dispo=', dispo

    # somme des signaux pour les valeurs non conservees
    # ss1 = 0
    # for i in range(nv):
    #   if garde[i] == 0:
    #     ss1 = ss1 + ls[i]

    # somme des coef de repartition pour les valeurs non conservees
    sr1 = 0.0
    for i in range(nv):
      if garde[i] == 0:
        sr1 = sr1 + lr[i]
    # print 'sr1=', sr1

    # nouveaux coefs de repartition
    lr1 = [0 for i in range(nv)]
    if sr1 != 0:
      for i in range(nv):
        if (ro[i]-lnt[i])*lc[i] >= seuil:
          lr1[i] = lr[i] / sr1
    # print 'lr1=', lr1

    ss1 = sr1
    # nouvelle repartition
    nr = [0 for i in range(nv)]
    for i in range(nv):
      if (ro[i]-lnt[i])*lc[i] > seuil:
        # nr[i] = ro[i]
        # nr[i] = int (dispo * ls[i] / ss1 / lc[i])
        nr[i] = int (dispo * lr1[i] / lc[i])
      else:
        nr[i] = lnt[i]
    # print 'lnt=', lnt
    # print 'nr=', nr

    # recalculer l 
    # valorisation totale
    vt = 0.0
    for i in range(nv):
      vt = vt + nr[i] * lc[i]
    # print 'vt=', vt 
    l = k - vt
    # print 'l=', l
    
    # la = [nr[i]-lnt[i] for i in range(nv)]
    # for i in range(nv):
    #   l = l + la[i] * lc[i]

    # k = l
    # for i in range(nv):
    #  k = k + nr[i] * lc[i]

    lnt = nr

    # a faire : aucune operation si t < t1

#    if s<0 :
#      acte = -nt - vd * int((l+c*nt)/float(c))
#    elif s>0:
#      acte = int(l/float(c))
#    else:
#      acte = 0
#    if t<t1: acte=0
#    nt = nt + acte
#    l = l - c * acte
#    if acte > 0:
#      l = l - fraisa
#    if acte < 0:
#      l = l - fraisv
#    k = l + nt * c
#    d = d + [[c/c0,nt*c0/l0*0.2+0.2,k/l0]]
#  if afc:
#    print k
#    courbes(d,['black','green','blue'],wd,hg,' ')

    if aft:
      print lnt

    for i in range(len(ld)):
      ld[i] = ld[i] + [[lc[i]/lc0[i],  lnt[i]*lc0[i]/l0*0.2+0.2, k/l0]]

  if afc:
    print k
    for d in ld:
      courbes(d,['black','green','blue'],wd,hg,' ')

  return [k,ld,ls]

def calculind4r(lcs,p):
  kd = calculind3r(lcs,p)
  return kd[0]

def moyindc(cours,ind,p):
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

def expansex(x):
 y = [0.0 for i in range(29)]
 y[0] = 50.0
 y[2] = 1.0
 y[6] = x[0]
 y[7] = x[1]
 y[9] = x[2]
 y[12] = x[3]
 y[13] = x[4]
 y[15] = x[5]
 y[18] = x[6]
 y[19] = x[7]
 y[21] = x[8]
 return y

def valeurc(x,c):
  p = qimts(x)
  # r = moyindc (c, calculind4, p)
  # r = minindcr (c, calculind4r, p)
  r = calculind4r (c, p)
  return r

def writex(fd,x):
  fd.write( '# valeur: '+str(x[0])+'\n')
  qms = qimts(x[1])
  fd.write('# seuil = '+str(qms[2])+'\n')
  fd.write( '# qi = ')
  for a in qms[0]:
    fd.write(" %6.3f" % a)
  fd.write( '\n# mt = \n# ' )
  for a in qms[1]:
    for b in a:
      fd.write( " %6.3f" % b )
    fd.write('\n# ')


