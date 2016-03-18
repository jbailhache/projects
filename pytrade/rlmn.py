
coefsrl = [0.0069206829266800479, -0.0025026015718270156, 0.0023652245589585587, 0.0011616079232574762, 0.0014440198520964565, 21189.413761958382, 0.016385963443315905, 0.0056393326983923808, -0.00019842694088381555, -0.0076384189679683167]

def tabcours (lcs, p):
  tab = []
  cs = lcs[0]
  q = init_indics (cs, p)
  for cs in lcs:
    etape_indics (q, cs, p)
    # tab = tab + [[0, 0, cs[6], q.mlc, q.ld, q.mcci, q.memv, q.rsi, q.msk, q.rle, q.a]]
    tab = tab + [ [0,0] + vectindics(q,cs) ]
  return tab

def sap (tab):
  clo = 2
  for i in range(len(tab)):
    c = tab[i][clo]
    ch = c * 1.02
    cb = c / 1.02
    tph = 0
    tpb = 0
    for j in range (i+1, len(tab)):
      th = (tab[j][clo] - tab[i][clo]) / tab[i][clo] / (j-i)
      if th > tph: tph = th
      tb = (tab[j][clo] - tab[i][clo]) / tab[i][clo] / (j-i)
      if tb < tpb: tpb = tb
    tab[i][0] = tpb
    tab[i][1] = tph

def graphesap (tab):
  d = []
  a = 3
  # rltab = rl (tab)
  # rltab = moyrl (sel3, cours1, p)
  rltab = coefsrl
  coefs = [rltab[0]] + [0.0, 0.0] + rltab[1:len(rltab)]
  for x in tab:
    r = prodmat (transpose(coefs), [1.0]+x) [0]
    d = d + [[0, x[2]/tab[0][2], x[2]/1.02/tab[0][2], x[2]*1.02/tab[0][2], a*x[0], a*x[1], a*(x[0]+x[1]), 4*a*r]]
  courbes (d, ['black', 'black', 'black', 'black', 'red', 'green', 'blue', 'black'], wd, hg, ' ')

def vary (tab):
  y = []
  for u in tab:
    y = y + [u[0]+u[1]]
  return y

def varx (tab):
  x = []
  for u in tab:
    x = x + [[1.0]+u[2:len(u)]]
  return x

def rl (tab):
  y = vary (tab)
  x = varx (tab)
  print 'calcul rl...'
  a = prodmat (inv(prodmat(transpose(x),x)),prodmat(transpose(x),y))
  print 'fait'
  return a

def moyrl (cours, p):
  tab = tabcours (cours[0], p)
  sap (tab)
  # print len(tab), tab[0]
  a = rl(tab)
  # print a
  # for v in sel[1:len(sel)]:
  for cv in cours[1:len(cours)]:
    # tab1 = tabcours (coursval(cours,v), p)
    tab1 = tabcours (cv, p)
    sap (tab1)
    a1 = rl(tab1)
    for i in range(len(a)):
      a[i] = a[i] + a1[i]
  for i in range(len(a)):
    a[i] = a[i] / len(sel)
  return a

def corl (cours, p):
  tab = []
  for cv in cours:
    # print v
    tab1 = tabcours (cv, p)
    sap (tab1)
    tab = tab + tab1
  a = rl(tab)
  return a

def testrlm (cours, p):
  # global flagrlm
  # global coefsrlm
  # flagrlm = 0
  coefsrlm = moyrl (cours, p)
  # flagrlm = 1
  p.coefsrlm = coefsrlm
  r = moyindc (cours, repetegsc, [init_indics, etape_indics, graphe_indics, p])
  return r
 
def testcorlm (cours, p):
  # global flagrlm
  # global coefsrlm
  # flagrlm = 0
  p.coefsrlm = []
  coefsrlm = corl (cours, p)
  # flagrlm = 1
  p.coefsrlm = coefsrlm
  r = moyindc (cours, repetegsc, [init_indics, etape_indics, graphe_indics, p])
  return r

def testsrlm(sel,cours,p,s):
  p.srlm=s
  return moyrlm(cours,p)


