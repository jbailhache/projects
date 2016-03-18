
fdmp = 'sgbourse_gamme_20100208_dmp.txt'
factions = 'sgbourse_gamme_20100208_actions.txt'
findices = 'sgbourse_gamme_20100208_indices.txt'
find100211 = 'sgbourse_gamme_20100211_indices.txt'

def extraire_nombre(s):
  t = ''
  for c in s:
    if c.isdigit():
      t=t+c
    if c==',':
      t=t+'.'
  if t=='':
    return 0
  else:
    return float(t)

def lire_warrants_sg(fname):
  lw = []
  f = open(fname,'r')
  for line in f:
    # print line
    t = line.split(';')
    # print t
    # print 'ISIN=',t[9],' parite=',t[5]
    isin = t[9]
    pe = extraire_nombre(t[1])
    achat = extraire_nombre(t[3])
    vente = extraire_nombre(t[4])
    delta = extraire_nombre(t[6])
    levier = extraire_nombre(t[7])
    parite1 = t[5]
    parite2 = parite1.split('/')
    if len(parite2)==2 and parite2[0].isdigit() and parite2[1].isdigit():
      parite = float(parite2[0])/float(parite2[1])
      # print 'ISIN=', isin, ' parite=', parite
      lw = lw + [[isin, parite, pe, achat, vente, delta, levier]]
  return lw

lwdmp = lire_warrants_sg(fdmp)
lwactions = lire_warrants_sg(factions)
lwindices = lire_warrants_sg(findices)
lwind100211 = lire_warrants_sg(find100211)



