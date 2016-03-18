
execfile('util.py')
execfile('matrix.py')
execfile('graph.py')
execfile('ad.py')
execfile('bourse.py')
execfile('graph.py')

# lmois = ['0901','0902','0903','0904a']
# lmois = ['0902','0903','0904a']
# lmois = ['0907','0908','0909','0910']
lmois = ['0910','0911','0912a']

lnfvista = [(dircoursvista + 'srd-' + mois + '.xls') for mois in lmois]
lnfppc = [(dircoursppc + 'srd-' + mois + '.xls') for mois in lmois2]
lnfxp = [(dircoursxp + 'srd-' + mois + '.xls') for mois in lmois]
lnfh = [(dircoursh + 'srd-' + mois + '.xls') for mois in lmois]
lnfs = [(dircourss + 'srd-' + mois + '.xls') for mois in lmois]
lnfh_sbf250 = [(dircoursh + 'sbf250-' + mois + '.xls') for mois in lmois]

# cours = lirecourslf(lnfh_sbf250)
# cours=lirecourslf(lnfxp)
# cours = lirecourslf(lnfu[45:48])

cours = lirecourslf (['cours/srd-1008.xls', 'cours/srd-1009.xls', 'cours/srd-1010.xls'])

# cours = cours[0:len(cours)-2]

# cours = [x[0:82] for x in cours]

def sizes(c):
  return [ len(a) for a in c ]

def libelles(c):
  return [ a[0][1] for a in c ]

def cloture(c):
  n = len(c[0])
  return [ [ a[6] for a in b[0:n-1] ] for b in c ]

def dataacp(cours):
  cl = cloture(cours)
  return [ [ a/b[0] for a in b ] for b in cl ]

def calculacp(c):
  d = dataacp(c)
  sluc = acpb(d)
  return sluc

def afacp(c,sluc):
  # graph (sluc[2], libelles(c), 1200, 800, 5.0, 11.0, -2.0, 2.0)
  # graph (sluc[2], libelles(c), 800, 600, 7.0, 13.0, -2.0, 2.0)
  # pour srd ci dessous
  # graph (sluc[2], libelles(c), 800, 600, 5.0, 20.0, -5.0, 4.0)
  # pour sbf250 ci dessous
  # graph (sluc[2], libelles(c), 800, 600, 5.0, 15.0, -4.0, 2.0)
  # graph (sluc[2], libelles(c), 800, 600, -20.0, 40.0, -20.0, 20.0)
  # graph (sluc[2], libelles(c), 800, 600, 401, 403, 299,301)
  # graph (sluc[2], libelles(c), 800, 600, 5.0, 8.0, -1.0, 1.0)
  # graph (sluc[2], libelles(c), 800, 600, 6.0, 9.0, -1.0, 1.0)
  # graph (sluc[2], libelles(c), 800, 600, 6.0, 8.5, -0.7, 0.7)
  graph (sluc[2], libelles(c), 800, 600, 6.0, 10.0, -1, 1)

def acpcours():
  sluc = calculacp(cours)
  afacp (cours, sluc)

def testgraph():
  c = a1
  noms = ['a','b','c','d','e']
  graph (c, noms, 600, 800, -20, 20, -20, 20)

  





