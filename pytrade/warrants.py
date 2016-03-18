
def lire_isin_warrants1():
  l = []
  f = open('warrants20091218.txt','r')
  for line in f:
     s = line.split(';')
     l = l + [s[0]]
  return l

def lire_isin_warrants():
  l = []
  f = open('warrants.txt','r')
  pre = ''
  for line in f:
     s = line.split('\t')
     if s[0] != pre:
       l = l + [s[0]]
       pre = s[0]
  return l

def lire_cours_warrants1(j1,j2):
  l = lire_isin_warrants1()
  cours = []
  for i in l:
    print i
    cours = cours + [cours_isin_jours(i,j1,j2)]
  return cours

def lire_cours_warrants(j1,j2):
  l = lire_isin_warrants()
  cours = []
  for i in l:
    print i
    cours = cours + [cours_isin_jours(i,j1,j2)]
  return cours

def lire_isin_warrants_fr():
  l = []
  f = open('warrants-fr-20091218.txt','r')
  for line in f:
     s = line.split(';')
     l = l + [s[0]]
  return l

def lire_cours_warrants_fr(j1,j2):
  l = lire_isin_warrants_fr()
  cours = []
  for i in l:
    print i
    cours = cours + [cours_isin_jours(i,j1,j2)]
  return cours

ws1 = ['FR0010205880', 'FR0010590455', 'FR0010635060', 'FR0010674119', 'FR0010674127', 'FR0010676957']


ws3=['FR0010205880', 'FR0010246314', 'FR0010600924', 'FR0010674119', 'FR0010731018', 'FR0010740464', 'NL0006246290', 'NL0006529919', 'NL0009115708', 'NL0009131861', 'NL0009132505', 
'NL0009133131', 'DE000CG2CWN8', 'DE000CM6PCE4']

ws4 = ['FR0010600924', 'FR0010674119', 'FR0010731018', 'NL0009131861', 'NL0009133131']

