
def lire_isin_f(nf):
  l=[]
  f=open(nf,'r')
  p=''
  for line in f:
    s=line.split('\t')
    if s[0]!=p:
      p=s[0]
      # print s[0]
      if s[0][0:2]=='FR':
        l=l+[s[0]]
  return l[1:len(l)]

def lire_cours_actions(nf,j1,j2):
  l=lire_isin_f(nf)
  c=[]
  for a in l:
    print a
    c=c+[cours_isin_jours(a,j1,j2)]
  return c
