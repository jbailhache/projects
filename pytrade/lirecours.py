
def lirecours(nom):
  f = open (nom,"r")
  hdr = f.readline()
  print hdr
  c=[[[] for j in range(30)] for v in range(300)]
  code=""
  v=-1
  for line in f:
    r=line.split('\t')
    if (len(r)>6):
      for i in range(3,7):
        r[i]=float(r[i].replace(',','.'))
    if (r[0]!=code):
      code=r[0]
      v=v+1
      nj=j
      j=0
    c[v][j]=r
    j=j+1
  return c


