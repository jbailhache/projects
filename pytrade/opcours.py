
def normcours(cours):
  coursn=cours
  c0 = [ a[0][6] for a in cours ]
  # c0 = [ 0 for a in cours ]
  for v in range(len(cours)):
    # c0[v] = cours[v][0][6]
    for t in range(len(cours[v])):
      for j in [3,4,5,6]:
        print 'v=', v, ' t=', t, ' j=', j
        print 'coursn=', coursn[v][t][j], ' /', c0[v]
        # coursn[v][t][j] /= cours[v][0][6]
        coursn[v][t][j] /= c0[v]
        print 'coursn=', coursn[v][t][j]
  return coursn

def sommecours(cours):
  s = [[] for i in range(len(cours[0]))]
  for t in range(len(cours[0])): 
    a = ['SOM', 'Somme', cours[0][t][2], 0.0, 0.0, 0.0, 0.0, 0.0]
    for j in [3,4,5,6]:
      for b in cours:
        a[j] += b[t][j]
    s[t] = a
  return s

def divcours(lcv,cv):
  for v in range(len(lcv)):
    for t in range(len(cv)):
      for j in [3,4,5,6]:
        lcv[v][t][j] /= cv[t][j]
  return lcv


  