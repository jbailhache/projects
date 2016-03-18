
def dif(lcs):
  r = []
  for n in range(1,30):
    s = 0
    for j in range (n, len(lcs)-n) :
      s = s + (lcs[j+n][6] - lcs[j][6]) * (lcs[j][6] - lcs[j-n][6]) / (lcs[j][6] * lcs[j][6])
    r = r + [ s/float(len(lcs)-2*n) ]
  return r
