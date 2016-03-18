
def normcours1(cv):
  cvn = []
  n = len(cv)
  a = cv[0][6]
  b = cv[n-1][6]
  for t in range(n):
    cvnt = [u for u in cv[t]]
    for j in [3,4,5,6]:
      cvnt[j] *= (a*t + b*(n-1-t))/n/b
    cvn = cvn + [cvnt]
  return cvn

def normcours(c):
  cn = [normcours1(cv) for cv in c]
  return cn