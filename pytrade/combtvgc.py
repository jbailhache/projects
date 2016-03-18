
def sigmat(t,param):
  return param[12] * exp(-t/param[13])

def combtv(x,y,param,t):
  z=[a for a in x]
  b=uniform(0.0,param[14]+param[8]+param[9]+param[10])
  if b<param[14]:
    z = [uniform(-1.0, 1.0) for a in x]
  elif b<param[14]+param[8]: 
    i=randint(0,len(z)-1)
    z[i]=uniform(-1.0,1.0)
  elif b<param[14]+param[8]+param[9]:
    i=randint(0,len(z)-1)
    z[i]=z[i]+gauss(0.0,sigmat(t,param))
    if z[i]<-1.0: z[i]=-1.0
    if z[i]>1.0: z[i]=1.0
  else:
    if (param[4] != 0) and (x==y):
      return [uniform(-1.0,1.0) for i in range(len(x))]
    z=[0 for i in x]
    b=uniform(0.0,1.0)
    if b<param[5]:
      for i in range(len(x)):
        b=randint(0,1)
        if b==0: z[i]=x[i]
        else: z[i]=y[i]
    else:
      for i in range(len(x)):
        z[i]=(x[i]+y[i])/2.0
  return z

      