
def tp(lcs,p):
  tab=tabcours(lcs,p)
  sap(tab)
  t=[]
  for u in tab:
    x=[1.0]+u[2:len(u)]
    rlm=prodmat(transpose(p.coefsrlm),x)[0]   
    t=t+[[u[0]+u[1],rlm]]
  return t

