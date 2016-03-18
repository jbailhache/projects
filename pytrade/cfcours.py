
def cfcours(c,fn):
  fd = open(fn,"w")
  for d in c:
    for e in d:
      if len(e)>7:
        fd.write("%s\t%s\t%s\t%f\t%f\t%f\t%f\t%d\n"%(e[0],e[1],e[2],e[3],e[4],e[5],e[6],e[7]));    
  fd.close()
