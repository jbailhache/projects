
from Tkinter import *

wd=800
hg=500
dx=5

f = open ("cours.txt","r")
hdr = f.readline()
print hdr

c=[[[] for j in range(3000)] for v in range(300)]
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

# print c

def depl(d):
  global v,l,w
  v=v+d
  if (len(c[v][0])>1):
    l['text']=c[v][0][1]
  w.create_rectangle(1,1,wd-1,hg-1,fill="yellow")
  # w.create_polygon (10, 20, 20, 10, 30, 20, 20, 30, fill="blue")
  max=0
  min=1000000000 
  for j in range(nj):
    if (c[v][j][5]<min): min=c[v][j][5]
    if (c[v][j][4]>max): max=c[v][j][4]
  if (len(c[v][0])>1):
    lmax['text'] = max
    lmin['text'] = min
  for j in range(nj):
    # w.create_rectangle(5*j+10,115,5*j+13,(max-c[v][j][6])*110/(max-min),fill="blue")
    # w.create_polygon (5*j+10, (max-c[v][j][3])*110/(max-min), 5*j+12, (max-c[v][j][4])*110/(max-min), 5*j+14, (max-c[v][j][6])*110/(max-min), 5*j+12, (max-c[v][j][5])*110/(max-min), fill="blue")
    w.create_line (dx*j+12, (max-c[v][j][4])*(hg-10)/(max-min), 5*j+12, (max-c[v][j][5])*(hg-10)/(max-min), fill="blue")
    w.create_line (dx*j+10, (max-c[v][j][3])*(hg-10)/(max-min), 5*j+12, (max-c[v][j][3])*(hg-10)/(max-min), fill="blue")
    w.create_line (dx*j+12, (max-c[v][j][6])*(hg-10)/(max-min), 5*j+14, (max-c[v][j][6])*(hg-10)/(max-min), fill="blue")    

def suivant ():
  depl(1)

def prec():
  depl(-1)

master=Tk()
w=Canvas(master,width=wd,height=hg)
w.pack(side=LEFT)
w.create_rectangle(1,1,wd-1,hg-1,fill="yellow")
l=Label(master,text="")
l.pack()
lmax=Label(master,text="")
lmax.pack()
lmin=Label(master,text="")
lmin.pack()
bp=Button(master,text="Precedent",command=prec)
bp.pack()
b = Button (master, text="Suivant", command=suivant)
b.pack()

v=-1
mainloop()

        # w.create_rectangle(1,1,239,159,fill="yellow")
        # for i in range(j):
        #   w.create_rectangle(5*i+10,155,5*i+13,(max-a[i])*150/(max-min),fill="blue")
        
        # max=0.0
        # min=1000000000.0
        # a=[0 for x in range(30)]
        # j=0
      #print 'code:' + r[0] + ' lib:' + r[1] + ' date:' + r[2] + ' prem:' + r[3] + ' haut:' + r[4] + ' bas:' + r[5] + ' dern:' + r[6] + ' vol:' + r[7]
      # dern=float(r[6].replace(',','.'))
      # if (dern<min):
      #   min=dern
      # if (dern>max):
      #   max=dern
      # a[j]=dern
     
#w.create_rectangle(5*j+10,150,5*j+13,40-20*(dern-20)+1,fill="blue")
      # j=j+1
 
# for i in range(j):
#   w.create_rectangle(5*i+10,155,5*i+13,(max-a[i])*150/(max-min),fill="blue")

# mainloop()


