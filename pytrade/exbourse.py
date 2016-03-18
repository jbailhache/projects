
cours=lirecourslf(lnfxp)
cours_2 = lirecourslf(lnfxp2)
lcs=coursval(cours,'HERMES')
mme(lcs,20)
p=[qi3macd,mt3macd(12,26,9)]
calculind3(lcs,p)
calculind4(lcs,p)
moyind(select,mme,14)
moyind(select,calculind4,p)
testind(select,mme,20)
# testindn (cours,[[mme,20]])

# cours1 = lirecourslf(lnfxp[0:3])
# cours2 = lirecourslf(lnfxp[3:6])
# cours3 = lirecourslf(lnfxp[6:9])

cours1 = lirecourslf(lnfxp[42:45])
cours2 = lirecourslf(lnfxp[45:48])
cours3 = lirecourslf(lnfxp[48:51])

cours1 = lirecourslf(lnfxp[42:44])
cours2 = lirecourslf(lnfxp[45:47])
cours3 = lirecourslf(lnfxp[48:50])

c1 = coursval(cours,'PPR')
c2 = coursval(cours,'AXA')
c3 = coursval(cours,'HERMES')

lc = [c1,c2,c3]

seed(31)
print khi2correl(correllc(100,lc))

# valeurs = [ a[0][1] for a in cours ]

lnf=lnfxp

lc4=[0,0,0,0]
lc4[0]=coursval(lirecourslf(lnf[9:12]),'CARREFOUR')
lc4[1]=coursval(lirecourslf(lnf[12:15]),'PPR')
lc4[2]=coursval(lirecourslf(lnf[15:18]),'AXA')
lc4[3]=coursval(lirecourslf(lnf[18:21]),'HERMES')
seed(26)
correlmin(100,lc4)

lc6=[0,0,0,0,0,0]
lc6[0]=coursval(lirecourslf(lnf[0:4]),'BOUYGUES')
lc6[3]=coursval(lirecourslf(lnf[4:8]),'RENAULT')
lc6[1]=coursval(lirecourslf(lnf[8:12]),'CARREFOUR')
lc6[4]=coursval(lirecourslf(lnf[12:16]),'PPR')
lc6[5]=coursval(lirecourslf(lnf[16:20]),'AXA')
lc6[2]=coursval(lirecourslf(lnf[20:24]),'HERMES')
seed(26)
correlmin3(100,lc6)

seed(26)
correlmin411(100,lc6)

seed(26)
correlmin3macd(100,lc6)






