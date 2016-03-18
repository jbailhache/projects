
cours=lirecourslf(lnfppc)
lcs=coursval(cours,'HERMES')
mme(lcs,20)
p=[qi3macd,mt3macd(12,26,9)]
calculind3(lcs,p)
calculind4(lcs,p)
moyind(select,mme,14)
moyind(select,calculind4,p)
testind(select,mme,20)
