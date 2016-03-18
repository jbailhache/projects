/*
Reflection principle :
	All d. IsDem d => eval (concl d)
			  eval (left d) = eval (right d)
			  eval_left d = eval_right d
		          eval_LR K d = eval_LR (KI) d
			  LR K K d = LR K (KI) d
	eval rI = I ...
	eval (rap rf ra) = eval rf (eval ra)

        Feferman uniform reflection principle :
	All n. (Pr("phi(n)") => phi(n))
	All n. (Exist d. Dem (d, "phi(n)") => phi(n))
	All n. All d. (Dem (d, "phi(n)" => phi(n))
	[All n. IsDem n =>] All d. IsDem d => (Dem (d, "phi(n)")=>phi(n))
						eval (concl d)
						eval (left d) = eval (right d)
	Parametrize with theory T:
	refl T : All d. IsDem T d => eval T (left T d) = eval T (right T d)
				     eval_LR T K d = eval_LR T (KI) d	 	

	All d. IsDem T d => eval_LR T K d = eval_LR T (K I) d

	parametrize with flag eval/rep :
	All d. IsDem T d => LR T K K d = LR T K (KI) d

	if d is a demonstration ot theory T, then 
	the evaluated left part of the conclusion of d equals the right part.

Representation of theory T by combinators
	T = list of rules
	rule = <arity, function>
	arity = number : 0 z s = z
			 suc n z s = s n
	pair <a, b> f = f a b
	list : nil n i = n
	       ins x l n i = i x l
	index n l = l err (^x:^s: n x : ^p: index p s)
	function : f LR1 ev lr lsd

Representation of a demonstration :
        d = <rn, [sd0, sd1, ...]>
		rn = number of the rule
		sdi = subdem number i	

	LR T ev lr d 
		T = theory = list of <arity, function>
		ev = K for evaluation, KI for representation 
		lr = K for left, KI for right
		d = representation of demonstration

	LR T ev lr d = Y : ^LR1 : d : ^rn : ^lsd :
			index rn T : ^arity: ^f:
			f LR1 T ev lr lsd.
 
Example :
        rule	rep	meaning		arity	function
	I    rI=<1,[]>	I=I		0	^LR1: ^t: ^ev: ^lr: ^lsd: 
						 ev I rI
Extension of a theory T with reflection : T1 = refl T
	Add new item <n+1, fr> at the end of list T
	reflection principle : 
		All d. IsDem T d => LR T K K d = LR T K (KI) d
		                    l d = r d
			with l d = LR T K K d
		     	     r d = LR T K (KI) d
		or :
		MapDem T l = MapDem T r
		with MapDem T f = [ f rI, f rK, f rS, f rE, f rIf,
				    (MapDem T : ^rf : MapDem T : ^ra :
			             f (rap rf ra)), ...]

		representation of MapDem =  rMapDem 
			eval rMapDem = LR T K x rMapDem = MapDem
		representation of T = rT
		representation of l = rl
		representation of r = rr

	refl	MapDem T l=MapDem T r	0    fr=^LR1: ^t: ^ev: ^lr: ^lsd:
						 LR1 t ev lr : 
						 rap (rap rMapDem rT) (lr rl rr)

 	transfinite iteration :
		increasing list of rules
		T = function Ord -> rule ?
		1 rule refl with premise Ord x = I

        axioms :

    Ord ZeroOrd  
    l_ZeroIsOrd = ap (Ord, ZeroOrd);
    r_ZeroIsOrd = I;

    All x. (Ord x => Ord (SucOrd x)) 
    l_SucIsOrd = lambda (x, app (If, ap (Ord, x), ap (Ord, ap (SucOrd, x))));
    r_SucIsOrd = KI;

    All f. (All x. (Ord x => Ord (f x))) => Ord (LimOrd f)) 
    l_LimIsOrd = lambda (f, app (If, app (E, 
	lambda (x, app (If, ap (Ord, x), ap (Ord, ap (f, x)))), KI),
	ap (Ord, ap (LimOrd, f)) ));
    r_LimIsOrd = KI;

    All x. (Ord (SucOrd x) => Ord x) 
    l_PredIsOrd = lambda (x, app (If, ap (Ord, ap (SucOrd, x)), ap (Ord, x)));
    r_PredIsOrd = KI;

    All f. All x. (Ord (Lim f) => Ord x => Ord (f x)) 
    l_StepIsOrd = lambda (f, lambda (x, app (If, ap (Ord, ap (Lim, f)),
	app (If, ap (Ord, x), ap (Ord, ap (f, x))) )));
    r_StepIsOrd = KKI; 
    
    Extensionality :

	K = \xy.x
	S = \xyz.xz(yz)
	S(Ka)(Kb) = K(ab)
	\x.Kab = \x.a
	\x.Sabc = \x.ac(bc)

	[x] Kx = S(K(Kx))I
	[xy] Sxy = S(K(Sxy))I
	[xyu] K(xu)(yu) = xu
	[xyzu] S(xu)(yu)(zu) = (xu)(zu)((yu)(zu))
	[xy] S(Kx)(Ky) = K(xy)
	[f] S(Kf)I = f

		with ([x] a=b) = (\x.a = \x.b)
		\ defined by
			\x.x = I
			\x.y = Ky if x is not in y
			\x.ab = S(\x.a)(\x.b)
			\x.fx = f

	K = \xy.Kxy
	S = \xyz.Sxyz
	\xy.S(Kx)(Ky) = \xy.K(xy)
	\xy.S(S(KK)x)y) = \xyz.xz
	\xyz.S(S(S(KS)x)y)z) = \xyz.S(Sxz)(Syz)

	K = \x.S(K(Kx))I
	S = \xy.S(K(Sxy))I

	K = S(S(KS)(S(KK)K))(K(SKK))                            
		= \xy.Kxy
	S = S(S(KS)(S(K(S(KS)))(S(K(S(KK)))S)))(K(K(SKK)))
		= \xyz.Sxyz
	S(S(KS)(S(KK)(S(KS)K)))(KK) = S(KK)
		\xy.S(Kx)(Ky) = \xy.K(xy)
	S(KS)(S(KK)) = S(KK)(S(S(KS)(S(KK)(SKK)))(K(SKK)))
		\xyu.K(xu)(yu) = \xyu.xu
	S(K(S(KS)))(S(KS)(S(KS))) = S(S(KS)(S(KK)(S(KS)(S(K(S(KS)))S))))(KS)
		\xyzu.S(xu)(yu)(zu) = \xyzu.(xu)(zu)((yu)(zu))
	S(S(KS)K)(K(SKK)) = SKK
		\f.S(Kf)I = \f.f

*/

#include "lctm.h"
 
#define fnc _fnc
#define arg _arg
 
DEM rI, rK, rS, rE, rIf, rOrd, rap, 
	rtransym, rdefI, rdefK, rdefS,
	rAE, rEA, rEXT, rMP, rAI, rAK, rAS, rRPA,
        rZeroIsOrd, rSucIsOrd, rLimIsOrd, rPredIsOrd, rStepIsOrd,
	rExt1, rExt2, rExt3, rExt4, rExt5, rExt6,
        LR;

/*
#define app(f,a,b) ap (ap (f, a), b)
#define appp(f,a,b,c) ap (ap (ap (f, a), b), c)

#define RAP(rf,ra) ap (ap (rap, rf), ra)
#define RAPP(rf,ra,rb) RAP(RAP(rf,ra),rb)

#define LET(var,val,res) ap(lambda(var,res),val)
*/
DEM rep (DEM d)
{
    switch (node(d))
    {
	case _I: return rI;
	case _K: return rK;
	case _S: return rS;
	case _E: return rE;
        case _If: return rIf;
        case _Ord: return rOrd;
	case _ap: return RAP (rep(subdem(0,d)), rep(subdem(1,d)));
	case _transym: return app (rtransym, rep(subdem(0,d)), rep(subdem(1,d)));
	case _defI: return ap (rdefI, rep(subdem(0,d)));
	case _defK: return app (rdefK, rep(subdem(0,d)), rep(subdem(1,d)));
        case _defS: return appp (rdefS, rep(subdem(0,d)), rep(subdem(1,d)), rep(subdem(2,d)));
	case _Ext1: return rExt1;
	case _Ext2: return rExt2;
	case _Ext3: return rExt3;
	case _Ext4: return rExt4;
	case _Ext5: return rExt5;
	case _Ext6: return rExt6;
	case _AE: return rAE;
	case _EA: return ap (rEA, rep(subdem(0,d)));
	case _MP: return rMP;
	case _AI: return rAI;
	case _AK: return rAK;
	case _AS: return rAS;
	case _RPA: return rRPA;
	case _ZeroIsOrd: return rZeroIsOrd;
	case _SucIsOrd: return rSucIsOrd;
	case _LimIsOrd: return rLimIsOrd;
	case _PredIsOrd: return rPredIsOrd;
	case _StepIsOrd: return rStepIsOrd;
    }
}

DEM MapDemL, MapDemR, t0, arefl0, fRefl; /*, ZeroOrd, SucOrd, LimOrd;*/
   
init_refl ()
{
#if 1
DEM True, False, P, Zero, Suc, Eqn, MkNod, Nod, Lsd, Arity, Subdem, 
    Nil, Ins, Adl, MkDem, Index, Length, Eql, EqDem, MapDem, MapDem1, Eval, 
    MkRule, RepTheory, 
    nI, nK, nS, nE, nIf, nOrd, nap, ntransym, ndefI, ndefK, ndefS,
    nExt1, nExt2, nExt3, nExt4, nExt5, nExt6, 
    nAE, nEA, nMP, nAI, nAK, nAS, nRPA,
    nZeroIsOrd, nSucIsOrd, nLimIsOrd, nPredIsOrd, nStepIsOrd;

DEM nod, lsd, f, rf, ra, rb, rc, r1, r2, r, x, l, n, i, z, s;

        nod = Var ("nod", U(Order(0)));
        lsd = Var ("lsd", U(Order(0)));
        f = Var ("f", U(Order(0)));
        rf = Var ("rf", U(Order(0)));
        ra = Var ("ra", U(Order(0)));
        rb = Var ("rb", U(Order(0)));
        rc = Var ("rc", U(Order(0)));
        r1 = Var ("r1", U(Order(0)));
        r2 = Var ("r2", U(Order(0)));
        r = Var ("r", U(Order(0)));
        x = Var ("x", U(Order(0)));
        l = Var ("l", U(Order(0)));
        n = Var ("n", U(Order(0)));
        i = Var ("i", U(Order(0)));
        z = Var ("z", U(Order(0)));
        s = Var ("s", U(Order(0)));

	Zero = K;
	Suc = lambda (n, lambda (z, lambda (s, ap (s, n))));

        Nil = K;
	Ins = lambda (x, lambda (l, lambda (n, lambda (i, app (i, x, l)))));

	MkDem = lambda (nod, lambda (lsd, lambda (f, app (f, nod, lsd))));

	nI = Zero; /*ap (Suc, Zero);*/
	nK = ap (Suc, nI);
	nS = ap (Suc, nK);
	nE = ap (Suc, nS);
	nIf = ap (Suc, nE);
        nOrd = ap (Suc, nIf);
	nap = ap (Suc, nOrd);
	ntransym = ap (Suc, nap);
	ndefI = ap (Suc, ntransym);
	ndefK = ap (Suc, ndefI);
	ndefS = ap (Suc, ndefK);
        nExt1 = ap (Suc, ndefS);
	nExt2 = ap (Suc, nExt1);
	nExt3 = ap (Suc, nExt2);
	nExt4 = ap (Suc, nExt3);
	nExt5 = ap (Suc, nExt4);
	nExt6 = ap (Suc, nExt5),
	nAE = ap (Suc, nExt6);
	nEA = ap (Suc, nAE);
	nMP = ap (Suc, nEA);
	nAI = ap (Suc, nMP);
	nAK = ap (Suc, nAI);
	nAS = ap (Suc, nAK);
	nRPA = ap (Suc, nAS);
        nZeroIsOrd = ap (Suc, nRPA);
	nSucIsOrd = ap (Suc, nZeroIsOrd);
	nLimIsOrd = ap (Suc, nSucIsOrd);
	nPredIsOrd = ap (Suc, nLimIsOrd);
	nStepIsOrd = ap (Suc, nPredIsOrd);

	rI = app (MkDem, nI, Nil);
	rK = app (MkDem, nK, Nil);
	rS = app (MkDem, nS, Nil);
	rE = app (MkDem, nE, Nil);
	rIf = app (MkDem, nIf, Nil);
        rOrd = app (MkDem, nOrd, Nil);
	rap = lambda (rf, lambda (ra, app (MkDem, nap, 
	    app (Ins, rf, app (Ins, ra, Nil)) )));
	rtransym = lambda (r1, lambda (r2, app (MkDem, ntransym,
	    app (Ins, r1, app (Ins, r2, Nil)) )));
	rdefI = lambda (ra, app (MkDem, ndefI, app (Ins, ra, Nil)));
	rdefK = lambda (ra, lambda (rb, app (MkDem, ndefK,
	    app (Ins, ra, app (Ins, rb, Nil)) )));
	rdefS = lambda (ra, lambda (rb, lambda (rc, app (MkDem, ndefS,
	    app (Ins, ra, app (Ins, rb, app (Ins, rc, Nil))) ))));
	rExt1 = app (MkDem, nExt1, Nil);
	rExt2 = app (MkDem, nExt2, Nil);
	rExt3 = app (MkDem, nExt3, Nil);
	rExt4 = app (MkDem, nExt4, Nil);
	rExt5 = app (MkDem, nExt5, Nil);
	rExt6 = app (MkDem, nExt6, Nil);
	rAE = app (MkDem, nAE, Nil);
	rEA = lambda (r, app (MkDem, nEA, app (Ins, r, Nil)));
	rMP = app (MkDem, nMP, Nil);
	rAI = app (MkDem, nAI, Nil);
	rAK = app (MkDem, nAK, Nil);
	rAS = app (MkDem, nAS, Nil);
	rRPA = app (MkDem, nRPA, Nil); 	
        rZeroIsOrd = app (MkDem, nZeroIsOrd, Nil);
	rSucIsOrd = app (MkDem, nSucIsOrd, Nil);
	rLimIsOrd = app (MkDem, nLimIsOrd, Nil);
	rPredIsOrd = app (MkDem, nPredIsOrd, Nil);
	rStepIsOrd = app (MkDem, nStepIsOrd, Nil);

#else
DEM T, vI, vK, vS, vE, vIf, vap, vtransym, vdefI, vdefK, vdefS,
	vAE, vEA, vEXT, vMP, vAI, vAK, vAS, vRPA, Y, A, vLR,
        israp, isrI, isrE, isnrap, isnrI, isnrE, eqdem,
        rf, ra, rb, rc, r1, r2, r, f, f1, d, d1, d2, a, b, c,
        LR_transym, ld, rd, fnc, arg;
DEM True, False, P, Zero, Suc, Eqn, MkNod, Nod, Lsd, Arity, Subdem, 
    Nil, Ins, Adl, MkDem, Index, Length, Eql, EqDem, MapDem, MapDem1, Eval, 
    MkRule, RepTheory, 
    nI, nK, nS, nE, nIf, nOrd, nap, ntransym, ndefI, ndefK, ndefS,
    nExt1, nExt2, nExt3, nExt4, nExt5, nExt6, 
    nAE, nEA, nMP, nAI, nAK, nAS, nRPA,
    nZeroIsOrd, nSucIsOrd, nLimIsOrd, nPredIsOrd, nStepIsOrd,
    n, z, s, s1, s2, p, n1, p1, l, l1, l2, i, x, x1, x2, eq, t, th, rt, ev, lr,
    nod, nod1, nod2, lsd, lsd1, lsd2, rEqn, rIndex, rLength, rEql, rEqDem,
    rMapDem1, rEval, rLR, rAdl, rRepTheory,
    fI, fK, fS, fE, fIf, fOrd, fap, ftransym, fdefI, fdefK, fdefS,
    fExt1, fExt2, fExt3, fExt4, fExt5, fExt6,     
    fAE, fEA, fMP, fAI, fAK, fAS, fRPA, 
    fZeroIsOrd, fSucIsOrd, fLimIsOrd, fPredIsOrd, fStepIsOrd, 
    fRefl0,
    rfI, rfK, rfS, rfE, rfIf, rfOrd, rfap, rftransym, rfdefI, rfdefK, rfdefS,
    rfExt1, rfExt2, rfExt3, rfExt4, rfExt5, rfExt6,
    rfAE, rfEA, rfMP, rfAI, rfAK, rfAS, rfRPA, 
    rfZeroIsOrd, rfSucIsOrd, rfLimIsOrd, rfPredIsOrd, rfStepIsOrd,
    rfRefl0,
    ExtractOrd, RepRep, rRepRep, OrdZero, rfOrder, rx, rOrd, rep_rfOrdx,
    rec_rep_rfOrdx, fRefl, rep_rec_fRefl, rep_fRefl, rec_rep_fRefl,
    RepInt, rRepInt, t1, aRefl0, rfOrdxr, fReflr, tx, rfOrdx;

        print_string (print_param, "init_refl\n");

	T = U(Order(0));
	vI = Var ("vI", T);
	vK = Var ("vK", T);
        vS = Var ("vS", T);
	vE = Var ("vE", T);
	vIf = Var ("vIf", T);
        vap = Var ("vap", T);	
	vtransym = Var ("vtransym", T);
	vdefI = Var ("vdefI", T);
	vdefK = Var ("vdefK", T);
	vdefS = Var ("vdefS", T);
	vAE = Var ("vAE", T);
	vEA = Var ("vEA", T);
	vEXT = Var ("vEXT", T);
	vMP = Var ("vMP", T);
	vAI = Var ("vAI", T);
	vAK = Var ("vAK", T);
	vAS = Var ("vAS", T);
	vRPA = Var ("vRPA", T);		
	vLR = Var ("vLR", T);
        r = Var ("r", T);
        r1 = Var ("r1", T);
        r2 = Var ("r2", T);
        rf = Var ("rf", T);
        ra = Var ("ra", T);
        rb = Var ("rb", T);
        rc = Var ("rc", T);
        f = Var ("f", T);
	f1 = Var ("f1", T);
        d = Var ("d", T);
	d1 = Var ("d1", T);
	d2 = Var ("d2", T);
        lr = Var ("lr", T);
        a = Var ("a", T);
        b = Var ("b", T);
        c = Var ("c", T);
        ld = Var ("ld", T);
        rd = Var ("rd", T);

	n = Var ("n", T);
	z = Var ("z", T);
	s = Var ("s", T);
	s1 = Var ("s1", T);
	s2 = Var ("s2", T);
	p = Var ("p", T);
	n1 = Var ("n1", T);
	p1 = Var ("p1", T);
	l = Var ("l", T);
	l1 = Var ("l1", T);
	l2 = Var ("l2", T);
	i = Var ("i", T);
	x = Var ("x", T);
	x1 = Var ("x1", T);
	x2 = Var ("x2", T);
	d = Var ("d", T);
	eq = Var ("eq", T);
	t = Var ("t", T);
        th = Var ("th", T);
        rt = Var ("rt", T);
	nod = Var ("nod", T);
	nod1 = Var ("nod1", T);
	nod2 = Var ("nod2", T); 
	lsd = Var ("lsd", T);
	lsd1 = Var ("lsd1", T);
	lsd2 = Var ("lsd2", T);
	ev = Var ("ev", T);
	rEqn = Var ("rEqn", T);
	rIndex = Var ("rIndex", T);
	rLength = Var ("rLength", T);
	rEql = Var ("rEql", T);
	rEqDem = Var ("rEqDem", T);
	rMapDem1 = Var ("rMapDem1", T);
	rEval = Var ("rEval", T);
	rLR = Var ("rLR", T);
        rRepTheory = Var ("rRepTheory", T);
        rRepRep = Var ("rRepRep", T);
        rx = Var ("rx", T);
        rec_rep_rfOrdx = Var ("rec_rep_rfOrdx", T);
        rep_rec_fRefl = Var ("rep_rec_fRefl", T); 
        rec_rep_fRefl = Var ("rec_rep_fRefl", T);
        rRepInt = Var ("rRepInt", T);
        t1 = Var ("t1", T);
        tx = Var ("tx", T);
        rAdl = Var ("rAdl", T);

        print_string (print_param, "Variables initialized\n");

#if 1
	A = ap (ap (S, I), I);
	Y = lambda (f, ap (A, ap (ap (S, ap (K, f)), A)));

	True = K;
	False = KI;

	P = lambda (a, lambda (b, lambda (f, app (f, a, b))));

	Zero = K;
	Suc = lambda (n, lambda (z, lambda (s, ap (s, n))));
	Eqn = ap (Y, lambda (rEqn,
	      lambda (n, lambda (p, app (n, app (p, True, ap (K, False)),
			lambda (n1, app (p, ap (K, False), ap (rEqn, n1))) 
		))) ));

/*
        ZeroOrd = lambda (z, lambda (s, lambda (l, z)));
        SucOrd = lambda (x, lambda (z, lambda (s, lambda (l, ap (s, x)))));
        LimOrd = lambda (f, lambda (z, lambda (s, lambda (l, ap (l, f)))));
*/
	Nil = K;
	Ins = lambda (x, lambda (l, lambda (n, lambda (i, app (i, x, l)))));
	Length = ap (Y, lambda (rLength, lambda (l, app (l, Zero, 
	    lambda (x, lambda (l1, 
	    ap (Suc, ap (rLength, l1)) ))))));
	Index = ap (Y, lambda (rIndex, lambda (n, lambda (l, 
	    app (l, I, lambda (x, lambda (l1,
	    app (n, x, lambda (n1, app (rIndex, n1, l1))) )))))));
	Eql = ap (Y, lambda (rEql, lambda (eq, lambda (l1, lambda (l2,
	    app (l1, app (l2, True, ap (K, False)), lambda (x1, lambda (s1,
		app (l2, False, lambda (x2, lambda (s2, 
		    app (app (eq, x1, x2),
			 appp (rEql, eq, s1, s2),
			 False) ))) ))) )))));
        Adl = ap (Y, lambda (rAdl, lambda (l, lambda (x,
            app (l, app (Ins, x, Nil), lambda (x1, lambda (l1,
                app (Ins, x1, app (rAdl, l1, x)) ))) ))));

	MkDem = lambda (nod, lambda (lsd, lambda (f, app (f, nod, lsd))));
	Nod = lambda (d, ap (d, K));
	Lsd = lambda (d, ap (d, KI));
	Arity = lambda (d, ap (Length, ap (Lsd, d)));
	Subdem = lambda (i, lambda (d, app (Index, i, ap (Lsd, d))));

	nI = Zero; /*ap (Suc, Zero);*/
	nK = ap (Suc, nI);
	nS = ap (Suc, nK);
	nE = ap (Suc, nS);
	nIf = ap (Suc, nE);
        nOrd = ap (Suc, nIf);
	nap = ap (Suc, nOrd);
	ntransym = ap (Suc, nap);
	ndefI = ap (Suc, ntransym);
	ndefK = ap (Suc, ndefI);
	ndefS = ap (Suc, ndefK);
        nExt1 = ap (Suc, ndefS);
	nExt2 = ap (Suc, nExt1);
	nExt3 = ap (Suc, nExt2);
	nExt4 = ap (Suc, nExt3);
	nExt5 = ap (Suc, nExt4);
	nExt6 = ap (Suc, nExt5),
	nAE = ap (Suc, nExt6);
	nEA = ap (Suc, nAE);
	nMP = ap (Suc, nEA);
	nAI = ap (Suc, nMP);
	nAK = ap (Suc, nAI);
	nAS = ap (Suc, nAK);
	nRPA = ap (Suc, nAS);
        nZeroIsOrd = ap (Suc, nRPA);
	nSucIsOrd = ap (Suc, nZeroIsOrd);
	nLimIsOrd = ap (Suc, nSucIsOrd);
	nPredIsOrd = ap (Suc, nLimIsOrd);
	nStepIsOrd = ap (Suc, nPredIsOrd);

	rI = app (MkDem, nI, Nil);
	rK = app (MkDem, nK, Nil);
	rS = app (MkDem, nS, Nil);
	rE = app (MkDem, nE, Nil);
	rIf = app (MkDem, nIf, Nil);
        rOrd = app (MkDem, nOrd, Nil);
	rap = lambda (rf, lambda (ra, app (MkDem, nap, 
	    app (Ins, rf, app (Ins, ra, Nil)) )));
	rtransym = lambda (r1, lambda (r2, app (MkDem, ntransym,
	    app (Ins, r1, app (Ins, r2, Nil)) )));
	rdefI = lambda (ra, app (MkDem, ndefI, app (Ins, ra, Nil)));
	rdefK = lambda (ra, lambda (rb, app (MkDem, ndefK,
	    app (Ins, ra, app (Ins, rb, Nil)) )));
	rdefS = lambda (ra, lambda (rb, lambda (rc, app (MkDem, ndefS,
	    app (Ins, ra, app (Ins, rb, app (Ins, rc, Nil))) ))));
	rExt1 = app (MkDem, nExt1, Nil);
	rExt2 = app (MkDem, nExt2, Nil);
	rExt3 = app (MkDem, nExt3, Nil);
	rExt4 = app (MkDem, nExt4, Nil);
	rExt5 = app (MkDem, nExt5, Nil);
	rExt6 = app (MkDem, nExt6, Nil);
	rAE = app (MkDem, nAE, Nil);
	rEA = lambda (r, app (MkDem, nEA, app (Ins, r, Nil)));
	rMP = app (MkDem, nMP, Nil);
	rAI = app (MkDem, nAI, Nil);
	rAK = app (MkDem, nAK, Nil);
	rAS = app (MkDem, nAS, Nil);
	rRPA = app (MkDem, nRPA, Nil); 	
        rZeroIsOrd = app (MkDem, nZeroIsOrd, Nil);
	rSucIsOrd = app (MkDem, nSucIsOrd, Nil);
	rLimIsOrd = app (MkDem, nLimIsOrd, Nil);
	rPredIsOrd = app (MkDem, nPredIsOrd, Nil);
	rStepIsOrd = app (MkDem, nStepIsOrd, Nil);

	israp = lambda (d, app (app (Eqn, ap (Nod, d), nap), True, False));
	isnrap = lambda (d, appp (israp, d, False, True));

	isrI = lambda (d, app (app (Eqn, ap (Nod, d), nI), True, False));
	isnrI = lambda (d, appp (isrI, d, False, True));

	isrE = lambda (d, app (app (Eqn, ap (Nod, d), nE), True, False));
	isnrE = lambda (d, appp (isrE, d, False, True));

	fnc = lambda (d, app (Subdem, Zero, d));
	arg = lambda (d, app (Subdem, ap (Suc, Zero), d));

	EqDem = ap (Y, lambda (rEqDem, lambda (d1, lambda (d2, 
	    ap (d1, lambda (nod1, lambda (lsd1,
	    ap (d2, lambda (nod2, lambda (lsd2,
	    app (app (Eqn, nod1, nod2), False,
		appp (Eql, rEqDem, lsd1, lsd2) ) ))) ))) ))));

	Eval = ap (Y, lambda (rEval, lambda (x,
	    ap (x, lambda (nod, lambda (lsd,
		app (app (Eqn, nod, nap), ap (ap (rEval, ap (fnc, x)),
					      ap (rEval, ap (arg, x))),
		app (app (Eqn, nod, nI), I,
		app (app (Eqn, nod, nK), K,
		app (app (Eqn, nod, nS), S, I) ))) ))) )));

	/* t = theory = [<arity, rf>, ...] */
	MapDem1 = ap (Y, lambda (rMapDem1, lambda (b, 
	    app (b,
		lambda (t, lambda (f,
		    app (t, Nil, lambda (x, lambda (s,
			ap (x, lambda (a, lambda (rf,
			LET (f1, ap (Eval, rf), 
			    app (appp (rMapDem1, False, a, f1), t, f) 
			    ) ))) ))) )),
		lambda (a, lambda (f1, lambda (t, lambda (f,
		    app (a, ap (f, f1),
			lambda (n,  appp (rMapDem1, True, t, lambda (x1,
			    app (appp (rMapDem1, False, n, ap (f1, x1)), t, f)
			    ))) ) )))) ) )));
 	 		
	MapDem = ap (MapDem1, True);

	LR = ap (Y, lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (d,
	    ap (d, lambda (nod, lambda (lsd,
		ap (app (Index, nod, t), lambda (a, lambda (rf,
		    appp (app (ap (Eval, rf), rLR, t), ev, lr, lsd) 
		    ))) ))) )))))); 

        /* other possibility : put function in proof d */

	MkRule = P;

	fI = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		app (ev, I, rI) )))));
	fK = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		app (ev, K, rK) )))));
	fS = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		app (ev, S, rS) )))));
	fE = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		app (ev, E, rE) )))));
	fIf = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		app (ev, If, rIf) )))));
        fOrd = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
             app (ev, Ord, rOrd) )))));

	fap = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		app (app (ev, I, rap),
			appp (rLR, ev, lr, app (Index, Zero, lsd)),
			appp (rLR, ev, lr, app (Index, ap(Suc,Zero), lsd)) 
			) )))));

	ftransym = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		app (app (EqDem , 
			    ap (appp (rLR, t, KI, K), app (Index, Zero, lsd)),
			    ap (appp (rLR, t, KI, K), app (Index, ap(Suc,Zero),
								    lsd)) ),
		     ap (appp (rLR, t, ev, KI), 
			 app (lr, app (Index, Zero, lsd), 
			          app (Index, ap(Suc,Zero), lsd) ) ),
		     app (ev, I, rI) ) )))));

	fdefI = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		    ap (app (lr, ap (app (ev, I, rap), app (ev, I, rI)), I),
		        ap (appp (rLR, t, ev, lr), app (Index, Zero, lsd)) 
		       ) )))));
  
	fdefK = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		    app (lr, 
		         app (app (ev, I, rap), 
			  app (app (ev, I, rap), app (ev, K, rK),
			    ap (appp (rLR, t, ev, lr), app (Index, Zero, lsd))),
			    ap (appp (rLR, t, ev, lr), app (Index, 
				    ap(Suc,Zero), lsd))),
		         ap (appp (rLR, t, ev, lr), app (Index, Zero, lsd)) 
			) )))));
	
        fdefS = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
	    app (lr, app (app (ev, I, rap), 
			app (app (ev, I, rap),
			    app (app (ev, I, rap), app (ev, S, rS),
				ap (appp (rLR, t, ev, lr), 
				    app (Index, Zero, lsd))),
			       ap (appp (rLR, t, ev, lr),
			           app (Index, ap(Suc,Zero), lsd))),
                              ap (appp (rLR, t, ev, lr),
			          app (Index, ap(Suc,ap(Suc,Zero)), lsd))),
		     app (app (ev, I, rap),
			app (app (ev, I, rap),
			    ap (appp (rLR, t, ev, lr),
                                    app (Index, Zero, lsd)),
		            ap (appp (rLR, t, ev, lr),
                                  app (Index, ap(Suc,ap(Suc,Zero)), lsd))),
			app (app (ev, I, rap),
			    ap (appp (rLR, t, ev, lr),
                                   app (Index, ap(Suc,Zero), lsd)),
			    ap (appp (rLR, t, ev, lr),
                                  app (Index, ap(Suc,ap(Suc,Zero)), lsd))))
				  ) )))));

	fExt1 = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_Ext1), rep(r_Ext1)) 
			    ) ))))); 

	fExt2 = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_Ext2), rep(r_Ext2)) 
			    ) ))))); 

	fExt3 = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_Ext3), rep(r_Ext3)) 
			    ) ))))); 

	fExt4 = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_Ext4), rep(r_Ext4)) 
			    ) ))))); 

	fExt5 = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_Ext5), rep(r_Ext5)) 
			    ) ))))); 

	fExt6 = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_Ext6), rep(r_Ext6)) 
			    ) ))))); 

		    
	/* AE: SEI=KI */
	fAE = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
		ap (appp (rLR, t, ev, lr),
		    app (lr, app (rap, app (rap, rS, rE), rI), 
			     app (rap, rK, rI) ) ) )))));

        /* Eab=I -> a=b */
        fEA = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
            /* Eab */ LET (x1, ap (appp (rLR, t, KI, K), 
                                   app (Index, Zero, lsd)),
            /* I */   LET (x2, ap (appp (rLR, t, KI, KI),
                                   app (Index, Zero, lsd)),
             app (app (EqDem, x2, rI),
                 app (app (Eqn, ap (Nod, x1), nap), 
                      app (app (Eqn, ap (Nod, ap (fnc, x1)), nap),
                           app (app (Eqn, ap (Nod, ap (fnc, ap (fnc, x1))),
                                     nE),
                                ap (appp (rLR, t, ev, lr), 
                                    app (lr, ap (arg, ap (fnc, x1)),
                                             ap (arg, x1) ) ),
                                app (ev, I, rI)),
                           app (ev, I, rI)),
                      app (ev, I, rI)),
                 app (ev, I, rI) ) ) ) )))));

        /* If I = I */
	fMP = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
              ap (appp (rLR, t, ev, lr), 
                  app (lr, app (rap, rIf, rI), rI) ) )))));

        /* S If I = K I */
	fAI = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
              ap (appp (rLR, t, ev, lr),
                  app (lr, app (rap, app (rap, rS, rIf), rI),
                           app (rap, rK, rI) ) ) )))));

        /* S (K (S If)) If = K (K I) */
	fAK = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
              ap (appp (rLR, t, ev, lr),
                  app (lr, 
                      app (rap, app (rap, rS, 
                       app (rap, rK, app (rap, rS, rIf))
                       ), rIf),              
                      app (rap, rK, app (rap, rK, rI)) ) ) )))));

        /* l_AS = K (K (K I)) */
	fAS = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
              ap (appp (rLR, t, ev, lr),
                  app (lr, rep (l_AS), 
                           app (rap, rK, app (rap, rK, 
				app (rap, rK, rI))) ) ) )))));

        /* l_RPA = K I */
	fRPA = lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
               ap (appp (rLR, t, ev, lr),
                   app (lr, rep (l_RPA),
                            app (rap, rK, rI) ) ) )))));

	fZeroIsOrd = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_ZeroIsOrd), rep(r_ZeroIsOrd)) 
			    ) )))));

	fSucIsOrd = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_SucIsOrd), rep(r_SucIsOrd)) 
			    ) )))));

	fLimIsOrd = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_LimIsOrd), rep(r_LimIsOrd)) 
			    ) )))));

	fPredIsOrd = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_PredIsOrd), rep(r_PredIsOrd)) 
			    ) )))));

	fStepIsOrd = lambda (rLR, lambda (t, lambda (ev, lambda (lr, 
			lambda (lsd,
			ap (appp (rLR, t, ev, lr),
			    app (lr, rep (l_StepIsOrd), rep(r_StepIsOrd)) 
			    ) ))))); 
	
	rfI = rep (fI);
	rfK = rep (fK);
	rfS = rep (fS);
	rfE = rep (fE);
	rfIf = rep (fIf);
        rfOrd = rep (fOrd);
	rfap = rep (fap);
	rftransym = rep (ftransym);
	rfdefI = rep (fdefI);
	rfdefK = rep (fdefK);
	rfdefS = rep (fdefS);
	rfExt1 = rep (fExt1);
	rfExt2 = rep (fExt2);
	rfExt3 = rep (fExt3);
	rfExt4 = rep (fExt4);
	rfExt5 = rep (fExt5);
	rfExt6 = rep (fExt6);
	rfAE = rep (fAE);
	rfEA = rep (fEA);
	rfMP = rep (fMP);
	rfAI = rep (fAI);
	rfAK = rep (fAK);
	rfAS = rep (fAS);
	rfRPA = rep (fRPA);
	rfZeroIsOrd = rep (fZeroIsOrd);
	rfSucIsOrd = rep (fSucIsOrd);
        rfLimIsOrd = rep (fLimIsOrd);
        rfPredIsOrd = rep (fPredIsOrd);
	rfStepIsOrd = rep (fStepIsOrd);

	t0 = ap (Ins, app (MkRule, Zero, rfI /*(rep(fI)*/),
	     ap (Ins, app (MkRule, Zero, rfK),
	     ap (Ins, app (MkRule, Zero, rfS),
	     ap (Ins, app (MkRule, Zero, rfE),
	     ap (Ins, app (MkRule, Zero, rfIf),
      ap (Ins, app (MkRule, Zero, rfOrd),
	     ap (Ins, app (MkRule, ap (Suc, ap (Suc, Zero)), rfap),
	     ap (Ins, app (MkRule, ap (Suc, ap (Suc, Zero)), rftransym),
	     ap (Ins, app (MkRule, ap (Suc, Zero), rfdefI),
	     ap (Ins, app (MkRule, ap (Suc, ap (Suc, Zero)), rfdefK),
	     ap (Ins, app (MkRule, ap (Suc, ap (Suc, ap (Suc, Zero))), 
		rfdefS),
	     ap (Ins, app (MkRule, Zero, rfExt1),
	     ap (Ins, app (MkRule, Zero, rfExt2),
	     ap (Ins, app (MkRule, Zero, rfExt3),
	     ap (Ins, app (MkRule, Zero, rfExt4),
	     ap (Ins, app (MkRule, Zero, rfExt5),
	     ap (Ins, app (MkRule, Zero, rfExt6),
	     ap (Ins, app (MkRule, Zero, rfAE),
	     ap (Ins, app (MkRule, ap (Suc, Zero), rfEA),
	     ap (Ins, app (MkRule, Zero, rfMP),
	     ap (Ins, app (MkRule, Zero, rfAI), 
	     ap (Ins, app (MkRule, Zero, rfAK),
	     ap (Ins, app (MkRule, Zero, rfAS),
	     ap (Ins, app (MkRule, Zero, rfRPA),
	     ap (Ins, app (MkRule, Zero, rfZeroIsOrd),
	     ap (Ins, app (MkRule, Zero, rfSucIsOrd),
	     ap (Ins, app (MkRule, Zero, rfLimIsOrd),
	     ap (Ins, app (MkRule, Zero, rfPredIsOrd),
	     ap (Ins, app (MkRule, Zero, rfStepIsOrd),	   

	     Nil )))))))))))))))))))))))))))));

        MapDemL = lambda (t, app (MapDem, t, appp (LR, t, K, K)));
        MapDemR = lambda (t, app (MapDem, t, appp (LR, t, KI, KI)));

        /* rule Refl0 : MapDemL t0 = MapDemR t0 
           add rule Refl0 to t0 -> t1 = ap (aRefl0, t0) 
           Eval (RepTheory t) = t
         */

        /* provisoirement */
        /* RepTheory = I; */
 
        /*
            RepRep rI = rep(rI) ...
            RepRep (rap rf ra) = rap (rap rep(rap) (RepRep rf)) (RepRep ra)
            Fnc = Subdem 0, Arg = Subdem 1
         */
        RepRep = ap (Y, lambda (rRepRep, lambda (r, 
               app (app (Eqn, ap (Nod, r), nap),
                    app (rap, app (rap, rep(rap), ap (rRepRep, ap (fnc, r))),
                         ap (rRepRep, ap (arg, r)) ),
                    app (app (Eqn, ap (Nod, r), nI), rep(rI),
                    app (app (Eqn, ap (Nod, r), nK), rep(rK),
                    app (app (Eqn, ap (Nod, r), nS), rep(rS),
                    app (app (Eqn, ap (Nod, r), nE), rep(rE),
                    app (app (Eqn, ap (Nod, r), nIf), rep(rIf),
                    app (app (Eqn, ap (Nod, r), nOrd), rep (rOrd), 
                    I )))))) 
                    ) )));
   
        RepInt = ap (Y, lambda (rRepInt, lambda (n,
               app (n, rep(Zero), lambda (n1,
                   app (rap, rep(Suc), ap (rRepInt, n1)) )) )));

        RepTheory = ap (Y, lambda (rRepTheory, lambda (t,
                  app (t, rep(Nil), lambda (x, lambda (t1,
                      app (rap, app (rap, rep(Ins),
                          app (rap, app (rap, rep(MkRule), 
                              ap (RepInt, ap (x, K)) ), 
                                  ap (RepRep, ap (x, KI)) ) ),
                           ap (rRepTheory, t1) ) ))) )));

        fRefl0 = lambda (th,
                 lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
               ap (appp (rLR, t, ev, lr),
                  /* app (rap, app (rap, rMapDem, rep(t0)), app (lr, */
                  app (rap, app (lr, rep(MapDemL), rep(MapDemR)), /*rep(th)*/
                        ap (RepTheory, th) )
                  ) ))))) );
                            
        rfRefl0 = rep (fRefl0);

        /* aRefl0 = lambda (rt, app (Adl, ap(Eval,rt), app (MkRule, Zero, 
                                              app (rap, rfRefl0, rt)))); */
        aRefl0 = lambda (t, app (Adl, t, app (MkRule, Zero,
                  app (rap, rfRefl0, ap (RepTheory, t)) ))); 

        /* rule Refl : 
            Refl t0 (Ord 0 = I) = Refl0 t0 
            Refl t0 (Ord x = I) = Refl tx (Ord 0 = I) = Refl0 tx
            (x>0) tx = t0 U Refl t0 U { Ord x = I } 
            ExtractOrd d = if concl d = (Ord x = I) then x else 0
         */

        /*
        fRefl = lambda (th,
                lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
                       LET (x, ap (ExtractOrd, app (Index, Zero, lsd)),

                            if x = 0 then fRefl0 th rLR t ev lr Nil
                            else 
                                let tx = th U Refl th U { Ord x = I } in
                                fRefl0 tx rLR t ev lr Nil   
         or
                           let tx = if x = 0 then th 
                               else th U Refl th U { Ord x = I } in 
                               fRefl0 tx rLR t ev lr Nil

                           ) ))))) );

        th = t -> lambda (th, ) useless ?

        ExtractOrd ("Ord x = I") = x, Zero otherwise

        OrdZero x = K if x = 0, KI otherwise

        rfOrdx : x:Ord -> rep function of rule Ord x = I

        problem : rep_rec_fRefl = rep (rec_fRefl)
        rep_fRefl = ap (Y, lambda (rec_rep_fRefl, rlambda (rth, ...
                       rap (rap (rrap, rep_rep_rec_fRefl), rth) ...) ?

        x such that x = f r and Eval r = x 
                    Eval r = f r
        r = Y (\r1. rap rf (reprep r1)) = Y g
        r = g r = rap rf (reprep r)
        Eval r = Eval rf (Eval (reprep r)) = f r

        rule Refl t : arity 1, function fRefl t
            d -> fRefl t LR t K K ["d"] = fRefl t LR t K KI ["d"]
              
        symbols : E, If, Ord

        */

        ExtractOrd = lambda (t, lambda (d, 
            LET (a, ap (appp (LR, t, KI, K), d),
            LET (b, ap (appp (LR, t, KI, KI), d),
            app (app (EqDem, b, rI),
                 app (app (Eqn, ap (Nod, a), nap),
                      app (app (Eqn, ap (Nod, app (Subdem, Zero, a)), nOrd),
                           ap (Eval, app (Subdem, ap(Suc,Zero), a)),
                           Zero), 
                      Zero),
                 Zero) ) ) ));

        OrdZero = lambda (x, appp (x, True, ap (K, False), ap (K, False)));                    
 
        rfOrdxr = lambda (rx, 
               lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
                      ap (appp (rLR, t, ev, lr),
                         app (lr, app (rap, rOrd, rx), rI) ) ))))) );

        rep_rfOrdx = ap (Y, lambda (rec_rep_rfOrdx, 
                   app (rap, rep(rfOrdxr), ap (RepRep, rec_rep_rfOrdx)) ));

        rfOrdx = ap (Eval, rep_rfOrdx);

        /* fRefl = ap (Y, lambda (rec_fRefl, lambda (th, */

           fReflr = lambda (rep_rec_fRefl, lambda (th,
                lambda (rLR, lambda (t, lambda (ev, lambda (lr, lambda (lsd,
                       LET (x, app (ExtractOrd, th, app (Index, Zero, lsd)),
                       ap (lambda (tx, 
                          ap (appp (ap (fRefl0, tx), rLR, ev, lr), Nil)),
                          app (ap (OrdZero, x), th, 
                            app (Adl,
                              app (Adl, th, 
                                  app (MkRule, ap (Suc, Zero),
                                      app (rap, rep_rec_fRefl, th)) ),
                              app (MkRule, Zero, app (rap, rfOrdx, x)) )
                              ) ) ) ))))) ));

        rep_fRefl = ap (Y, lambda (rec_rep_fRefl, 
                  app (rap, rep(fReflr), ap (RepRep, rec_rep_fRefl)) ));

        fRefl = ap (Eval, rep_fRefl);

	
#else

#define defr(d) \
	lambda (vI, lambda (vK, lambda (vS, lambda (vE, lambda (vIf, \
	lambda (vap, lambda (vtransym, \
	lambda (vdefI, lambda (vdefK, lambda (vdefS, \
	lambda (vAE, lambda (vEA, /* lambda (vEXT, */ \
	lambda (vMP, lambda (vAI, lambda (vAK, lambda (vAS, lambda (vRPA, \
		d ))))) ))/*)*/ ))) )) )))))

#define switch_dem(d,cI,cK,cS,cE,cIf,cap,ctransym,cdefI,cdefK,cdefS,cAE,cEA,/*cEXT,*/cMP,cAI,cAK,cAS,cRPA) \
	ap (ap (ap (ap (ap (ap (ap /*(ap*/ \
	(ap (ap (ap (ap (ap (ap (ap (ap (ap (ap (d, \
	 cI), cK), cS), cE), cIf), cap), ctransym), \
	cdefI), cdefK), cdefS), cAE), cEA)/*, cEXT)*/, \
        cMP), cAI), cAK), cAS), cRPA)

        rI = defr (vI);
	rK = defr (vK);
        rS = defr (vS);
	rE = defr (vE);
        rIf = defr (vIf);

	rap = lambda (rf, lambda (ra, defr (ap (ap (vap, rf), ra))));
  	rtransym = lambda (r1, lambda (r2, 
		defr (ap (ap (vtransym, r1), r2))));
	rdefI = lambda (r, defr (ap (vdefI, r)));
	rdefK = lambda (ra, lambda (rb,
		defr (ap (ap (vdefK, ra), rb))));
	rdefS = lambda (ra, lambda (rb, lambda (rc,
		defr (ap (ap (ap (vdefS, ra), rb), rc)))));
	rAE = defr (vAE);
	rEA = lambda (r, defr (ap (vEA, r)));
	rEXT = lambda (r, defr (ap (vEXT, r)));
	rMP = defr (vMP);
	rAI = defr (vAI);
	rAK = defr (vAK);
	rAS = defr (vAS);
	rRPA = defr (vRPA);

	A = ap (ap (S, I), I);
	Y = lambda (f, ap (A, ap (ap (S, ap (K, f)), A)));

	israp = lambda (d, switch_dem (d,
		KI, KI, KI, KI, KI, ap(K,ap(K,K)), 
		ap(K,ap(K,KI)),
		ap(K,KI), ap(K,ap(K,KI)), ap(K,ap(K,ap(K,KI))),
		KI, ap(K,KI),
		KI, KI, KI, KI, KI				
		));
	isnrap = lambda (d, appp(israp,d,KI,K));

	isrI = lambda (d, switch_dem (d,
		K, KI, KI, KI, KI, ap(K,ap(K,KI)), 
		ap(K,ap(K,KI)),
		ap(K,KI), ap(K,ap(K,KI)), ap(K,ap(K,ap(K,KI))),
		KI, ap(K,KI),
		KI, KI, KI, KI, KI				
		));
	isnrI = lambda (d, appp(isrI,d,KI,K));

	isrE = lambda (d, switch_dem (d,
		KI, KI, KI, K, KI, ap(K,ap(K,KI)), 
		ap(K,ap(K,KI)),
		ap(K,KI), ap(K,ap(K,KI)), ap(K,ap(K,ap(K,KI))),
		KI, ap(K,KI),
		KI, KI, KI, KI, KI				
		));
	isnrE = lambda (d, appp(isrE,d,KI,K));

        fnc = lambda (d, switch_dem (d,
                KI, KI, KI, K, KI, lambda(rf,lambda(ra,rf)),    
		ap(K,ap(K,KI)),
		ap(K,KI), ap(K,ap(K,KI)), ap(K,ap(K,ap(K,KI))),
		KI, ap(K,KI),
		KI, KI, KI, KI, KI				
		));

        arg = lambda (d, switch_dem (d,
                KI, KI, KI, K, KI, lambda(rf,lambda(ra,ra)),    
		ap(K,ap(K,KI)),
		ap(K,KI), ap(K,ap(K,KI)), ap(K,ap(K,ap(K,KI))),
		KI, ap(K,KI),
		KI, KI, KI, KI, KI				
		));

        /* eqdem */
	eqdem = KKKI; /* provisoirement */
        
        LR_transym = lambda (r1, lambda (r2,
                                app (app(eqdem,app(vLR,K,r1),app(vLR,K,r2)),
                                        app(vLR,KI,app(lr,r1,r2)), rI)));

	LR = ap (Y, lambda (vLR,
                lambda (lr, lambda (d, switch_dem (d,
			rI, rK, rS, rE, rIf,
                        lambda (rf, lambda (ra, 
				ap (ap (rap, ap (ap (vLR, lr), rf)),
                                        ap (ap (vLR, lr), ra)) )),
                        LR_transym,
                        /*lambda (r1, lambda (r2,
                                app (app(eqdem,app(vLR,K,r1),app(vLR,K,r2)),
                                        app(vLR,KI,app(lr,r1,r2)), rI),*/
                        /*lambda (r1, lambda (r2,
				ap(ap (ap (ap (eqdem, ap(ap(vLR,K),r1)) 
					       ap(ap(vLR,K),r2)),
					ap(ap(vLR,KI),ap(ap(lr,r1),r2))),rI))),
                        */
                                                
                        lambda (a, ap (ap (lr, ap (ap (rap, rI), ap(ap(vLR,lr),a))),
						ap(ap(vLR,lr),a))),
                        lambda (a, lambda (b, ap (ap (rap, ap (ap (rap, rK), ap(ap(vLR,lr),a))),
						ap(ap(vLR,lr),b)))),
                        lambda (a, lambda (b, lambda (c,
				ap (ap (lr,
				    RAP(RAP(RAP(rS,a),b),c)				    
				),
			            RAP(RAP(a,c),RAP(b,c))
				) ))),
                        app (lr, RAPP (rS,rE, rI), RAP (rK, rI)),
                        
			lambda (d, LET(ld,ap(ap(vLR,K),d),
				   LET(rd,ap(ap(vLR,KI),d),
			 	   appp(isnrap,ld,rI,
				   appp(isnrap,ap(fnc,ld),rI,
				   appp(isnrE,ap(fnc,ap(fnc,ld)),rI,
				   appp(isnrI,rd,rI,
					app(lr,ap(arg,ap(fnc,ld)),ap(arg,ld))
					) ) ) ) ) )), 
                        
                        app (lr, RAP(rIf,rI), rI),
                        app (lr, RAPP(rS,rIf,rI), RAP(rK,rI)),
                        app (lr, RAPP(rS,RAP(rK,RAP(rS,rIf)),rIf),
					RAP(rK,RAP(rK,rI))),
                        app (lr, rep(l_AS), rep(KKKI)),
                        app (lr, rep(l_RPA), rep(KI))
                                        )))));
#endif
#endif
}







