
#include "lctm.h"

init ()
{
DEM p, q, r, u, x, f, z, s, l, a, b, c, fOrd;
char buf[10];
#ifdef ALLOC
    dems = alloc ( (MAX_DEM+1) * sizeof (struct S_DEM) );
    printf ("dems=%lp\n", dems);
#endif
    u = U(Order(0));
    a = Var ("a", u);
    b = Var ("b", u);
    c = Var ("c", u);
/*
    printf ("Defining I ...\n");
    gets (buf);
*/

#ifdef LAMBDA_DB
    I = lambda (a, a);
    K = lambda (a, lambda (b, a));
    S = lambda (a, lambda (b, lambda (c, ap (ap (a, c), ap (b, c)))));

#else
    I = mk_dem (_I, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
/*
    printf ("I defined\n");
*/
    K = mk_dem (_K, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    S = mk_dem (_S, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
#endif
    E = mk_dem (_E, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    If = mk_dem (_If, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    Ord = mk_dem (_Ord, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);

    itransym = mk_dem (_itransym, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    idefI = mk_dem (_idefI, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    idefK = mk_dem (_idefK, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    idefS = mk_dem (_idefS, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    ileft = mk_dem (_ileft, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    iright = mk_dem (_iright, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL); 
    ieq = mk_dem (_ieq, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    inode = mk_dem (_inode, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    isubdem0 = mk_dem (_isubdem0, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    isubdem1 = mk_dem (_isubdem1, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    isubdem2 = mk_dem (_isubdem2, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    ired = mk_dem (_ired, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    iredu = mk_dem (_iredu, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    iext = mk_dem (_iext, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    istep = mk_dem (_istep, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    irstep = mk_dem (_irstep, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);

    nil = mk_dem (_nil, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    subdem(0,nil) = I;
    subdem(1,nil) = nil;

    /* printf ("&SEI=%04X\n", &SEI); */
    WATCH(SEI)
    /* printf ("watch=%04X\n", watch); */
    trace_dem ("", SEI);
    SEI = ap (ap (S, E), I);
    trace_dem ("", SEI);


#ifdef LAMBDA_DB
    KI = lambda (a, lambda (b, b));
#else
    KI = ap (K, I);
#endif

#if 1
    IfI = ap (If, I);
    SIfI = ap (ap (S, If), I);
    SKSIfIf = ap ( ap (S ,ap (K , ap (S, If)) ), If);
    KKI = ap (K, KI);
    KKKI = ap (K, KKI);

#define DA(x,y) x = mk_dem (y, 0,  NULL, NULL,  NULL, NULL, NULL, NULL, NULL);

	DA(Ext1,_Ext1);
	DA(Ext2,_Ext2);
	DA(Ext3,_Ext3);
	DA(Ext4,_Ext4);
	DA(Ext5,_Ext5);
	DA(Ext6,_Ext6);

	DA(AE,_AE);
        DA(EA0,_EA0); 
	DA(MP,_MP);
	DA(AI,_AI);
	DA(AK,_AK);
	DA(AS,_AS);
	DA(RPA,_RPA);

	DA(ZeroIsOrd,_ZeroIsOrd);
	DA(SucIsOrd,_SucIsOrd);
	DA(LimIsOrd,_LimIsOrd);
	DA(PredIsOrd,_PredIsOrd);
	DA(StepIsOrd,_StepIsOrd); 
        DA(TfI,_TfI)    
        DA(dSubst,_Subst);
        DA(dDB_Subst,_DB_Subst);

    p = Var ("p", u);
    q = Var ("q", u);
    r = Var ("r", u);
    x = ap (ap (If, ap (ap (If, p), ap (ap (If, q), r))),
                ap (ap (If, ap (ap (If, p), q)),
                            ap (ap (If, p), r))
                );
    l_AS = lambda (p, lambda (q, lambda (r, x)));
    print_string (print_param, "l_AS = ");
    print_dem (print_param, l_AS);
    print_string (print_param, "\n");
    Fa = KKI;

    x = ap (ap (If, ap (ap (If, ap (ap (If, p), Fa)), Fa)), p);
    l_RPA = lambda (p, x);

    l_EA0 = lambda (a, lambda (b, appp (E, app (E, a, b), I, a))); 
    r_EA0 = lambda (a, lambda (b, appp (E, app (E, a, b), I, b)));

    x = Var ("x", U(Order(0)));
    f = Var ("f", U(Order(0)));
    z = Var ("z", U(Order(0)));
    s = Var ("s", U(Order(0)));
    l = Var ("l", U(Order(0)));

    ZeroOrd = lambda (z, lambda (s, lambda (l, z)));
    SucOrd = lambda (x, lambda (z, lambda (s, lambda (l, ap (s, x)))));
    LimOrd = lambda (f, lambda (z, lambda (s, lambda (l, ap (l, f)))));

    /* Ord ZeroOrd */
    l_ZeroIsOrd = ap (Ord, ZeroOrd);
    r_ZeroIsOrd = I;

    /* All x. (Ord x => Ord (SucOrd x)) */
    l_SucIsOrd = lambda (x, app (If, ap (Ord, x), ap (Ord, ap (SucOrd, x))));
    r_SucIsOrd = KI;

    /* All f. (All x. (Ord x => Ord (f x))) => Ord (LimOrd f)) */
    l_LimIsOrd = lambda (f, app (If, app (E, 
	lambda (x, app (If, ap (Ord, x), ap (Ord, ap (f, x)))), KI),
	ap (Ord, ap (LimOrd, f)) ));
    r_LimIsOrd = KI;

    /* All x. (Ord (SucOrd x) => Ord x) */
    l_PredIsOrd = lambda (x, app (If, ap (Ord, ap (SucOrd, x)), ap (Ord, x)));
    r_PredIsOrd = KI;

    /* All f. All x. (Ord (Lim f) => Ord x => Ord (f x)) */
    l_StepIsOrd = lambda (f, lambda (x, app (If, ap (Ord, ap (LimOrd, f)),
	app (If, ap (Ord, x), ap (Ord, ap (f, x))) )));
    r_StepIsOrd = KKI; 

    /* Transfinite induction :
        All p. ( ((p 0) &
                  (All x.(p x => p (Suc x))) &
                  (All f.((All x.(Ord x => p (f x))) => p (Lim f))) )
              => (All x.(Ord x => p x) )
     */
    fOrd = lambda (f, app (E, lambda (x,
                app (If, ap (Ord, x), ap (Ord, ap (f, x))) ), KI));
    l_TfI = lambda (p, app (If, ap (p, ZeroOrd),
                                app (If,
                                 app (E, lambda (x,
                                      app(If,ap(p,x),ap(p,ap(SucOrd,x)))
                                                ),
                                      KI
                                     ),
                                  app (If,
                                   app (E, lambda (f,
                                                  app(If,/*ap(fOrd,f),*/
                                                   app (E, lambda (x,
                                                    app (If, ap (Ord, x), ap (/*Ord*/p, ap (f, x))) ), KI),
                                                       ap(p,ap(LimOrd,f))
                                                     )
                                                  ), KI
                                       ),
                                   app (E,
                                        lambda(x, app(If,ap(Ord,x),ap(p,x))),
                                        KI
                                       )
                                      )
                                     )
                             ));
    r_TfI = KI;


    /* Extensionality :

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

#if 1
    /* Ext_I */
    l_Ext1 = ap (S, ap (K, I));
    r_Ext1 = I;

    /* Ext_K : \xyu.K(xu)(yu) = \xyu.xu */                 
    l_Ext2 = app(S,ap(K,S),ap(S,ap(K,K)));
    r_Ext2 = K;

    /* Ext_S : \xyzu.S(xu)(yu)(zu) = \xyzu.xu(zu)(yu(zu)) */
    l_Ext3 = app(S,ap(K,ap(S,ap(K,S))),app(S,ap(K,S),ap(S,ap(K,S))));
    r_Ext3 = app(S,app(S,ap(K,S),app(S,ap(K,K),app(S,ap(K,S),
              app(S,ap(K,ap(S,ap(K,S))),S)))),ap(K,S));

/*
    r_Ext3 = app(S,app(S,ap(K,S),app(S,ap(K,K),app(S,ap(K,S),
              app(S,ap(K,S),app(S,ap(K,ap(S,ap(K,S))),S))))),p(K,S));
*/

    /* Ax_1 : S(Kf)I = f */
    l_Ext4 = app(S,app(S,ap(K,S),K),ap(K,I));
    r_Ext4 = I;

    /* Ax_2 : S(Kx)(Ky) = K(xy) */
    l_Ext5 = app(S,app(S,ap(K,S),app(S,ap(K,K),app(S,ap(K,S),K))),ap(K,K));
    r_Ext5 = ap(S,ap(K,K));

    l_Ext6 = I;
    r_Ext6 = I;
#else
    /*	K = S(S(KS)(S(KK)K))(K(SKK))                            
		= \xy.Kxy */
    l_Ext1 = K;
    r_Ext1 = app (S, app (S, ap (K, S), app (S, ap (K, K), K)), ap (K, 
		    app (S, K, K)));
    
    /*	S = S(S(KS)(S(K(S(KS)))(S(K(S(KK)))S)))(K(K(SKK)))
		= \xyz.Sxyz */
    l_Ext2 = S;
    r_Ext2 = app(S,app(S,ap(K,S),app(S,ap(K,ap(S,ap(K,S))),
        app(S,ap(K,ap(S,ap(K,K))),S) )),ap(K,ap(K,I)) );
 
    /*	S(S(KS)(S(KK)(S(KS)K)))(KK) = S(KK)
		\xy.S(Kx)(Ky) = \xy.K(xy) */
    l_Ext3 = app(S,app(S,ap(K,S),app(S,ap(K,K),app(S,ap(K,S),K))),ap(K,K));
    r_Ext3 = ap(S,ap(K,K));

    /*	S(KS)(S(KK)) = S(KK)(S(S(KS)(S(KK)(SKK)))(K(SKK)))
		\xyu.K(xu)(yu) = \xyu.xu */
    l_Ext4 = app(S,ap(K,S),ap(S,ap(K,K)));
    r_Ext4 = app(S,ap(K,K),app(S,app(S,ap(K,S),app(S,ap(K,K),I)),ap(K,I)));

    /*	S(K(S(KS)))(S(KS)(S(KS))) = S(S(KS)(S(KK)(S(KS)(S(K(S(KS)))S))))(KS)
		\xyzu.S(xu)(yu)(zu) = \xyzu.(xu)(zu)((yu)(zu)) */
    l_Ext5 = app(S,ap(K,ap(S,ap(K,S))),app(S,ap(K,S),ap(S,ap(K,S))));
    r_Ext5 = app(S,app(S,ap(K,S),
                       app(S,ap(K,K),app(S,ap(K,S),
                       app(S,ap(K,ap(S,ap(K,S))),S) ))),ap(K,S));

    /*	S(S(KS)K)(K(SKK)) = SKK
		\f.S(Kf)I = \f.f */
    l_Ext6 = app(S,app(S,ap(K,S),K),ap(K,I));
    r_Ext6 = I;
#endif  
    init_refl ();

    Ord = mk_dem (_Ord, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    Zero = mk_dem (_Zero, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    Suc = mk_dem (_Suc, 0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
    Lim = mk_dem (_Lim,  0, NULL, NULL,  NULL, NULL, NULL, NULL, NULL);
#endif

}
