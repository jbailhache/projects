
#include "lctm.h"

int flags = 0;

#ifdef ALLOC
struct S_DEM far *dems;
#else
struct S_DEM dems[MAX_DEM];
#endif

int n_dem = 0;

DEM I, K, S, E, If,
        itransym, idefI, idefK, idefS,
        ileft, iright, ieq, inode, isubdem0, isubdem1, isubdem2,
        ired, iredu, iext, istep, irstep,
        nil,
	Ext1, Ext2, Ext3, Ext4, Ext5, Ext6,
        AE, EA0, MP, AI, AK, AS, RPA,
        ZeroIsOrd, SucIsOrd, LimIsOrd, PredIsOrd, StepIsOrd, TfI, dSubst,
        dDB_Subst,
        SEI, KI, IfI, SIfI, SKSIfIf, KKI, l_AS, KKKI, Fa, l_RPA,
        Ord, Zero, Suc, Lim,
	l_ZeroIsOrd, l_SucIsOrd, l_LimIsOrd, l_PredIsOrd, l_StepIsOrd,
        r_ZeroIsOrd, r_SucIsOrd, r_LimIsOrd, r_PredIsOrd, r_StepIsOrd,
        l_TfI, r_TfI,
	l_Ext1, l_Ext2, l_Ext3, l_Ext4, l_Ext5, l_Ext6,
	r_Ext1, r_Ext2, r_Ext3, r_Ext4, r_Ext5, r_Ext6,
         l_EA0, r_EA0,
	ZeroOrd, SucOrd, LimOrd;

int arity [] = { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,  0, 0,
    2,  2,       1,    2,    3, 2 };

struct
#ifdef CPP
        print_param
#else
        print_param_file
#endif
                print_param[1];

void global (void)
{
}

