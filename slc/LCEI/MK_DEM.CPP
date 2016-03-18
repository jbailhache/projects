
#include "lctm.h"

char far *add_ptr (char far *p, long i)
{
#ifndef CPP
int seg, off;
union
{
   long x;
   struct { int l; int h; } lh;
} u;
char far *p1;
   
    seg = FP_SEG(p);
    off = FP_OFF(p);
    u.x = off + i;
    off = u.lh.l;
    seg += u.lh.h << 12;
    p1 = MK_FP (seg, off);
    return p1;
#endif
}

#ifdef ALLOC
/* #define ADD_PTR(p,i) ((p)+(i)) */
#define ADD_PTR(p,i) (DEM)add_ptr(p,i*sizeof(*p))
#else
#define ADD_PTR(p,i) ((DEM)((p)+(i)))
#endif

#ifdef ALLOC
#define IND(p,i) (*(ADD_PTR(p,i)))
#else
#define IND(p,i) p[i]
#endif

int farstrncmp (char far *s1, char *s2, int n)
{
int i;
    for (i=0; i<n; i++)
    {
        /* printf ("\ni=%d s1[i]=%c s2[i]=%c ",i, s1[i], s2[i]); */
        if (s1[i] == 0)
            if (s2[i] == 0)
                return 0;
            return s1[i]-s2[i];
        if (s2[i] == 0)
            return s1[i]-s2[i];
        if (s1[i] != s2[i])
            return s1[i]-s2[i];
    }
    return 0;
}

/*
int farstrcmp (char far *s1, char *s2)
{
int x;
    x = farstrcmp1 (s1, s2);
    printf ("\nfarstrcmp -> %d\n", x);
    return x;
}
*/
DEM mk_dem (NODE node_, ORDER order_, char *name_1,
    DEM sd0, DEM sd1, DEM sd2, DEM sd3, DEM sd4, DEM sd5) 
{
int i, j, order1;
NODE node1;
char *name_;
DEM d;
    if (name_1 == NULL)
        name_ = "";
    else
        name_ = name_1;
    for (i=0; i<n_dem; i++)
    {
/*
#ifdef TRACE
        if (dems[i]._name != NULL && name_ != NULL && dems[i]._name[0])
        printf ("%d <%s> <%s>\n",
                strcmp(dems[i]._name, name_), dems[i]._name, name_);
#endif
*/
#if 1

#if 1
        d = ADD_PTR(dems,i);

#ifdef TRACE
        /* fprintf (stderr, "\nname(d)=<%s>\nname_=<%s>", name(d), name_); */
#endif
        if (node(d) == node_ &&
            order(d) == order_ &&
            ((node(d) != _Sym && node(d) != _Var) ||
             name(d) == name_ || !
#ifdef ALLOC
                                             farstrncmp
#else
                                             strncmp
#endif
                                                        (name(d), name_, sizeof(d->_buf)-1)) &&
            (node_ == _Sym ||
             subdem(0,d) == sd0) &&
             subdem(1,d) == sd1 &&
             subdem(2,d) == sd2)
                return d; 
    }
    if (n_dem >= MAX_DEM)
    {
        fprintf (stderr, "Insufficient memory (%d)\n", n_dem);
#ifdef CPP
#else
        exit (0);
#endif
    }
    i = n_dem;
    d = ADD_PTR(dems,i);
    node(d) = node_;
    order(d) = order_;
/*
    IND(dems,i)._name = name_;
*/
#ifdef NAME
    name(d) = IND(dems,i)._buf;
#endif
    /* strncpy (IND(dems,i)._buf, name_, sizeof(IND(dems,i)._buf)); */
    for (j=0; j<sizeof(IND(dems,i)._buf); j++)
    {
#ifdef TRACE1
        printf ("\ni=%d j=%d name_[j]=%c ", i, j, name_[j]);
#endif
        d->_buf[j] = name_[j];
        if (name_[j] == 0)
                break;
#ifdef TRACE1
        printf ("IND(dems,i)._buf[j]=%c ", IND(dems,i)._buf[j]);
#endif
    }
#ifdef TRACE1
    printf ("\nname_=<%s>", name_);
    printf ("\n_buf=<%s>\n", IND(dems,i)._buf);
    printf ("_buf[0]=%c\n", IND(dems,i)._buf[0]);
#endif
    d->_buf[sizeof(IND(dems,i)._buf)-1] = 0;

    d->_left = NULL;
    d->_right = NULL;
    d->_red[0] = NULL;
    d->_red[1] = NULL;
    subdem(0,d) = sd0;
    subdem(1,d) = sd1;
    subdem(2,d) = sd2;
/*
    IND(dems,i)._subdem[3] = sd3;
    IND(dems,i)._subdem[4] = sd4;
    IND(dems,i)._subdem[5] = sd5;
*/
    n_dem++;
    if (node_ == _Sym && !strcmp (name_, "watch"))
    {
        WATCH (IND(dems,i)._subdem[0])
    }
    return d; 

#else
        if (IND(dems,i)._node == node_ &&
            IND(dems,i)._order == order_ &&
            (IND(dems,i)._name == name_ || !
#ifdef ALLOC
                                             farstrcmp
#else
                                             strcmp
#endif
                                                        (IND(dems,i)._name, name_)) &&
            (node_ == _Sym ||
             IND(dems,i)._subdem[0] == sd0) &&
            IND(dems,i)._subdem[1] == sd1 &&
            IND(dems,i)._subdem[2] == sd2)
                return ADD_PTR(dems,i);
    }
    if (n_dem >= MAX_DEM)
    {
        fprintf (stderr, "Insufficient memory (%d)\n", n_dem);
        exit (0);
    }
    i = n_dem;
    IND(dems,i)._node = node_;
    IND(dems,i)._order = order_;
/*
    IND(dems,i)._name = name_;
*/
    IND(dems,i)._name = IND(dems,i)._buf;
    /* strncpy (IND(dems,i)._buf, name_, sizeof(IND(dems,i)._buf)); */
    for (j=0; j<sizeof(IND(dems,i)._buf); j++)
    {
#ifdef TRACE1
        printf ("\ni=%d j=%d name_[j]=%c ", i, j, name_[j]);
#endif
        IND(dems,i)._buf[j] = name_[j];
        if (name_[j] == 0)
                break;
#ifdef TRACE1
        printf ("IND(dems,i)._buf[j]=%c ", IND(dems,i)._buf[j]);
#endif
    }
#ifdef TRACE1
    printf ("\nname_=<%s>", name_);
    printf ("\n_buf=<%s>\n", IND(dems,i)._buf);
    printf ("_buf[0]=%c\n", IND(dems,i)._buf[0]);
#endif
    IND(dems,i)._buf[sizeof(IND(dems,i)._buf)-1] = 0;

    IND(dems,i)._left = NULL;
    IND(dems,i)._right = NULL;
    IND(dems,i)._subdem[0] = sd0;
    IND(dems,i)._subdem[1] = sd1;
    IND(dems,i)._subdem[2] = sd2;
/*
    IND(dems,i)._subdem[3] = sd3;
    IND(dems,i)._subdem[4] = sd4;
    IND(dems,i)._subdem[5] = sd5;
*/
    n_dem++;
    if (node_ == _Sym && !strcmp (name_, "watch"))
    {
        WATCH (IND(dems,i)._subdem[0])
    }
    return ADD_PTR(dems,i);
#endif
#else
#if 1
        if (dems[i]._node == node_ &&
            dems[i]._order == order_ &&
            (dems[i]._name == name_ || !farstrcmp (dems[i]._name, name_)) &&
            (node_ == _Sym ||
             dems[i]._subdem[0] == sd0) &&
            dems[i]._subdem[1] == sd1 &&
            dems[i]._subdem[2] == sd2)
            /*
            dems[i]._subdem[3] == sd3 &&
            dems[i]._subdem[4] == sd4 &&
            dems[i]._subdem[5] == sd5)
            */
                return dems+i;

#else
        if (dems[i]._node != node_)
            goto new;
        if (dems[i]._Order != order_)
            goto new;
        if (farstrcmp (dems[i]._name, name_))
        {
            printf ("dif\n");
            goto new;
        }
        if (node != _Sym && dems[i]._subdem[0] != sd0)
            goto new;
        if (dems[i]._subdem[1] != sd1)
            goto new;
        return dems+i;

        new: ;
#endif
	/*
	node1 = dems[i].node;
        order1 = dems[i].order;
        if (node1 == node &&
            order1 == order &&
	    !strcmp (dems[i].name, name) &&
            dems[i].subdem[0] == sd0 &&
            dems[i].subdem[1] == sd1 &&
            dems[i].subdem[2] == sd2 &&
            dems[i].subdem[3] == sd3 &&
            dems[i].subdem[4] == sd4 &&
            dems[i].subdem[5] == sd5)
                return dems+i;
	*/
    }
    if (n_dem >= MAX_DEM)
    {
        fprintf (stderr, "Insufficient memory (%d)\n", n_dem);
        exit (0);
    }
    i = n_dem;
    dems[i]._node = node_;
    dems[i]._order = order_;
/*
    dems[i]._name = name_;
*/
    dems[i]._name = dems[i]._buf;
    /* strncpy (dems[i]._buf, name_, sizeof(dems[i]._buf)); */
    for (j=0; j<sizeof(dems[i]._buf); j++)
    {
#ifdef TRACE1
        printf ("\ni=%d j=%d name_[j]=%c ", i, j, name_[j]);
#endif
        dems[i]._buf[j] = name_[j];
        if (name_[j] == 0)
                break;
#ifdef TRACE1
        printf ("dems[i]._buf[j]=%c ", dems[i]._buf[j]);
#endif
    }
#ifdef TRACE1
    printf ("\nname_=<%s>", name_);
    printf ("\n_buf=<%s>\n", dems[i]._buf);
    printf ("_buf[0]=%c\n", dems[i]._buf[0]);
#endif
    dems[i]._buf[sizeof(dems[i]._buf)-1] = 0;

    dems[i]._left = NULL;
    dems[i]._right = NULL;
    dems[i]._subdem[0] = sd0;
    dems[i]._subdem[1] = sd1;
    dems[i]._subdem[2] = sd2;
/*
    dems[i]._subdem[3] = sd3;
    dems[i]._subdem[4] = sd4;
    dems[i]._subdem[5] = sd5;
*/
    n_dem++;
    if (node_ == _Sym && !strcmp (name_, "watch"))
    {
        WATCH (dems[i]._subdem[0])
    }
    return dems+i;
#endif
}

