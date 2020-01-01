
#define MAX_NEW_CONS 120

#define UNDEF 0x7FFD
#define VAR 0x7FFC

#ifdef VAR_VAL
#define mk_var(adr) (cons (VAR, *(adr)))
#else
#define mk_var(adr) (cons (VAR, expr_int ((int) adr)))
#endif

#define pl_cut_0(k) alt_process->status |= PL_STATUS_CUT

extern struct process_list *getpl();

#define pl_ccode_1(k,x) { x; }

