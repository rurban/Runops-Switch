#define PERL_NO_GET_CONTEXT
#define PERL_CORE
#include "EXTERN.h"
#include "perl.h"
#include "XSUB.h"

/* Note that Switch can only be faster if we remove the op_ppaddr
   field from OP* in op.h, and export all the pp functions. - rurban */

/* for computed GOTO's we compress the jump table to the special cases only */
#ifdef CGOTO
#define L(op) L_##op
#define SWITCH_START(OP) if (jmptbl[OP->op_type]) \
    goto *jmptbl[OP->op_type];                    \
  else                                            \
    PL_op =(*OP->op_ppaddr)(aTHX); goto L_end;
#define CASE(op, block)    L_##op: { block; } goto L_end;
#define CASE_EMPTY(NAME)   L_##NAME:
#define CASE_DEF(NAME,name)
#define SWITCH_END         L_end: ;
#else
#define SWITCH_START(OP) switch (OP->op_type) {
#define CASE(op, block)     case OP_##op: block; break;
#define CASE_EMPTY(NAME)    case OP_##NAME:
#define CASE_DEF(NAME,name) case OP_##NAME: PL_op = Perl_pp_##name(aTHX); break;
#define SWITCH_END       }
#endif

int runops_switch(pTHX)
{
    DEBUG_l(Perl_deb(aTHX_ "Entering new RUNOPS level (Runops::Switch)\n"));

#ifdef CGOTO
    /* we either jump to the label for special inlined parts, or call the pp directly */
#define NUMOPS OP_max /* sizeof(PL_ppaddr) / sizeof(PL_ppaddr[0]) */
    static void *jmptbl[NUMOPS] = {
      &&L_NULL, &&L(SCALAR), &&L(SCOPE), &&L(LINESEQ), &&L(REGCMAYBE), &&L(STUB),
      &&L(PUSHMARK), &&L(CONST), &&L(GV), &&L(STRINGIFY), &&L(AND), &&L(OR),
      &&L(COND_EXPR), &&L(NEXTSTATE), &&L(UNSTACK)
    };
#endif

    do {
#if PERL_VERSION < 13
      PERL_ASYNC_CHECK();
#endif
      if (PL_debug) {
	if (PL_watchaddr && (*PL_watchaddr != PL_watchok))
	  PerlIO_printf(Perl_debug_log,
		      "WARNING: %"UVxf" changed from %"UVxf" to %"UVxf"\n",
		      PTR2UV(PL_watchaddr), PTR2UV(PL_watchok),
		      PTR2UV(*PL_watchaddr));
#if defined(DEBUGGING) \
  && !(defined(_WIN32) || (defined(__CYGWIN__) && (__GNUC__ > 3)) || defined(AIX))
# if (PERL_VERSION > 7)
	if (DEBUG_s_TEST_) debstack();
	if (DEBUG_t_TEST_) debop(PL_op);
# else
	DEBUG_s(debstack());
	DEBUG_t(debop(PL_op));
# endif
#endif
      }

    SWITCH_START(PL_op)
      CASE(NULL,   PL_op = NORMAL )
      CASE(SCALAR, PL_op = NORMAL )
      CASE(SCOPE,   PL_op = NORMAL )
      CASE(LINESEQ, PL_op = NORMAL)
      CASE(REGCMAYBE, PL_op = NORMAL )
      CASE(STUB,
           {
             dSP;
             if (GIMME_V == G_SCALAR)
               XPUSHs(&PL_sv_undef);
             PUTBACK;
             PL_op = NORMAL;
           })
      CASE(PUSHMARK,
           PUSHMARK(PL_stack_sp);
           PL_op = NORMAL)
      CASE(CONST,
           {
             dSP; XPUSHs(cSVOP_sv); PUTBACK; PL_op = NORMAL;
           })
      CASE(GV,
           {
             dSP;
             XPUSHs((SV*)cGVOP_gv);
             PUTBACK;
             PL_op = NORMAL;
           })
      CASE(STRINGIFY,
           {
             dSP; dTARGET;
             sv_copypv(TARG,TOPs);
             SETTARG;
             PUTBACK;
             PL_op = NORMAL;
           })
      CASE(AND,
           {
             dSP;
             if (!SvTRUE(TOPs)) {
               PUTBACK;
               PL_op = NORMAL;
             }
             else {
               --SP;
               PUTBACK;
               PL_op = cLOGOP->op_other;
             }
           })
      CASE(OR,
           {
             dSP;
             if (SvTRUE(TOPs)) {
               PUTBACK;
               PL_op = NORMAL;
             }
             else {
               --SP;
               PUTBACK;
               PL_op = cLOGOP->op_other;
             }
           })
      CASE(COND_EXPR,
           {
             dSP;
             if (SvTRUE(POPs)) {
               PUTBACK; PL_op = cLOGOP->op_other;
             } else {
               PUTBACK; PL_op = cLOGOP->op_next;
             }
           })
      CASE(NEXTSTATE,
           {
             PL_curcop = (COP*)PL_op;
             TAINT_NOT;		/* Each statement is presumed innocent */
             PL_stack_sp = PL_stack_base + cxstack[cxstack_ix].blk_oldsp;
             FREETMPS;
             PL_op = NORMAL;
           })
#if PERL_VERSION >= 13
      CASE(UNSTACK,
           {
             I32 oldsave;
             TAINT_NOT;		/* Each statement is presumed innocent */
             PL_stack_sp = PL_stack_base + cxstack[cxstack_ix].blk_oldsp;
             FREETMPS;
             if (!(PL_op->op_flags & OPf_SPECIAL)) {
               oldsave = PL_scopestack[PL_scopestack_ix - 1];
               LEAVE_SCOPE(oldsave);
             }
             PL_op = NORMAL;
           })
#else
      CASE(UNSTACK,
           {
             I32 oldsave;
             TAINT_NOT;		/* Each statement is presumed innocent */
             PL_stack_sp = PL_stack_base + cxstack[cxstack_ix].blk_oldsp;
             FREETMPS;
             if (!(PL_op->op_flags & OPf_SPECIAL)) {
               oldsave = PL_scopestack[PL_scopestack_ix - 1];
               LEAVE_SCOPE(oldsave);
             }
             oldsave = PL_scopestack[PL_scopestack_ix - 1];
             LEAVE_SCOPE(oldsave);
             PL_op = NORMAL;
           })
#endif

      /* from here on only regular cases */
      CASE_DEF(GVSV, gvsv)
      CASE_DEF(WANTARRAY, wantarray)
      CASE_DEF(GELEM, gelem)
      CASE_DEF(PADSV, padsv)
      CASE_DEF(PADAV, padav)
      CASE_DEF(PADHV, padhv)
      CASE_DEF(PADANY, padany)
      CASE_DEF(PUSHRE, pushre)
      CASE_DEF(RV2GV, rv2gv)
      CASE_DEF(RV2SV, rv2sv)
      CASE_DEF(AV2ARYLEN, av2arylen)
      CASE_DEF(RV2CV, rv2cv)
      CASE_DEF(ANONCODE, anoncode)
      CASE_DEF(PROTOTYPE, prototype)
      CASE_DEF(REFGEN, refgen)
      CASE_DEF(SREFGEN, srefgen)
      CASE_DEF(REF, ref)
      CASE_DEF(BLESS, bless)
      CASE_DEF(BACKTICK, backtick)
      CASE_DEF(GLOB, glob)
      CASE_DEF(READLINE, readline)
      CASE_DEF(RCATLINE, rcatline)
      CASE_DEF(REGCRESET, regcreset)
      CASE_DEF(REGCOMP, regcomp)
      CASE_DEF(MATCH, match)
      CASE_DEF(QR, qr)
      CASE_DEF(SUBST, subst)
      CASE_DEF(SUBSTCONT, substcont)
      CASE_DEF(TRANS, trans)
      CASE_DEF(SASSIGN, sassign)
      CASE_DEF(AASSIGN, aassign)
      CASE_DEF(CHOP, chop)
      CASE_DEF(SCHOP, schop)
      CASE_DEF(CHOMP, chomp)
      CASE_DEF(SCHOMP, schomp)
      CASE_DEF(DEFINED, defined)
      CASE_DEF(UNDEF, undef)
      CASE_DEF(STUDY, study)
      CASE_DEF(POS, pos)
      CASE_DEF(PREINC, preinc)
      CASE_DEF(I_PREINC, i_preinc)
      CASE_DEF(PREDEC, predec)
      CASE_DEF(I_PREDEC, i_predec)
      CASE_DEF(POSTINC, postinc)
      CASE_DEF(I_POSTINC, i_postinc)
      CASE_DEF(POSTDEC, postdec)
      CASE_DEF(I_POSTDEC, i_postdec)
      CASE_DEF(POW, pow)
      CASE_DEF(MULTIPLY, multiply)
      CASE_DEF(I_MULTIPLY, i_multiply)
      CASE_DEF(DIVIDE, divide)
      CASE_DEF(I_DIVIDE, i_divide)
      CASE_DEF(MODULO, modulo)
      CASE_DEF(I_MODULO, i_modulo)
      CASE_DEF(REPEAT, repeat)
      CASE_DEF(ADD, add)
      CASE_DEF(I_ADD, i_add)
      CASE_DEF(SUBTRACT, subtract)
      CASE_DEF(I_SUBTRACT, i_subtract)
      CASE_DEF(CONCAT, concat)
      CASE_DEF(LEFT_SHIFT, left_shift)
      CASE_DEF(RIGHT_SHIFT, right_shift)
      CASE_DEF(LT, lt)
      CASE_DEF(I_LT, i_lt)
      CASE_DEF(GT, gt)
      CASE_DEF(I_GT, i_gt)
      CASE_DEF(LE, le)
      CASE_DEF(I_LE, i_le)
      CASE_DEF(GE, ge)
      CASE_DEF(I_GE, i_ge)
      CASE_DEF(EQ, eq)
      CASE_DEF(I_EQ, i_eq)
      CASE_DEF(NE, ne)
      CASE_DEF(I_NE, i_ne)
      CASE_DEF(NCMP, ncmp)
      CASE_DEF(I_NCMP, i_ncmp)
      CASE_DEF(SLT, slt)
      CASE_DEF(SGT, sgt)
      CASE_DEF(SLE, sle)
      CASE_DEF(SGE, sge)
      CASE_DEF(SEQ, seq)
      CASE_DEF(SNE, sne)
      CASE_DEF(SCMP, scmp)
      CASE_DEF(BIT_AND, bit_and)
      CASE_DEF(BIT_XOR, bit_xor)
      CASE_DEF(BIT_OR, bit_or)
      CASE_DEF(NEGATE, negate)
      CASE_DEF(I_NEGATE, i_negate)
      CASE_DEF(NOT, not)
      CASE_DEF(COMPLEMENT, complement)
      CASE_DEF(ATAN2, atan2)
      CASE_DEF(SIN, sin)
      CASE_DEF(COS, cos)
      CASE_DEF(RAND, rand)
      CASE_DEF(SRAND, srand)
      CASE_DEF(EXP, exp)
      CASE_DEF(LOG, log)
      CASE_DEF(SQRT, sqrt)
      CASE_DEF(INT, int)
      CASE_DEF(HEX, hex)
      CASE_DEF(OCT, oct)
      CASE_DEF(ABS, abs)
      CASE_DEF(LENGTH, length)
      CASE_DEF(SUBSTR, substr)
      CASE_DEF(VEC, vec)
      CASE_DEF(INDEX, index)
      CASE_DEF(RINDEX, rindex)
      CASE_DEF(SPRINTF, sprintf)
      CASE_DEF(FORMLINE, formline)
      CASE_DEF(ORD, ord)
      CASE_DEF(CHR, chr)
      CASE_DEF(CRYPT, crypt)
      CASE_DEF(UCFIRST, ucfirst)
      CASE_DEF(LCFIRST, lcfirst)
      CASE_DEF(UC, uc)
      CASE_DEF(LC, lc)
      CASE_DEF(QUOTEMETA, quotemeta)
      CASE_DEF(RV2AV, rv2av)
#if PERL_VERSION >= 15
      CASE_EMPTY(AELEMFAST_LEX)
#endif
      CASE_DEF(AELEMFAST, aelemfast)
      CASE_DEF(AELEM, aelem)
      CASE_DEF(ASLICE, aslice)
      CASE_DEF(EACH, each)
      CASE_DEF(VALUES, values)
      CASE_DEF(KEYS, keys)
      CASE_DEF(DELETE, delete)
      CASE_DEF(EXISTS, exists)
      CASE_DEF(RV2HV, rv2hv)
      CASE_DEF(HELEM, helem)
      CASE_DEF(HSLICE, hslice)
      CASE_DEF(UNPACK, unpack)
      CASE_DEF(PACK, pack)
      CASE_DEF(SPLIT, split)
      CASE_DEF(JOIN, join)
      CASE_DEF(LIST, list)
      CASE_DEF(LSLICE, lslice)
      CASE_DEF(ANONLIST, anonlist)
      CASE_DEF(ANONHASH, anonhash)
      CASE_DEF(SPLICE, splice)
      CASE_DEF(PUSH, push)
      CASE_DEF(POP, pop)
      CASE_DEF(SHIFT, shift)
      CASE_DEF(UNSHIFT, unshift)
      CASE_DEF(SORT, sort)
      CASE_DEF(REVERSE, reverse)
      CASE_EMPTY(MAPSTART)
      CASE_DEF(GREPSTART, grepstart)
      CASE_DEF(GREPWHILE, grepwhile)
      CASE_DEF(MAPWHILE, mapwhile)
      CASE_DEF(RANGE, range)
      CASE_DEF(FLIP, flip)
      CASE_DEF(FLOP, flop)
      CASE_DEF(XOR, xor)
      CASE_DEF(ANDASSIGN, andassign)
      CASE_DEF(ORASSIGN, orassign)
      CASE_DEF(METHOD, method)
      CASE_DEF(ENTERSUB, entersub)
      CASE_DEF(LEAVESUB, leavesub)
      CASE_DEF(LEAVESUBLV, leavesublv)
      CASE_DEF(CALLER, caller)
      CASE_DEF(WARN, warn)
      CASE_DEF(DIE, die)
      CASE_DEF(RESET, reset)
      CASE_DEF(DBSTATE, dbstate)
      CASE_DEF(ENTER, enter)
      CASE_DEF(LEAVE, leave)
      CASE_DEF(ENTERITER, enteriter)
      CASE_DEF(ITER, iter)
      CASE_DEF(ENTERLOOP, enterloop)
      CASE_DEF(LEAVELOOP, leaveloop)
      CASE_DEF(RETURN, return)
      CASE_DEF(LAST, last)
      CASE_DEF(NEXT, next)
      CASE_DEF(REDO, redo)
      CASE_DEF(DUMP, dump)
      CASE_DEF(GOTO, goto)
      CASE_DEF(EXIT, exit)
      CASE_DEF(OPEN, open)
      CASE_DEF(CLOSE, close)
      CASE_DEF(PIPE_OP, pipe_op)
      CASE_DEF(FILENO, fileno)
      CASE_DEF(UMASK, umask)
      CASE_DEF(BINMODE, binmode)
      CASE_DEF(TIE, tie)
      CASE_DEF(UNTIE, untie)
      CASE_DEF(TIED, tied)
      CASE_DEF(DBMOPEN, dbmopen)
      CASE_DEF(DBMCLOSE, dbmclose)
      CASE_DEF(SSELECT, sselect)
      CASE_DEF(SELECT, select)
      CASE_DEF(GETC, getc)
      CASE_DEF(READ, read)
      CASE_DEF(ENTERWRITE, enterwrite)
      CASE_DEF(LEAVEWRITE, leavewrite)
      CASE_DEF(PRTF, prtf)
      CASE_DEF(PRINT, print)
#if PERL_VERSION >= 10
      CASE_DEF(SAY, print)
#endif
      CASE_DEF(SYSOPEN, sysopen)
      CASE_DEF(SYSSEEK, sysseek)
      CASE_DEF(SYSREAD, sysread)
      CASE_DEF(SYSWRITE, syswrite)
      CASE_DEF(SEND, send)
      CASE_DEF(RECV, recv)
      CASE_DEF(EOF, eof)
      CASE_DEF(TELL, tell)
      CASE_DEF(SEEK, seek)
      CASE_DEF(TRUNCATE, truncate)
      CASE_DEF(FCNTL, fcntl)
      CASE_DEF(IOCTL, ioctl)
      CASE_DEF(FLOCK, flock)
      CASE_DEF(SOCKET, socket)
      CASE_DEF(SOCKPAIR, sockpair)
      CASE_DEF(BIND, bind)
      CASE_DEF(CONNECT, connect)
      CASE_DEF(LISTEN, listen)
      CASE_DEF(ACCEPT, accept)
      CASE_DEF(SHUTDOWN, shutdown)
      CASE_DEF(GSOCKOPT, gsockopt)
      CASE_DEF(SSOCKOPT, ssockopt)
      CASE_DEF(GETSOCKNAME, getsockname)
      CASE_DEF(GETPEERNAME, getpeername)
      CASE_DEF(LSTAT, lstat)
      CASE_DEF(STAT, stat)
      CASE_DEF(FTRREAD, ftrread)
      CASE_DEF(FTRWRITE, ftrwrite)
      CASE_DEF(FTREXEC, ftrexec)
      CASE_DEF(FTEREAD, fteread)
      CASE_DEF(FTEWRITE, ftewrite)
      CASE_DEF(FTEEXEC, fteexec)
      CASE_DEF(FTIS, ftis)
      CASE_DEF(FTEOWNED, fteowned)
      CASE_DEF(FTROWNED, ftrowned)
      CASE_DEF(FTZERO, ftzero)
      CASE_DEF(FTSIZE, ftsize)
      CASE_DEF(FTMTIME, ftmtime)
      CASE_DEF(FTATIME, ftatime)
      CASE_DEF(FTCTIME, ftctime)
      CASE_DEF(FTSOCK, ftsock)
      CASE_DEF(FTCHR, ftchr)
      CASE_DEF(FTBLK, ftblk)
      CASE_DEF(FTFILE, ftfile)
      CASE_DEF(FTDIR, ftdir)
      CASE_DEF(FTPIPE, ftpipe)
      CASE_DEF(FTLINK, ftlink)
      CASE_DEF(FTSUID, ftsuid)
      CASE_DEF(FTSGID, ftsgid)
      CASE_DEF(FTSVTX, ftsvtx)
      CASE_DEF(FTTTY, fttty)
      CASE_DEF(FTTEXT, fttext)
      CASE_DEF(FTBINARY, ftbinary)
      CASE_DEF(CHDIR, chdir)
      CASE_DEF(CHOWN, chown)
      CASE_DEF(CHROOT, chroot)
      CASE_DEF(UNLINK, unlink)
      CASE_DEF(CHMOD, chmod)
      CASE_DEF(UTIME, utime)
      CASE_DEF(RENAME, rename)
      CASE_DEF(LINK, link)
      CASE_DEF(SYMLINK, symlink)
      CASE_DEF(READLINK, readlink)
      CASE_DEF(MKDIR, mkdir)
      CASE_DEF(RMDIR, rmdir)
      CASE_DEF(OPEN_DIR, open_dir)
      CASE_DEF(READDIR, readdir)
      CASE_DEF(TELLDIR, telldir)
      CASE_DEF(SEEKDIR, seekdir)
      CASE_DEF(REWINDDIR, rewinddir)
      CASE_DEF(CLOSEDIR, closedir)
      CASE_DEF(FORK, fork)
      CASE_DEF(WAIT, wait)
      CASE_DEF(WAITPID, waitpid)
      CASE_DEF(SYSTEM, system)
      CASE_DEF(EXEC, exec)
      CASE_DEF(KILL, kill)
      CASE_DEF(GETPPID, getppid)
      CASE_DEF(GETPGRP, getpgrp)
      CASE_DEF(SETPGRP, setpgrp)
      CASE_DEF(GETPRIORITY, getpriority)
      CASE_DEF(SETPRIORITY, setpriority)
      CASE_DEF(TIME, time)
      CASE_DEF(TMS, tms)
      CASE_DEF(LOCALTIME, localtime)
      CASE_DEF(GMTIME, gmtime)
      CASE_DEF(ALARM, alarm)
      CASE_DEF(SLEEP, sleep)
      CASE_DEF(SHMGET, shmget)
      CASE_DEF(SHMCTL, shmctl)
      CASE_DEF(SHMREAD, shmread)
      CASE_DEF(SHMWRITE, shmwrite)
      CASE_DEF(MSGGET, msgget)
      CASE_DEF(MSGCTL, msgctl)
      CASE_DEF(MSGSND, msgsnd)
      CASE_DEF(MSGRCV, msgrcv)
      CASE_DEF(SEMGET, semget)
      CASE_DEF(SEMCTL, semctl)
      CASE_DEF(SEMOP, semop)
      CASE_EMPTY(REQUIRE)
      CASE_DEF(DOFILE, require)
      CASE_DEF(ENTEREVAL, entereval)
      CASE_DEF(LEAVEEVAL, leaveeval)
      CASE_DEF(ENTERTRY, entertry)
      CASE_DEF(LEAVETRY, leavetry)
      CASE_DEF(GHBYNAME, ghbyname)
      CASE_DEF(GHBYADDR, ghbyaddr)
      CASE_DEF(GHOSTENT, ghostent)
      CASE_DEF(GNBYNAME, gnbyname)
      CASE_DEF(GNBYADDR, gnbyaddr)
      CASE_DEF(GNETENT, gnetent)
      CASE_DEF(GPBYNAME, gpbyname)
      CASE_DEF(GPBYNUMBER, gpbynumber)
      CASE_DEF(GPROTOENT, gprotoent)
      CASE_DEF(GSBYNAME, gsbyname)
      CASE_DEF(GSBYPORT, gsbyport)
      CASE_DEF(GSERVENT, gservent)
      CASE_DEF(SHOSTENT, shostent)
      CASE_DEF(SNETENT, snetent)
      CASE_DEF(SPROTOENT, sprotoent)
      CASE_DEF(SSERVENT, sservent)
      CASE_EMPTY(ENETENT)
      /* fall thru to ehostent */
#if PERL_VERSION < 15
      PL_op = Perl_pp_enetent(aTHX); break;
#endif
      CASE_EMPTY(EPROTOENT)
#if PERL_VERSION < 15
        PL_op = Perl_pp_eprotoent(aTHX); break;
#endif
      CASE_EMPTY(ESERVENT)
#if PERL_VERSION < 15
        PL_op = Perl_pp_eservent(aTHX); break;
#endif
      CASE_EMPTY(SPWENT)
#if PERL_VERSION < 15
        PL_op = Perl_pp_spwent(aTHX); break;
#endif
      CASE_EMPTY(EPWENT)
#if PERL_VERSION < 15
        PL_op = Perl_pp_epwent(aTHX); break;
#endif
      CASE_EMPTY(EGRENT)
#if PERL_VERSION < 15
        PL_op = Perl_pp_egrent(aTHX); break;
#endif
      CASE_EMPTY(SGRENT)
#if PERL_VERSION < 15
        PL_op = Perl_pp_sgrent(aTHX); break;
#endif
      CASE_DEF(EHOSTENT, ehostent)
      CASE_EMPTY(GPWUID)
        /* fall thru to gpwent */
#if PERL_VERSION < 9
        PL_op = Perl_pp_gpwuid(aTHX); break;
#endif
      CASE_EMPTY(GPWNAM)
#if PERL_VERSION < 9
        PL_op = Perl_pp_gpwnam(aTHX); break;
#endif
      CASE_DEF(GPWENT, gpwent)
      CASE_EMPTY(GGRNAM)
        /* fall thru to ggrent */
#if PERL_VERSION < 9
        PL_op = Perl_pp_ggrnam(aTHX); break;
#endif
      CASE_DEF(GGRENT, ggrent)
      CASE_DEF(GGRGID, ggrgid)
      CASE_DEF(GETLOGIN, getlogin)
      CASE_DEF(SYSCALL, syscall)
      CASE_DEF(LOCK, lock)
#if PERL_VERSION < 10
      CASE_DEF(THREADSV, threadsv)
#endif
#if PERL_VERSION < 11
      CASE(SETSTATE, 
           PL_curcop = (COP*)PL_op;
           PL_op = NORMAL)
#endif
      CASE_DEF(METHOD_NAMED, method_named)
#if PERL_VERSION >= 9
      CASE_DEF(DOR, dor)
      CASE_DEF(DORASSIGN, dorassign)
#endif
#if PERL_VERSION >= 10
        CASE_DEF(ENTERGIVEN, entergiven)
        CASE_DEF(LEAVEGIVEN, leavegiven)
        CASE_DEF(ENTERWHEN, enterwhen)
        CASE_DEF(LEAVEWHEN, leavewhen)
        CASE_DEF(BREAK, break)
        CASE_DEF(CONTINUE, continue)
        CASE_DEF(SMARTMATCH, smartmatch)
        CASE_DEF(ONCE, once)
#endif
#if PERL_VERSION >= 11
# if PERL_VERSION < 18
        CASE_DEF(BOOLKEYS, boolkeys)
# endif
        CASE_DEF(HINTSEVAL, hintseval)
        CASE_DEF(AEACH, aeach)
        CASE_EMPTY(AKEYS)
        CASE_DEF(AVALUES, akeys)
#endif
#if PERL_VERSION >= 13
        CASE_EMPTY(REACH)
        CASE_EMPTY(RKEYS)
        CASE_DEF(RVALUES, rkeys)
        CASE_DEF(TRANSR, transr)
#endif
#if PERL_VERSION >= 15
        CASE_DEF(COREARGS, coreargs)
        CASE_DEF(RUNCV, runcv)
        CASE_DEF(FC, fc)
#endif
#if PERL_VERSION >= 19
        CASE_DEF(PADRANGE, padrange)
#endif
#if PERL_VERSION >= 21
        CASE_DEF(MULTIDEREF, multideref)
        CASE_DEF(METHOD_SUPER, method_super)
        CASE_DEF(METHOD_REDIR, method_redir)
#endif
#if PERL_VERSION >= 13
	CASE(CUSTOM,
             PL_op = (*PL_op->op_ppaddr)(aTHX))
#else
	CASE(CUSTOM,
             PL_op = CALL_FPTR(PL_op->op_ppaddr)(aTHX))
#endif
#ifdef CGOTO
#else
	default:
#endif
             Perl_croak(aTHX_ "Invalid opcode '%s'\n", OP_NAME(PL_op));
        SWITCH_END
    } while (PL_op);

    TAINT_NOT;
    return 0;
}

MODULE = Runops::Switch PACKAGE = Runops::Switch

PROTOTYPES: DISABLE

BOOT:
    PL_runops = runops_switch;
