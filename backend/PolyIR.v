Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.
Require Import AST.
Require Import Cop.
Require Import Cminor.
Require Import Integers.
Require Import SCEV.

Inductive affineexpr: Type :=
| Eindvar: affineexpr
| Econstint: int -> affineexpr.

Inductive stmt: Type :=
| Sstore:  memory_chunk -> affineexpr -> int -> stmt
| Sseq: stmt -> stmt -> stmt.

Notation indvar := nat.
Notation upperbound := nat.
Definition indvar_to_int (iv: indvar): int := (Int.repr (Z.of_nat iv)).
Definition ub_to_int (ub: upperbound): int := (Int.repr (Z.of_nat ub)).

Record loop : Type := mkLoop { loopub: upperbound; loopstmt: stmt }.


Section EVALAFFINEEXPR.
  Variable iv: indvar.

Inductive eval_affineexpr: affineexpr -> int -> Prop :=
| eval_Econstint: forall (x: int), eval_affineexpr (Econstint x) x
| eval_Eindvar: eval_affineexpr Eindvar (indvar_to_int iv).
End EVALAFFINEEXPR.


Section EXECSTMT.

  Inductive exec_stmt: indvar -> mem -> stmt -> mem -> Prop :=
  | exec_Sstore: forall iv m m' chunk addr vaddr vwrite,
      eval_affineexpr iv addr vaddr ->
      Mem.storev chunk m (Vint vaddr) (Vint vwrite) = Some m' ->
      exec_stmt  iv m (Sstore chunk  addr vwrite) m'.
      
      
End EXECSTMT.

Section EXECLOOP.
  Inductive exec_loop: indvar -> mem -> loop -> indvar -> mem -> Prop :=
  | eval_loop_stop: forall iv ub mem s,
      (iv >= ub)%nat  ->
      exec_loop iv mem (mkLoop ub s) iv mem
  | eval_loop_loop: forall iv iv2 ub mem s mem2 mem3,
      (iv < ub)%nat ->
      exec_stmt iv mem s mem2 ->
      exec_loop (iv + 1) mem2  (mkLoop ub s) iv2 mem3 ->
      exec_loop iv mem2 (mkLoop ub s) iv2 mem3.
End EXECLOOP.

Inductive eequiv: Cminor.expr -> affineexpr -> Prop :=
| eequiv_Constint: forall (i: int),
    eequiv (Econst (Ointconst i)) (Econstint i).
  

Section STMTEQUIV.
Inductive sequiv: Cminor.stmt -> stmt -> Prop :=
| sequiv_Sstore: forall (chunk: memory_chunk) (cmaddr: Cminor.expr) (addr: affineexpr)
                        (ival: int),
    eequiv cmaddr addr ->
    sequiv (Cminor.Sstore chunk cmaddr (Econst (Ointconst ival))) (Sstore chunk addr ival).
End STMTEQUIV.

     

(*
----
  var 'i';                                                                         
  'i' = 0;                                                                         
  {{ loop {                                                                        
       {{ if ('i' < 10) {                                                          
            /*skip*/                                                               
            } else {                                                                 
            exit 1;                                                                
          }                                                                        
          int32[&0 +l 4LL *l longofint 'i'] = 'i' + 1;                             
       }}                                                                          
       'i' = 'i' + 1;                                                              
     }                                                                             
  }}
----
 *)


(* construct a CMinor loop from 0 to ub with stmt cmstmt inside the loop *)
Definition cm_loop_0_to_ub (ub: upperbound) (ivname: ident) (addrexpr: expr) (storeval: expr): Cminor.stmt :=
  Cminor.Sseq (Sassign ivname (Econst (Ointconst (Int.repr 0))))
       (Sblock (
            Sloop (
                Sblock (
                    Cminor.Sseq (Sifthenelse (Ebinop
                                                (Ocmp  Clt)
                                                (Evar ivname)
                                                (Econst (Ointconst (ub_to_int ub))))
                                (Sskip)
                                (Sexit 0) (* this is a hack, there is no reason it has to be 0 *)
                                )
                                (Cminor.Sstore Mint32 addrexpr storeval)
                  )
              )
          )
       ).
Hint Transparent cm_loop_0_to_ub.


Definition cm_fn_0_to_ub
           (fn: Cminor.function)
           (ub: upperbound)
           (addre storee: expr)
           (iv: ident): Prop :=
  Cminor.fn_body fn = cm_loop_0_to_ub ub iv addre storee.
  

Hint Transparent cm_fn_0_to_ub.
  
Check (Cminor.exec_stmt).

Theorem fnequiv_preserves_mem:
  forall  (ge: genv) (cmf: Cminor.function) (cmfargs: list val)   (tr: trace) (l: loop) (mem mem': mem) (ub: upperbound) (iv: ident) (addre storee: expr) (addraff storeaff: affineexpr),
    eequiv addre addraff ->
    eequiv storee storeaff ->
    cm_fn_0_to_ub cmf ub addre storee iv ->
    eval_funcall ge mem (Internal cmf) cmfargs tr mem' Vundef ->
    exec_loop 0 mem l ub mem'.
Abort.