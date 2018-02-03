Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.
Require Import AST.
Require Import Cop.
Require Import Cminor.
Require Import Integers.

Inductive affineexpr: Type :=
| Eindvar: affineexpr
| Econstint: int -> affineexpr.

Inductive stmt: Type :=
| Sstore:  memory_chunk -> affineexpr -> int -> stmt
| Sseq: stmt -> stmt -> stmt.

Notation indvar := nat.
Notation upperbound := nat.
Definition indvar_to_int (iv: indvar): int := (Int.repr (Z.of_nat iv)).

Record loop : Type := mkLoop { loopub: upperbound; loopstmt: stmt }.


Section EVALAFFINEEXPR.
  Variable iv: indvar.

Inductive eval_affineexpr: affineexpr -> int -> Prop :=
| eval_Econstint: forall (x: int), eval_affineexpr (Econstint x) x
| eval_Eindvar: eval_affineexpr Eindvar (indvar_to_int iv).
End EVALAFFINEEXPR.


Section EVALSTMT.

  Inductive exec_stmt: indvar -> mem -> stmt -> mem -> Prop :=
  | exec_Sstore: forall iv m m' chunk addr vaddr vwrite,
      eval_affineexpr iv addr vaddr ->
      Mem.storev chunk m (Vint vaddr) (Vint vwrite) = Some m' ->
      exec_stmt  iv m (Sstore chunk  addr vwrite) m'
  | exec_Sseq: forall iv m m1 m2 s1 s2,
      exec_stmt iv m s1 m1 ->
               exec_stmt iv m1 s2 m2 ->
               exec_stmt iv m1 (Sseq s1 s2) m2.

  
  (* 
  | exec_Sloop_loop: forall (iv :indvar) k l m m1 m2 s ub,
      Int.cmp Clt (indvar_to_int iv) ub = true ->
      exec_stmt iv m s (iv + k) m1 ->
      exec_stmt (iv + k) m1 (Sloop iv ub s) m2 (iv + k + l) ->
      exec_stmt iv m  (Sloop indvar ub s) (iv + k + l) m2
     
 
                
  | exec_Sloop_stop: forall indvar env mem  s indvari ub,
      PTree.get indvar env = Some indvari ->
      Int.cmp Cge indvari ub = true ->
      exec_stmt env mem (Sloop indvar ub s) env mem.
*)
      
      
End EVALSTMT.

Section EVALLOOP.
  Inductive exec_loop: indvar -> mem -> loop -> indvar -> mem -> Prop :=
  | eval_loop_stop: forall iv ub mem s,
      (iv >= ub)%nat  ->
      exec_loop iv mem (mkLoop ub s) iv mem
  | eval_loop_loop: forall iv iv2 ub mem s mem2 mem3,
      (iv < ub)%nat ->
      exec_stmt iv mem s mem2 ->
      exec_loop (iv + 1) mem2  (mkLoop ub s) iv2 mem3 ->
      exec_loop iv mem2 (mkLoop ub s) iv2 mem3.
End EVALLOOP.

Inductive eequiv: Cminor.expr -> affineexpr -> Prop :=
| eequiv_Constint: forall (i: int),
    eequiv (Econst (Ointconst i)) (Econstint i).
  

Inductive sequiv: Cminor.stmt -> stmt -> Prop :=
| sequiv_Sseq: forall (cms1 cms2: Cminor.stmt) (s1 s2: stmt),
    sequiv cms1 s1 ->
    sequiv cms2 s2 ->
    sequiv (Cminor.Sseq cms1 cms2) (Sseq s1 s2)
| sequiv_Sstore: forall (chunk: memory_chunk) (cmaddr: Cminor.expr) (addr: affineexpr)
                        (ival: int),
    eequiv cmaddr addr ->
    sequiv (Cminor.Sstore chunk cmaddr (Econst (Ointconst ival))) (Sstore chunk addr ival).


(* construct a CMinor loop from 0 to ub with stmt cmsinner inside the loop *)
Definition cm_loop_0_to_ub (ub: upperbound) (cmsinner: Cminor.stmt) : Cminor.stmt :=
  cmsinner.
  
Inductive lequiv : Cminor.stmt -> loop -> Prop :=
| lequiv_loop_0_to_ub: forall (ub: upperbound) (cmsinner: Cminor.stmt) (sinner: stmt),
    sequiv cmsinner sinner ->
    lequiv (cm_loop_0_to_ub 0 cmsinner) (mkLoop ub sinner).

    
(*
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
*)

    