Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.
Require Import AST.
Require Import Cop.
Require Import Csharpminor.

Definition indvar := positive.

Inductive affineexpr: Type :=
| Eindvar: indvar -> affineexpr
| Econstint: int -> affineexpr
| Eadd:  affineexpr -> affineexpr -> affineexpr.

Inductive stmt: Type :=
| Sstore:  memory_chunk -> affineexpr -> int -> stmt
| Sseq: stmt -> stmt -> stmt
| Sloop: indvar -> affineexpr -> stmt -> stmt. (* Sloop <trip count> <statement> *)

Section EVALAFFINEEXPR.
Definition env := PTree.t int.
Variable e: env.

Inductive eval_affineexpr: affineexpr -> int -> Prop :=
| eval_Econstint: forall (i: int),
    eval_affineexpr (Econstint i) i
| eval_Eadd: forall (a1 a2: affineexpr) (v1 v2: int),
    eval_affineexpr a1 v1 ->
    eval_affineexpr a2 v2 ->
    eval_affineexpr (Eadd a1 a2) (Int.add v1 v2)
| eval_Eindvar: forall (indvar: indvar) (i: int),
    PTree.get indvar e = Some i -> eval_affineexpr (Eindvar indvar) i.

End EVALAFFINEEXPR.

Section NATURALSEM.
  Inductive exec_stmt: env -> mem -> stmt -> env -> mem -> Prop :=
  | exec_Sstore: forall e m m' chunk addr vaddr vwrite,
      eval_affineexpr e addr vaddr ->
      Mem.storev chunk m (Vint vaddr) (Vint vwrite) = Some m' ->
      exec_stmt e m (Sstore chunk  addr vwrite) e m'
  | exec_Sseq: forall mem mem1 mem2 env env1 env2 s1 s2,
      exec_stmt env mem s1 env1 mem1 ->
               exec_stmt env1 mem1 s2 env2 mem2 ->
               exec_stmt env mem (Sseq s1 s2) env2 mem2
  | exec_Sloop_loop: forall indvar env env1 env2 mem mem1 mem2 tripcountexpr s tripcounti indvari,
      eval_affineexpr env tripcountexpr tripcounti ->
      PTree.get indvar env = Some indvari ->
      Int.cmp Clt indvari  tripcounti = true ->
      exec_stmt env mem s env1 mem1 ->
      exec_stmt env1 mem1 (Sloop indvar tripcountexpr s) env2 mem2 ->
      exec_stmt env mem (Sloop indvar tripcountexpr s) env2 mem2
      
                
  | exec_Sloop_stop: forall indvar env mem  tripcountexpr s tripcounti indvari,
      eval_affineexpr env tripcountexpr tripcounti ->
      PTree.get indvar env = Some indvari ->
      Int.cmp Cge indvari  tripcounti = true ->
      exec_stmt env mem (Sloop indvar tripcountexpr s) env mem.
      
      
 End Section NATURALSEM.
  

    
    

