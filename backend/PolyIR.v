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
| Sstore:  memory_chunk -> affineexpr -> int -> stmt.
                                              

Notation vindvar := nat.
Notation indvar := nat.
Notation upperbound := nat.

Definition nat_to_int (n: nat): int := (Int.repr (Z.of_nat n)).
Definition nat_to_val (n: nat): val := Vint (nat_to_int  n).

Record loop : Type := mkLoop { loopub: upperbound;
                               loopstmt: stmt;
                               loopschedule: vindvar -> vindvar
                             }.
Record lenv : Type := mkLenv { viv: vindvar }.
Definition lenv_bump_vindvar (le: lenv) : lenv :=
  mkLenv ((viv le) + 1)%nat.

Section EVAL_AFFINEEXPR.

Variable le: lenv.
Variable l: loop.

Inductive eval_affineexpr: affineexpr -> val -> Prop :=
  | eval_Eindvar: eval_affineexpr Eindvar (nat_to_val (loopschedule l (viv le)))
  | eval_Econstint: forall (i: int),
      eval_affineexpr (Econstint i) (Vint i).
End EVAL_AFFINEEXPR.

Section EXEC_STMT.
Variable l: loop.
  
  Inductive exec_stmt: lenv -> mem -> stmt -> mem -> Prop :=
  | exec_Sstore: forall (le: lenv) (m m': mem)
                   (chunk: memory_chunk) (addr: affineexpr) (i: int) (vaddr: val),
      eval_affineexpr le l addr vaddr ->
      Mem.storev chunk m vaddr (Vint i) = Some m' ->
      exec_stmt le m (Sstore chunk addr i) m'.
End EXEC_STMT.

Section EXEC_LOOP.

  Inductive exec_loop: lenv -> mem -> loop -> mem -> lenv -> Prop :=
  | eval_loop_stop: forall le m l,
      (viv le >= loopub l)%nat ->
      exec_loop le m l m le
  | eval_loop_loop: forall le le' m m' m'' l,
      (viv le < loopub l)%nat ->
      exec_stmt l le m (loopstmt l) m' ->
      exec_loop (lenv_bump_vindvar le) m' l m'' le' ->
      exec_loop le m l m'' le'.
End EXEC_LOOP.

Theorem eval_affineexpr_is_function:
  forall (le: lenv) (l: loop) (ae: affineexpr) (v v': val),
    eval_affineexpr le l ae v ->
    eval_affineexpr le l ae v' ->
    v = v'.
Proof.
  intros until v'.
  intros eval_v.
  intros eval_v'.
  induction ae; inversion eval_v; inversion eval_v'; subst; try auto.
Qed.


Theorem exec_stmt_is_function:
  forall (le: lenv) (l: loop) (m m' m'': mem) (s: stmt),
    exec_stmt l le m s m' ->
    exec_stmt l le m s m'' ->
    m' = m''.
Proof.
  intros until s.
  intros eval_m.
  intros eval_m'.
  induction s; inversion eval_m;inversion eval_m'; subst; try auto.
  assert(vaddr = vaddr0) as veq.
  eapply eval_affineexpr_is_function; eassumption.
  subst.
  assert (Some m' = Some m'') as meq.
  rewrite <- H14. rewrite <- H6.
  reflexivity.
  inversion meq. subst.
  auto.
Qed.

Theorem exec_loop_is_function:
  forall (le' le'': lenv) (viv: vindvar) (l: loop) (m m' m'': mem),
    exec_loop (mkLenv viv) m l m' le' ->
    exec_loop (mkLenv viv) m l m'' le'' ->
    m' = m'' /\ le' = le''.
Proof.
  intros until m''.
  intros exec_l1 exec_l2.
  induction exec_l1; induction exec_l2; subst.
  - auto.
  - omega.
  - omega.
  -  assert (m' = m'0) as meq.
     eapply exec_stmt_is_function; eassumption.
     subst.
     eapply IHexec_l1.
     eassumption.
Qed.
      
      
      
      
    
    
  
  
