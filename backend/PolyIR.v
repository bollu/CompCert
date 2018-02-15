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
  
  Inductive exec_stmt: lenv -> mem -> stmt -> mem -> lenv -> Prop :=
  | exec_Sstore: forall (le: lenv) (m m': mem)
                   (chunk: memory_chunk) (addr: affineexpr) (i: int) (vaddr: val),
      eval_affineexpr le l addr vaddr ->
      Mem.storev chunk m vaddr (Vint i) = Some m' ->
      exec_stmt le m (Sstore chunk addr i) m' le.
End EXEC_STMT.

Section EXEC_LOOP.

  Inductive exec_loop: lenv -> mem -> loop -> mem -> lenv -> Prop :=
  | eval_loop_stop: forall le m l,
      (loopschedule l (viv le) >= (loopub l))%nat ->
      exec_loop le m l m le
  | eval_loop_loop: forall le le' le'' m m' m'' l,
      exec_stmt l le m (loopstmt l) m' le' ->
      exec_loop (lenv_bump_vindvar le) m' l m'' le'' ->
      exec_loop le m l m'' le''.
End EXEC_LOOP.

Theorem eval_affinexpr_is_function:
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
      
      
      
      
    
    
  
End EXEC_STMT.
  
