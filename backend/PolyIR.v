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
                               loopivname: ident;
                               loopstmt: stmt;
                               loopschedule: vindvar -> vindvar;
                               loopscheduleinv: vindvar -> vindvar
                             }.
Record loopenv : Type := mkLenv { viv: vindvar }.
Definition loopenv_bump_vindvar (le: loopenv) : loopenv :=
  mkLenv ((viv le) + 1)%nat.

Section EVAL_AFFINEEXPR.

  Variable le: loopenv.
  Variable l: loop.

  Inductive eval_affineexpr: affineexpr -> val -> Prop :=
  | eval_Eindvar: eval_affineexpr Eindvar (nat_to_val (loopschedule l (viv le)))
  | eval_Econstint: forall (i: int),
      eval_affineexpr (Econstint i) (Vint i).
End EVAL_AFFINEEXPR.

Section EXEC_STMT.
  Inductive exec_stmt: loopenv -> loop -> mem -> stmt -> mem -> Prop :=
  | exec_Sstore: forall (le: loopenv) (l: loop) (m m': mem)
                   (chunk: memory_chunk) (addr: affineexpr) (i: int) (vaddr: val),
      eval_affineexpr le l addr vaddr ->
      Mem.storev chunk m vaddr (Vint i) = Some m' ->
      exec_stmt le l m (Sstore chunk addr i) m'.
End EXEC_STMT.

Section EXEC_LOOP.

  Inductive exec_loop: loopenv -> mem -> loop -> mem -> loopenv -> Prop :=
  | eval_loop_stop: forall le m l,
      (viv le >= loopub l)%nat ->
      exec_loop le m l m le
  | eval_loop_loop: forall le le' m m' m'' l,
      (viv le < loopub l)%nat ->
      exec_stmt le l m (loopstmt l) m' ->
      exec_loop (loopenv_bump_vindvar le) m' l m'' le' ->
      exec_loop le m l m'' le'.
End EXEC_LOOP.

Theorem eval_affineexpr_is_function:
  forall (le: loopenv) (l: loop) (ae: affineexpr) (v v': val),
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
  forall (le: loopenv) (l: loop) (m m' m'': mem) (s: stmt),
    exec_stmt le l m s m' ->
    exec_stmt le l m s m'' ->
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
  rewrite <- H7. rewrite <- H16.
  reflexivity.
  inversion meq. subst.
  auto.
Qed.

Theorem exec_loop_is_function:
  forall (le' le'': loopenv) (viv: vindvar) (l: loop) (m m' m'': mem),
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

Section MATCHENV.
  Definition match_env (l: loop) (e: env) (le: loopenv) : Prop :=
    e ! (loopivname  l) = Some (nat_to_val (loopschedule l (viv le))).
End MATCHENV.



Section MATCHAFFINEEXPR.
  Variable le: loopenv.
  Variable l: loop.
  Inductive match_affineexpr: expr -> affineexpr -> Prop :=
  | match_Evar: match_affineexpr (Evar (loopivname l)) Eindvar
  | match_Econstint: forall i,match_affineexpr (Econst (Ointconst i)) (Econstint i).
End MATCHAFFINEEXPR.

Theorem match_expr_have_same_value:
  forall (l:loop) (le:loopenv) (a:expr) (sp: val) (m: mem) (ae:affineexpr) (e:env) (ge: genv) (v v':val),
    match_affineexpr l a ae ->
    match_env l e le ->
    eval_expr ge sp e m a v ->
    eval_affineexpr le l ae v' ->
    v = v'.
Proof.
  intros until v'.
  intros match_exprs.
  intros match_envs.
  intros eval_expr.
  intros eval_affineexpr.
  
  induction match_exprs;
    inversion eval_expr;
    inversion eval_affineexpr;
    inversion match_envs;
    subst.
  - (* eval indvar *)
    rewrite H4 in H0.
    inversion H0.
    auto.

  -  (* eval const int *)
    inversion H0.
    auto.
Qed.



Section MATCHSTMT.
  Variable le: loopenv.
  Variable l: loop.
  Inductive match_stmt: Cminor.stmt -> stmt -> Prop :=
  | match_Sstore: forall (chunk: memory_chunk) (addre: expr) (i: int)
                    (addrae: affineexpr),
      match_affineexpr l addre addrae ->
      match_stmt (Cminor.Sstore chunk addre (Econst (Ointconst i)))
                 (Sstore chunk addrae i).
End MATCHSTMT.

Theorem match_stmt_has_same_effect:
  forall (le: loopenv) (l: loop)(f: function) (sp: val) (cms: Cminor.stmt) (s: stmt) (m m' m'': mem) (ge: genv) (e e': env) (t: trace) (o: outcome),
    match_env l e le ->
    Cminor.exec_stmt ge f sp e m cms t e' m' o ->
    exec_stmt le l m s m'' ->
    match_stmt l  cms s ->
    m' = m'' /\ e = e' /\ t = E0 /\ o = Out_normal.
Proof.
  intros until o.
  intros matchenv.
  intros exec_cms.
  intros exec_s.
  intros match_cms_s.
  induction match_cms_s.
  inversion exec_s.
  inversion exec_cms.
  subst.
  assert (vaddr0 = vaddr) as vaddreq.
  eapply match_expr_have_same_value; eassumption.
  subst.

  assert (v = Vint i) as veq.
  inversion H21.
  subst.
  inversion H1. subst.
  reflexivity.
  subst.
  
  assert (Some m' = Some m'') as meq.
  rewrite <- H22.
  rewrite <- H8.
  auto.
  inversion meq. subst.
  auto.
Qed.

Section MATCHLOOP.
  Inductive match_loop: Cminor.stmt -> loop -> Prop :=
  | match_oned_loop: forall (l: loop)
                       (cm_inner_stmt: Cminor.stmt)
                       (inner_stmt: stmt),
      loopschedule l = id ->
      loopscheduleinv l = id ->
      match_stmt l cm_inner_stmt inner_stmt ->
      match_loop (oned_loop (loopub l) (loopivname l) (cm_inner_stmt))
                 l.
End MATCHLOOP.

Theorem match_loop_has_same_effect:
  forall (le le': loopenv) (l: loop)(f: function) (sp: val) (cms: Cminor.stmt) (s: stmt) (m m' m'': mem) (ge: genv) (e e': env) (o: outcome),
    match_env l e le ->
    Cminor.exec_stmt ge f sp e m cms E0 e' m' o ->
    exec_loop le m l  m'' le' ->
    match_loop cms l ->
    m' = m''  /\  match_env l e' le'.
Proof.
  intros until o.
  intros matchenv.
  intros exec_cm_loop.
  intros exec_l.
  intros match_l.


  induction match_l.

  (* match_oned_loop *)
  - rename H into l_sched_id.
    rename H0 into l_schedinv_id.
    rename H1 into match_stmts.

    inversion exec_l.
    subst.

    + (* exec_loop when loop has no iters *)
      rename H into viv_le_gt_loopub.
      assert (e = e' /\ m'' = m').
      eapply oned_loop_with_iv_gt_ub_will_not_execute with
          (ivname := (loopivname l))
          (n := loopub l).
      inversion matchenv. subst. exact H0.
      rewrite l_sched_id.
      unfold id.
      unfold Int.ltu.
      rewrite zlt_false.
      reflexivity.
      unfold SCEV.nat_to_int.
      unfold z_to_int.
      admit. (* modulo arithmetic *)
      eassumption.
      destruct H. subst.
      auto.

    + (* exec_loop where we have loop iters *)
      intros.
      subst.
      rename H into iv_in_bounds.
      rename H0 into exec_prev_s.
      rename H1 into exec_cur_l.
      induction (loopub l).

      * (* loopub = 0 *)
        inversion iv_in_bounds.
      * (* loopub > 0 *)
        apply IHn.
        inversion exec_cm_loop. subst.
Abort.
             




