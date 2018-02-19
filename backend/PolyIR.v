Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.
Require Import AST.
Require Import Cop.
Require Import Cminor.
Require Import Integers.
Require Import SCEV.
Require Import Znat.
Require Import Nat.
Require Import PeanoNat.

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

Definition env_bump_indvar (le: loopenv) (l: loop) (e: env) : env :=
  PTree.set (loopivname l)
            (nat_to_val(loopschedule l (viv le + 1)%nat))
            e.
  


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


(* Transform a previous match_env into a new match_env *)
Lemma match_env_bump_indvar':
     forall (l: loop) (e: env) (le: loopenv),
  match_env l e le ->
  match_env l (env_bump_indvar le l e) (loopenv_bump_vindvar le).
Proof.
  intros until le.
  intros me.
  unfold match_env in *.
  unfold env_bump_indvar.
  rewrite PTree.gss.
  unfold loopenv_bump_vindvar.
  simpl.
  reflexivity.
Qed.
  



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

(* When we have a loop that is in bounds, shit will work out *)
Theorem match_loop_inner_block_has_same_effect_when_loop_in_bounds:
  forall (le: loopenv) (l: loop)(f: function) (sp: val) (cms: Cminor.stmt) (s: stmt) (m m' m'': mem) (ge: genv) (e e': env) (t: trace) (o: outcome),
    (viv le < loopub l)%nat ->
    match_env l e le ->
    Cminor.exec_stmt ge f sp e m
                     (oned_loop_inner_block (nat_to_int (loopub l))
                                            (loopivname l)
                        cms) t e' m' o ->
    exec_stmt le l m s m'' ->
    match_stmt l cms s ->
    m' = m'' /\
    e' = env_bump_indvar le l e /\
    match_env l e' (loopenv_bump_vindvar le).
Proof.
  admit.
Admitted.


Section MATCHLOOP.
  Inductive match_loop: Cminor.stmt -> loop -> Prop :=
  | match_oned_loop: forall (l: loop)
                       (cm_inner_stmt: Cminor.stmt)
                       (inner_stmt: stmt),
      loopschedule l = id ->
      loopscheduleinv l = id ->
      match_stmt l cm_inner_stmt (loopstmt l) ->
      match_loop (oned_loop
                    (nat_to_int (loopub l))
                    (loopivname l)
                    (cm_inner_stmt))
                 l.
End MATCHLOOP.

Theorem exec_loop_when_iv_gt_ub_has_no_effect:
  forall (ub: nat) (iv: nat),
  forall (le le': loopenv) (l: loop) (m m': mem),
    loopub l = ub ->
    viv le = iv ->
    (iv >= ub)%nat -> 
    exec_loop le  m l  m' le' ->
    le = le' /\ m = m'.
Proof.
  intros until m'.
  intros loopub.
  intros viv.
  intros iv_gt_ub.
  intros execloop.
  induction execloop.
  -  auto.
  - omega.
Qed.

Lemma transfer_nat_lt_to_int_lt:
  forall (n1 n2: nat),
    (n1 < n2)%nat ->
    Int.ltu (nat_to_int n1) (nat_to_int n2) = true.
Proof.
  intros until n2.
  intros n1_lt_n2.
  unfold nat_to_int.
  unfold Int.ltu.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  rewrite zlt_true.
  reflexivity.
  rewrite <- Z.compare_lt_iff.
  rewrite  Znat.inj_compare.
  rewrite Nat.compare_lt_iff.
  assumption.
  split.
  apply Nat2Z.is_nonneg.
  
  
  
  reflexivity.




  
Theorem match_loop_has_same_effect:
  forall le m l m'' le',
    exec_loop le m l  m'' le' ->
    forall (lub: nat)
      (iv: vindvar)
      (ivname: ident)
      (lsched lschedinv: vindvar -> vindvar)
      (loopstmt: stmt),
    forall (f: function)
      (sp: val)
      (cms: Cminor.stmt)
      (m': mem)
      (ge: genv)
      (e e': env),
    le = mkLenv iv ->
    l = mkLoop lub ivname loopstmt lsched lschedinv ->
    match_env l e le ->
    Cminor.exec_stmt ge f sp e m cms E0 e' m' Out_normal ->
    match_loop cms l ->
    m' = m'' /\  match_env l e' le'.
Proof.
  intros until le'.
  intros execl.
  induction execl.
  - intros until e'.
    intros leval.
    intros lval.
    intros matchenv.
    intros exec_cms.
    intros matchloop.

    revert lval.
    revert leval.
    inversion matchloop. subst.
    intros lval.
    intros leval.
    assert (e = e' /\ m = m') as mem_env_unchanged.
    eapply exit_oned_loop.
    assert (eval_expr ge sp e m
                      (Ebinop
                         (Ocmpu Clt)
                         (Evar (loopivname l))
                         (Econst (Ointconst (nat_to_int (loopub l))))) Vfalse)
           as iv_geq_ub.
    admit.
    exact iv_geq_ub.
    exact exec_cms.
    destruct mem_env_unchanged as [meq eeq].
    subst e m.
    auto.
    
  - rename H into viv_inbounds.
    rename H0 into exec_stmt.

    intros until e'.
    intros leval.
    intros lval.
    intros matchenv.
    intros exec_cms.
    intros matchloop.

    (* Extract as much information we can get from matchloop *)
    inversion matchloop.

    (* Revert to prevent proof term explosion *)
    revert lval leval.
    
    subst.
    (* inversion from exec_loop *)
    inversion exec_cms; subst.

    + (* Loop succeeds an iteration *)
    rename H into loopsched.
    rename H0 into loopschedinv.
    rename H1 into match_cm_inner_stmt.
    rename H3 into exec_cms_inner_block.
    rename H4 into exec_cms_loop.
    rename H9 into t1t2val.

    assert (t1 = E0 /\ t2 = E0) as t1_t2_e0.
    apply destruct_trace_app_eq_E0.
    assumption.
    destruct t1_t2_e0.
    subst.
    clear t1t2val.
    
    intros leval lval.

    

    assert(m1 = m' /\
    e1 = env_bump_indvar le l e /\
    match_env l e1 (loopenv_bump_vindvar le)) as match_prev_stmt.
    eapply match_loop_inner_block_has_same_effect_when_loop_in_bounds;
      eassumption.
    destruct match_prev_stmt as [meq [eeq matchenve1]].
    subst m1.
    subst e1.
    
    eapply IHexecl.
    unfold loopenv_bump_vindvar. auto.
    exact leval.
    exact matchenve1.
    exact exec_cms_loop.
    exact matchloop.

    + rename H8 into out_neq_normal.
      contradiction.
Admitted.
       
      
    
    
  




