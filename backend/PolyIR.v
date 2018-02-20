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

Record loop : Type :=
  mkLoop { loopub: upperbound;
           loopub_in_range_witness: Z.of_nat loopub < Int.max_unsigned;
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

Definition env_incr_iv_wrt_loop (le: loopenv) (l: loop) (e: env) : env :=
  PTree.set (loopivname l)
            (nat_to_val(loopschedule l (viv le + 1)%nat))
            e.


(* Transform a previous match_env into a new match_env *)
Lemma match_env_incr_iv_wrt_loop':
     forall (l: loop) (e: env) (le: loopenv),
  match_env l e le ->
  match_env l (env_incr_iv_wrt_loop le l e) (loopenv_bump_vindvar le).
Proof.
  intros until le.
  intros me.
  unfold match_env in *.
  unfold env_incr_iv_wrt_loop.
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


(* match_expr in terms of synthesizing the eval_expr *)
Theorem match_expr_have_same_value':
  forall (l:loop) (le:loopenv) (a:expr) (sp: val) (m: mem) (ae:affineexpr) (e:env) (ge: genv) (v:val),
    match_affineexpr l a ae ->
    match_env l e le ->
    eval_affineexpr le l ae v ->
    eval_expr ge sp e m a v.
Proof.
  intros until v.
  intros match_exprs.
  intros match_envs.
  intros eval_affineexpr.
  
  induction match_exprs;
    inversion eval_affineexpr;
    inversion match_envs;
    subst.
  - (* eval indvar *)
    eapply eval_Evar.
    assumption.

  -  (* eval const int *)
    eapply eval_Econst.
    unfold eval_constant.
    reflexivity.
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

Theorem match_stmt_has_same_effect':
  forall (le: loopenv) (l: loop)(f: function) (sp: val) (cms: Cminor.stmt) (s: stmt) (m m':mem) (ge: genv) (e: env),
    match_env l e le ->
    exec_stmt le l m s m' ->
    match_stmt l  cms s ->
    Cminor.exec_stmt ge f sp e m cms E0 e m' Out_normal.
Proof.
  intros until e.
  intros matchenv.
  inversion matchenv.
  rename H0 into e_at_loopivname.

  intros execstmt.
  intros matchstmt.
  induction s.

  - (* Store *)
    
    inversion execstmt. subst.
    
    inversion matchstmt. subst.
    eapply Cminor.exec_Sstore.
    eapply match_expr_have_same_value'.
    eassumption.
    eassumption.
    eassumption.

    eapply eval_Econst.
    unfold eval_constant.
    auto.

    assumption.
Qed.
     
     

  

(* NOTE: this may need to be changed later on and become some dynamic
condition we extract out from the code. For now, we know that all
the statements we allow do not modify the environment *)
Theorem match_stmt_does_not_alias: 
  forall (l: loop) (name: ident) (s: stmt) (cms: Cminor.stmt),
    match_stmt l cms s ->
    stmt_does_not_alias cms name.
Proof.
  intros until cms.
  intros matchstmt.
  unfold stmt_does_not_alias.
  intros until locv.
  intros e_at_name.
  intros exec_s.

  inversion matchstmt; subst.

  - inversion exec_s. subst.
    auto.
Qed.
  

Lemma transfer_nat_add_to_int_add:
  forall (n: nat),
    Z.of_nat n < Int.max_unsigned ->
    Int.repr (Z.of_nat (n + 1)%nat) =
    (Int.add (Int.repr (Z.of_nat n)) Int.one).
Proof.
  intros n.
  intros n_lt_unsigned.
  rewrite Int.add_unsigned.
  unfold Int.one.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  rewrite Nat2Z.inj_add.
  simpl.
  reflexivity.
  split.
  omega.
  unfold Int.max_unsigned.
  unfold Int.modulus.
  unfold Int.wordsize.
  simpl.
  omega.

  split.
  omega.
  omega.
Qed.

Lemma transfer_nat_lt_to_int_lt:
  forall (n1 n2: nat),
    (n1 < n2)%nat ->
    Z.of_nat n1 <= Int.max_unsigned ->
    Z.of_nat n2 <= Int.max_unsigned ->
    Int.ltu (nat_to_int n1) (nat_to_int n2) = true.
Proof.
  intros until n2.
  intros n1_lt_n2.

  intros n1_lt_max_unsigned.
  intros n2_lt_max_unsigned.
  
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
  apply n2_lt_max_unsigned.

  split.
  apply Nat2Z.is_nonneg.
  apply n1_lt_max_unsigned.
Qed.


Lemma transfer_nat_ge_to_int_ltu:
  forall (n1 n2: nat),
    (n1 >= n2)%nat ->
    Z.of_nat n1 <= Int.max_unsigned ->
    Z.of_nat n2 <= Int.max_unsigned ->
    Int.ltu (nat_to_int n1) (nat_to_int n2) = false.
Proof.
  intros until n2.
  intros n1_lt_n2.

  intros n1_lt_max_unsigned.
  intros n2_lt_max_unsigned.
  
  unfold nat_to_int.
  unfold Int.ltu.
  rewrite Int.unsigned_repr.
  rewrite Int.unsigned_repr.
  rewrite zlt_false.
  reflexivity.
  apply Z.le_ge.
  rewrite <- Z.compare_ge_iff.
  rewrite  Znat.inj_compare.
  rewrite Nat.compare_lt_iff.
  omega.

  split.
  apply Nat2Z.is_nonneg.
  apply n2_lt_max_unsigned.

  split.
  apply Nat2Z.is_nonneg.
  apply n1_lt_max_unsigned.
Qed.

Lemma eval_iv_lt_ub_false:
  forall (ge: genv) (sp: val) (m: mem),
  forall (e: env) (ivname: ident) (viv: nat) (ub: upperbound),
    Z.of_nat viv <= Int.max_unsigned ->
    (viv >= ub)%nat ->
    e ! ivname = Some (nat_to_val viv) ->
    eval_expr ge sp e m 
              (Ebinop
                 (Ocmpu Clt)
                 (Evar ivname)
                 (Econst (Ointconst (nat_to_int ub)))) Vfalse.
Proof.
  intros until ub.
  intros ub_lt_max_unsigned.
  intros viv_lt_ub.
  intros e_at_ivname_is_viv.
  eapply eval_Ebinop.
  eapply eval_Evar.
  eassumption.
  eapply eval_Econst.
  unfold eval_constant.
  auto.

  unfold eval_binop.
  unfold Val.cmpu.
  unfold Val.cmpu_bool.
  unfold nat_to_val.
  unfold Val.of_optbool.
  unfold Int.cmpu.
  rewrite transfer_nat_ge_to_int_ltu.
  reflexivity.
  eassumption.

  eassumption.


  eapply Z.le_trans with (m := Z.of_nat viv0).
  omega.
  omega.
Qed.

Lemma eval_iv_lt_ub_true:
  forall (ge: genv) (sp: val) (m: mem),
  forall (e: env) (ivname: ident) (viv: nat) (ub: upperbound),
    Z.of_nat ub < Int.max_unsigned ->
    (viv < ub)%nat ->
    e ! ivname = Some (nat_to_val viv) ->
    eval_expr ge sp e m 
              (Ebinop
                 (Ocmpu Clt)
                 (Evar ivname)
                 (Econst (Ointconst (nat_to_int ub)))) Vtrue.
Proof.
  intros until ub.
  intros ub_lt_max_unsigned.
  intros viv_lt_ub.
  intros e_at_ivname_is_viv.
  eapply eval_Ebinop.
  eapply eval_Evar.
  eassumption.
  eapply eval_Econst.
  unfold eval_constant.
  auto.

  unfold eval_binop.
  unfold Val.cmpu.
  unfold Val.cmpu_bool.
  unfold nat_to_val.
  unfold Val.of_optbool.
  unfold Int.cmpu.
  rewrite transfer_nat_lt_to_int_lt.
  reflexivity.
  eassumption.

  assert (Z.of_nat viv0 < Z.of_nat ub) as z_viv0_lt_ub.
  apply Znat.inj_lt.
  assumption.

  eapply Z.le_trans with (m := Z.of_nat ub).
  omega.
  omega.
  omega.
Qed.

  

Section MATCHLOOP.
  Inductive match_loop: Cminor.stmt -> loop -> Prop :=
  | match_oned_loop: forall (l: loop)
                       (cm_inner_stmt: Cminor.stmt)
                       (inner_stmt: stmt),
      loopschedule l = id ->
      loopscheduleinv l = id ->
      match_stmt l cm_inner_stmt (loopstmt l) ->
      match_loop (oned_loop_incr_by_1
                    (nat_to_int (loopub l))
                    (loopivname l)
                    (cm_inner_stmt))
                 l.
End MATCHLOOP.


(* When we have a loop that is in bounds, shit will work out *)
(*
Theorem match_loop_inner_block_has_same_effect_when_loop_in_bounds:
  forall (le le': loopenv) (l: loop)(f: function) (sp: val)
    (cms: Cminor.stmt) (s: stmt)
    (m mloop mblock minner: mem)
    (ge: genv)
    (e eblock einner: env)
    (o: outcome),
    match_loop cms l ->
    match_stmt l cms s ->
    exec_loop le m l  mloop le' ->
    match_env l e le ->
    loopschedule l = id ->
    (Z.of_nat (loopub l) < Int.max_unsigned) ->
    (viv le < loopub l)%nat ->
    Cminor.exec_stmt ge f sp e m
                     (oned_loop_inner_block (nat_to_int (loopub l))
                                            (loopivname l)
                                            (Sseq
                                               cms
                                               (s_incr_by_1 (loopivname l))
                     )) E0 eblock mblock o ->
    Cminor.exec_stmt ge f sp e m cms E0 einner minner Out_normal ->
     (*exec_stmt le l m s mloop -> *)
    mloop = mblock.
Proof.
  intros until o.
  intros matchloop.
  intros matchstmt.
  intros execloop.
  intros matchenv.
  intros loopsched_l_id.

  
  intros loopub_lt_max_unsigned.
  intros viv_le_ub.
  
  intros exec_cm_block.
  intros exec_cm_stmt.

  inversion matchenv. subst.
  rename H0 into e_at_loopiv.
  rewrite loopsched_l_id in e_at_loopiv.
  unfold id in e_at_loopiv.



  (* assert (mblock = minner  /\
          o = Out_normal /\
         eblock = incr_env_by_1 einner (loopivname l) (nat_to_int (viv le))) as eqs. *)
  assert (mblock = minner) as eqs.
  eapply continue_sblock_incr_by_1_sseq_sif.
  eapply eval_iv_lt_ub_true.
  exact loopub_lt_max_unsigned.
  exact viv_le_ub.
  exact e_at_loopiv.
  exact exec_cm_stmt.
  exact exec_cm_block.
  exact e_at_loopiv.
  eapply match_stmt_does_not_alias.
  exact matchstmt.

  destruct eqs as [meq [oeq eeq]].
  subst.

  inversion execloop. subst.
  omega.
  subst.

  assert ()

  assert (mloop = minner /\ )
Admitted.
*)


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

  
Theorem match_loop_has_same_effect:
  forall le m l mloop le',
    exec_loop le m l  mloop le' ->
    forall (lub: nat)
      (iv: vindvar)
      (ivname: ident)
      (lsched lschedinv: vindvar -> vindvar)
      (lub_in_range: Z.of_nat lub < Int.max_unsigned)
      (viv_in_range: Z.of_nat iv < Int.max_unsigned)
      (loopstmt: stmt),
    forall (f: function)
      (sp: val)
      (cms: Cminor.stmt)
      (mblock: mem)
      (ge: genv)
      (e eblock: env),
    le = mkLenv iv ->
    l = mkLoop lub lub_in_range ivname loopstmt lsched lschedinv ->
    match_env l e le ->
    Cminor.exec_stmt ge f sp e m cms E0 eblock mblock Out_normal ->
    match_loop cms l ->
    mloop = mblock /\  match_env l eblock le'.
Proof.
  intros until le'.
  intros execl.
  induction execl.
  - intros until eblock.
    intros leval.
    intros lval.
    intros matchenv.
    intros exec_cms.
    intros matchloop.

    revert lval.
    revert leval.
    inversion matchloop. subst.
    intros leval.
    intros lval.
    assert (e = eblock /\ m = mblock) as mem_env_unchanged.
    eapply exit_oned_loop_incr_by_1.

    assert (viv le = iv) as viv_le_is_iv. rewrite leval.
    auto.
    
    assert (eval_expr ge sp e m
                      (Ebinop
                         (Ocmpu Clt)
                         (Evar (loopivname l))
                         (Econst (Ointconst (nat_to_int (loopub l))))) Vfalse)
      as iv_geq_ub.
    eapply eval_iv_lt_ub_false with (viv := iv).
    omega.
    rewrite <- viv_le_is_iv.
    omega.
    inversion matchenv. rewrite H4.
    inversion matchloop. rewrite H10.
    unfold id. rewrite <- viv_le_is_iv.
    reflexivity.
    exact iv_geq_ub.
    exact exec_cms.
    destruct mem_env_unchanged as [meq eeq].
    subst e m.
    auto.
    
  - rename H into viv_inbounds.
    rename H0 into exec_stmt.

    intros until eblock.
    intros leval.
    intros lval.
    intros matchenv.
    intros exec_cms_full_loop.
    intros matchloop.

    (* Extract as much information we can get from matchloop *)
    inversion matchloop.

    (* Revert to prevent proof term explosion *)
    revert lval leval.
    
    subst.

    
    (* inversion from exec_loop *)
    inversion exec_cms_full_loop; subst.

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

    
    intros lval leval.
    eapply IHexecl with (iv := (iv + 1)%nat).
    admit. (* figure out how to control this *)
    unfold loopenv_bump_vindvar.
    rewrite leval. simpl. reflexivity.
    exact lval.
    eapply match_env_incr_iv_wrt_loop'. eassumption.

    (* this should be matched with exec_cms_loop *)
    assert (m1 = m') as meq.
    eapply continue_sblock_incr_by_1_sseq_sif.
    admit. (* admit the condition thing for this case *)
    eapply match_stmt_has_same_effect'.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eassumption.
    eapply match_stmt_does_not_alias.
    eassumption.
    (* ---- *)

    inversion matchenv.
    rename H0 into e_at_ivname.
    rewrite loopsched in e_at_ivname.
    rewrite lval in e_at_ivname.
    rewrite leval in e_at_ivname.
    simpl in e_at_ivname.
    unfold id in e_at_ivname.
    
    assert (env_incr_iv_wrt_loop le l e = e1) as eeq.
    assert (e1 = incr_env_by_1 e (loopivname l) (nat_to_int iv)) as
        e1_is_incr_e_at_loopivname.
    eapply continue_sblock_incr_by_1_sseq_sif.
    admit.
    eapply match_stmt_has_same_effect'.
    eassumption.
    eassumption.
    eassumption.
    exact exec_cms_inner_block.
    rewrite lval. simpl.
    eassumption.
    eapply match_stmt_does_not_alias.
    eassumption.
    rewrite e1_is_incr_e_at_loopivname.
    unfold env_incr_iv_wrt_loop.
    unfold incr_env_by_1.
    unfold nat_to_val.
    unfold nat_to_int.
    rewrite lval. simpl.
    assert (lsched = id) as lsched_id.
    rewrite <- loopsched.
    rewrite lval.
    simpl.
    reflexivity.
    rewrite lsched_id.
    unfold id.
    rewrite transfer_nat_add_to_int_add.
    rewrite leval. simpl.
    reflexivity.
    rewrite leval. simpl.
    assumption.
    
    
    (* --- *)
    subst m1 e1.
    eapply exec_cms_loop.
    eassumption.




    + rename H8 into out_neq_normal.
      contradiction.
Admitted.
       
      
    
    
  




