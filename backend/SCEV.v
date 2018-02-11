Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.
Require Import AST.
Require Import Cop.
Require Import Cminor.
Require Import Integers.
Require Import Maps.

Definition nat_to_int (n: nat): int := (Int.repr (Z.of_nat n)).
Definition z_to_int (z: Z): int := (Int.repr z).
Definition z_to_val (z: Z) : val := Vint (Int.repr z).

Hint Unfold z_to_val.
Hint Unfold z_to_int.
Hint Transparent z_to_val.
Hint Transparent z_to_int.

(* scev for identifier "i" that starts with first val and recurrences with val *)
Inductive scev: Type :=
  SCEVAddRec: Z -> Z -> scev.

Definition numiters := positive.

Fixpoint eval_scev (s: scev) (n: nat) : Z :=
  match s with
    | SCEVAddRec init step => match n with
                             | 0%nat => init
                             | S n' => step +  (eval_scev s n')
                             end
  end.




Definition oned_loop (n: nat) (ivname: ident) (inner_stmt: Cminor.stmt): Cminor.stmt :=
Sloop (
    Sblock (
        Cminor.Sseq (Sifthenelse (Ebinop
                                    (Ocmp Clt)
                                    (Evar ivname)
                                    (Econst (Ointconst (nat_to_int n))))
                                 (Sskip)
                                 (Sexit 1) (* this is a hack, there is no reason it has to be 0 *)
                    )
                    (inner_stmt)
      )
  ).

Definition iv_init (ivname: ident) (iv_init_val: Z): Cminor.stmt :=
  Sassign ivname (Econst (Ointconst (Int.repr iv_init_val))).


Definition oned_loop_with_init (n: nat)
           (ivname: ident)
           (iv_init_val: Z)
           (inner_stmt: Cminor.stmt): Cminor.stmt :=
  Cminor.Sseq
    (iv_init ivname iv_init_val)
    (oned_loop n ivname inner_stmt).


Definition oned_loop_add_rec (n: nat) (ivname: ident) (iv_init_val: Z) (add_val: Z) : Cminor.stmt :=
  oned_loop_with_init n ivname iv_init_val
            (Sassign
               ivname
               (Ebinop
                  Oadd
                  (Evar ivname)
                  (Econst (Ointconst (Int.repr add_val))))).

Lemma iv_init_sets_iv_value: forall (ivname: ident)
                               (iv_init_val: Z),
    
   forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv),
    exec_stmt ge f sp e m
              (iv_init ivname iv_init_val) E0
              e' m' Out_normal -> e' ! ivname = Some (z_to_val iv_init_val).
  intros until ge.
  intros exec.
  inversion exec.
  subst.
  rewrite PTree.gss.
  inversion_clear H4.
  subst.
  inversion_clear H.
  auto.
Qed.

Lemma eval_expr_is_function:
  forall  (a: expr) (sp: val) (ge: genv) (e: env) (m: mem) (v v': val),
    eval_expr ge sp e m a v ->
    eval_expr ge sp e m a v' ->
    v = v'.
Proof.
  intros a.
  induction a;
    intros until v';
  intros eval_to_v;
  intros eval_to_v';
  inversion eval_to_v; inversion eval_to_v'; subst;
    try(rewrite H3 in H0; inversion H0; auto).
  (* unary op*)
  - 
    rename H3 into eval_unop_u_v1.
    rename H8 into eval_unop_u_v2.
    rename H1 into eval_a_to_v1.
    rename H6 into eval_a_to_v2.
    assert (v1 = v2) as v1_eq_v2.
    eapply IHa.
    apply eval_a_to_v1.
    apply eval_a_to_v2.
    rewrite v1_eq_v2 in *.
    assert (Some v = Some v') as inv_target.
    rewrite <- eval_unop_u_v1.
    rewrite <- eval_unop_u_v2.
    reflexivity.
    inversion inv_target. auto.

  - (* binary op *)
    assert (v1 = v3) as v1_eq_v3.
    eapply IHa1.
    apply H2.
    apply H9.

    assert (v2 = v4) as v2_eq_v4.
    eapply IHa2.
    apply H4.
    apply H11.
    rewrite v1_eq_v3 in *.
    rewrite v2_eq_v4 in *.
    clear v1_eq_v3. clear v2_eq_v4.
    rewrite H5 in H12.
    inversion H12.
    auto.

    (* Load? Why is this a different case? *)
  -
    assert (vaddr = vaddr0) as vaddr_eq_vaddr0.
    eapply IHa.
    exact H1. exact H6.
    rewrite vaddr_eq_vaddr0 in *.
    rewrite H3 in H8.
    inversion H8.
    auto.
Qed.
  

Check(eval_exprlist).
Check (eval_funcall_ind2).
Check (exec_stmt_ind2).

(* genv -> val -> env -> mem -> list expr -> list val *)
Lemma eval_exprlist_is_function:
  forall  (list_a: list expr) (sp: val) (ge: genv) (e: env) (m: mem) (vs vs': list val),
    eval_exprlist ge sp e m list_a vs -> 
    eval_exprlist ge sp e m list_a vs' ->
    vs = vs'.
Proof.
  intros list_a.
  induction list_a;
    intros until vs';
    intros eval_vs;
    intros eval_vs';
    inversion eval_vs; inversion eval_vs'; subst; try auto.
  assert (v1 = v0) as v1_eq_v0.
  eapply eval_expr_is_function; eassumption.
  rewrite v1_eq_v0 in *.
  assert (vl = vl0) as vl_eq_vl0.
  eapply IHlist_a; eassumption.
  rewrite vl_eq_vl0.
  reflexivity.
Qed.

Lemma outcome_result_value_is_function:
  forall (o: outcome) (t: option typ) (v v' : val),
    outcome_result_value o t v ->
    outcome_result_value o t v' ->
    v = v'.
Proof.
  intros o.
  induction o; intros until v';
  intros out_v out_v'.

  - (* out_normal *)
    inversion out_v. inversion out_v'. subst; try auto.

  -  (* out_exit *)
    inversion out_v.

  - (*out_return *)
  unfold outcome_result_value in *.
  destruct o.
  + inversion out_v. inversion out_v'. subst. auto.
  + subst. auto.

  -  (* Out_taicall_return *)
  unfold outcome_result_value in *.
  subst. auto.
Qed.

Lemma outcome_free_mem_is_function:
  forall (out: outcome) (m: mem) (sp: block) (sz: Z),
  forall (m' m'': mem),
    outcome_free_mem out m sp sz m' ->
    outcome_free_mem out m sp sz m'' ->
    m' = m''.
Proof.
  intro out.
  induction out;
  intros until m''; intros outcome_m' outcome_m'';
  inversion outcome_m'; inversion outcome_m'';
    subst; try (rewrite H0 in H1; inversion H1; auto). try reflexivity.
Qed.
  
Lemma funsig_is_inj: forall (fd fd': fundef),
    funsig fd = funsig fd' -> fd = fd'.
Proof.
  intros.
Abort.
  
(* TODO: this was proof-hacked. Do this nicely *)
Lemma bool_of_val_is_function: forall (v: val) (b b': bool),
    Val.bool_of_val v b ->
    Val.bool_of_val v b' ->
    b = b'.
Proof.
  intros until b'.
  intros valb valb'.
  induction b.

  - induction b'.
    + inversion valb.
      inversion valb'.
      subst. auto.

    + inversion valb.
      inversion valb'.
      subst.
      inversion H0. auto.

  - induction b'.
    + inversion valb. inversion valb'.
      subst.
      inversion H0.
      auto.

    + auto.
Qed.
  

Lemma switch_argument_is_function:
  forall (b: bool) (v : val) (out out': Z),
    Switch.switch_argument b v out -> 
    Switch.switch_argument b v out' ->
    out = out'.
Proof.
  intros.
  inversion H; inversion H0; subst; try (inversion H5; auto).
Qed.


  
Check (external_call).

Lemma external_functions_sem_is_function:
  forall name (sg: signature) (ge: genv) (args: list val) (m mout mout': mem) (tr tr': trace)
    (v v': val),
 external_functions_sem name sg ge args m tr v mout ->
 external_functions_sem name sg ge args m tr' v' mout' ->
 tr = tr' /\ v = v' /\ mout = mout'.

Proof.
Admitted.


Lemma volatile_load_sem_is_function:
  forall (chunk: memory_chunk)
    (ge: genv)
    (args: list val)
    (m mout mout': mem)
    (tr tr': trace)
    (v v': val),
  volatile_load_sem chunk ge args m tr v mout ->
    volatile_load_sem chunk ge args m tr' v' mout' ->
    tr = tr' /\ v = v' /\ mout = mout'.
Proof.
Admitted.

Lemma external_call_is_function: forall (ef: external_function),
    forall (ge: genv) (args: list val) (m mout mout': mem) (tr tr': trace) (v v': val),
      external_call ef ge args m
                    tr v mout ->
      external_call ef ge args m
                    tr' v' mout' ->
      tr = tr' /\ v = v' /\ mout = mout'.
Proof.
  intros until v'.
  intros call1 call2.
  induction ef;
    unfold external_call in *;
    try (eapply external_functions_sem_is_function; eassumption).
  eapply volatile_load_sem_is_function; eassumption.
  (* mother of god, this is just annoying as fuck case analysis *)
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Admitted.


Lemma int_eq_dec': forall (i i': int), i = i' \/ i <> i'.
Proof.
  intros.
  assert ({i = i'} + {i <> i'}).
  apply Int.eq_dec.
  destruct H.
  left. assumption.
  right.
  assumption.
Qed.


Lemma int64_eq_dec': forall (i i': int64), i = i' \/ i <> i'.
Proof.
  intros.
  assert ({i = i'} + {i <> i'}).
  apply Int64.eq_dec.
  destruct H.
  left. assumption.
  right.
  assumption.
Qed.

Lemma val_eq_dec: forall (v v': val), v = v' \/ v <> v'.
  intros.
  assert ({v = v'} + {v <> v'}).
  apply Val.eq.
  destruct H; auto.
Qed.

Lemma outcome_eq_dec: forall (o o': outcome), o = o' \/ o <> o'.
Proof.
  intros.
  decide equality.
  omega.
  decide equality.
  apply val_eq_dec.
  apply val_eq_dec.
Qed.
  

Check (eval_funcall).
(* Check out how "eval_funcall_exec_stmt_steps" does this in CMinor *)
Check (eval_funcall_exec_stmt_ind2).
Lemma eval_stmt_funcall_is_function: forall ge,
  (forall m fd args t m' res,
      eval_funcall ge m fd args t m' res ->
      (forall m'' res' t',
          eval_funcall ge m fd args t' m'' res' -> m' = m'' /\ res = res' /\ t = t'
  )) 
  /\(forall f sp e m s t e' m' out,
       exec_stmt ge f sp e m s t e' m' out ->
       (forall e'' m'' out' t',
           exec_stmt ge f sp e m s t' e'' m'' out' ->
           m' = m'' /\ out = out' /\ e' = e'' /\ t = t')).
Proof.
  intros ge.
  apply eval_funcall_exec_stmt_ind2; intros.

  - (* eval funcall internal *)
  inversion H5. subst.

  assert ((m4, sp0) = (m1, sp)) as m_sp_eq.
  rewrite <- H. rewrite <- H7. reflexivity.
  inversion m_sp_eq.
  rewrite H6 in *. rewrite H8 in *.
  clear H6.
  clear H8.
  clear m_sp_eq.

  specialize (H2 _ _ _ _ H9).
  inversion H2.
  inversion H6.
  subst.
  clear H6.
  clear H2.
  assert (m3 = m'') as m3_eq_m''.
  eapply outcome_free_mem_is_function; eassumption.
  rewrite m3_eq_m'' in *. clear m3_eq_m''.
  assert (vres = res') as vres_eq_res'.
  eapply outcome_result_value_is_function; eassumption.
  rewrite vres_eq_res' in *.
  inversion H11.
  rewrite H2 in *.
  auto.

  -  (* eval funcall inernal *)
    inversion H0. subst.
    assert (t = t' /\ res = res' /\ m' = m'').
    eapply external_call_is_function; eassumption.
    intuition.
  -  (* Sskip *)
    inversion H. subst.
    auto.
  -  (* Sasssign *)
    inversion H0. subst.
    assert (v = v0) as v_eq_v0.
    eapply eval_expr_is_function; eassumption.
    rewrite v_eq_v0 in *. auto.

  -  (* Sstore *)
    inversion H2. subst.
    assert (v = v0) as v_eq_v0.
    eapply eval_expr_is_function; eassumption.
    rewrite v_eq_v0 in *. auto.
    
    assert (vaddr = vaddr0) as vaddr_eq_vaddr0.
    eapply eval_expr_is_function; eassumption.
    rewrite vaddr_eq_vaddr0 in *.
    assert (Some m' = Some m'') as eq_some_m'_m''.
    rewrite <- H16. rewrite <- H1. reflexivity.
    inversion eq_some_m'_m'' as [m_eq_m'].
    rewrite m_eq_m' in *. auto.

  -  (* Scall. Gulp *)
    inversion H6. subst.

    assert(vf = vf0) as vf_eq_vf0.
    eapply eval_expr_is_function; eassumption.
    rewrite vf_eq_vf0 in *. clear vf_eq_vf0.

    
    assert (fd = fd0) as fd_eq_fd0.
    rewrite H1 in H17. 
    inversion H17. auto.
    rewrite fd_eq_fd0 in *. clear fd_eq_fd0.

    assert (vargs = vargs0) as vargs_eq.
    eapply eval_exprlist_is_function; eassumption.
    rewrite vargs_eq in *. clear vargs_eq.

    specialize (H4 _ _ _ H23).
    inversion H4.
    rewrite H2 in *.
    destruct H5.
    rewrite H7 in *.
    rewrite H5 in *.
    auto.

  - (*Sbuiltin *)
    inversion H2. subst.

    assert (vargs = vargs0) as vargs_eq.
    eapply eval_exprlist_is_function; eassumption.
    rewrite vargs_eq in *.
    assert (t = t' /\ vres = vres0 /\ m' = m'').
    eapply external_call_is_function; eassumption.
    destruct H1 as [teq [vreseq meq]].
    rewrite teq, vreseq, meq in *.
    auto.

  - (*S IfThenElse *)
    inversion H3.
    subst.
    assert (v = v0) as veq.
    eapply eval_expr_is_function; eassumption.
    rewrite veq in *. clear veq.
    assert (b0 = b) as beq.
    eapply bool_of_val_is_function; eassumption.
    rewrite beq in *. clear beq.

    specialize (H2 _ _ _ _ H17).
    inversion H2.
    inversion H5.
    subst.
    auto.

  - (* Sseq *)
    inversion H4.

    + subst.
    specialize (H0 _ _ _ _ H7).
    destruct H0 as [meq [_ [eeq teq]]].
    rewrite meq,  teq, eeq in *.
    clear meq. clear eeq. clear teq.

    
    specialize (H2 _ _ _ _ H12).
    destruct H2 as [meq [outeq [eeq teq]]].
    rewrite meq, outeq, teq, eeq in *.
    clear meq. clear outeq. clear eeq. clear teq.
    auto.

    (* out != out_normal *)
    + subst.
      specialize (H0 _ _ _ _ H11).
      destruct H0.
      destruct H3.
      assert (out' = Out_normal /\ out' <> Out_normal) as contra.
      split; auto.
      inversion contra.
      contradiction.
  -  (* Sseq again? *)
    intros.
    inversion H2.
    + subst.
      specialize (H0 _ _ _ _ H5).
      destruct H0 as [meq [outeq [eeq teq]]].
      rewrite outeq, meq, eeq, teq in *.
      rename H1 into contra.
      contradiction.
    + subst.
      specialize (H0 _ _ _ _ H9).
      auto.
  -  (* Sloop *)
    inversion H4.

    + subst.
    specialize (H0 _ _ _ _ H6).
    destruct H0 as [meq [_ [eeq teq]]].
    rewrite meq, eeq, teq in *.
    clear meq.
    clear eeq.
    clear teq.
    specialize (H2 _ _ _ _ H7).
    destruct H2 as [meq [outeq [eeq teq]]].
    rewrite meq, outeq, eeq, teq in *.
    auto.

    + subst.
      specialize (H0 _ _ _ _ H6).
      destruct H0 as [_ [out_normal _]].
      assert (Out_normal = out' /\  Out_normal <> out') as contra. auto.
      inversion contra.
      contradiction.

  -  (* Sloop *)
    inversion H2;
      subst;
      specialize (H0 _ _ _ _ H4);
      destruct H0  as [meq [outeq [eeq teq]]];
      rewrite meq, outeq, eeq, teq in *.
    try contradiction. try auto.

  -  (* Sblock *)
    inversion H1. subst.
    specialize (H0 _ _ _ _ H7).
    destruct H0 as [meq [outeq [eeq teq]]].
    rewrite meq, outeq, eeq, teq in *.
    auto.

  - (* Sexit *)
    inversion H. subst. auto.

  - (* Sswitch *)
    inversion H1. subst.
    assert (v0 = v) as veq.
    eapply eval_expr_is_function; eassumption.
    rewrite veq in *.

    assert (n = n0) as neq.
    eapply switch_argument_is_function; eassumption.
    rewrite neq in *.
    auto.


  -  (* Sreturn *)
    inversion H. subst.
    auto.

  -  (* Sreturn, Some *)
    inversion H0. subst.
    assert (v = v0) as veq.
    eapply eval_expr_is_function; eassumption.
    rewrite veq in *.
    auto.

  - (* Stailcall (is this going to be hard?) *)
    inversion H6. subst.

    assert(m' = m'0) as m'eq.
    rewrite H22 in H3. inversion H3. auto.
    rewrite m'eq in *. clear m'eq.

    assert (vf = vf0) as vfeq.
    eapply eval_expr_is_function; eassumption.
    rewrite vfeq in *.
    clear vfeq.
    
    assert (fd = fd0) as fdeq.
    rewrite  H14 in H1.
    inversion H1. auto.
    rewrite fdeq in *.
    clear fdeq.

    assert (vargs0 = vargs) as vargseq.
    eapply eval_exprlist_is_function; eassumption.
    rewrite vargseq in *.
    
    specialize (H5 _ _ _ H23).
    destruct H5 as [meq [vreseq teq]].
    rewrite meq, vreseq, teq in *.
    auto.
Qed.

      
  