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

(* What in the fuck, why does match_traces only take 1 trace value? *)
Inductive match_traces_long: genv -> trace -> trace -> Prop :=
| Match_traces_long_E0: forall (ge: genv), match_traces_long ge E0 E0
| Match_traces_long_eq: forall (t t': trace) (ge: genv),  t = t' -> match_traces_long ge t t'
| Match_traces_long_match: forall (ge: genv) (t t':trace), match_traces ge t t' -> match_traces_long ge t t'
| Match_traces_long_app: forall (ge: genv) (t1 t1' t2 t2': trace),
    match_traces_long  ge t1 t1' ->
    match_traces_long ge t2 t2' ->
    match_traces_long ge (t1 ** t2) (t1' ** t2').

  

Lemma external_call_is_function: forall (ef: external_function),
    forall (ge: genv) (args: list val) (m mout mout': mem) (tr tr': trace) (v v': val),
      external_call ef ge args m
                    tr v mout ->
      external_call ef ge args m
                    tr' v' mout' ->
      match_traces_long ge tr tr' /\ v = v' /\ mout = mout'.
Proof.
  intros until v'.
  intros call1 call2.
  assert (match_traces ge tr tr').
  eapply external_call_match_traces; eassumption.
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
Check (eval_funcall_exec_stmt_ind2).


(* Check out how "eval_funcall_exec_stmt_steps" does this in CMinor *)
Check (eval_funcall_exec_stmt_ind2).
Lemma eval_stmt_funcall_is_function: forall ge,
  (forall m fd args t m' res,
      eval_funcall ge m fd args t m' res ->
      (forall m'' res' t',
         eval_funcall ge m fd args t' m'' res' -> t = t' -> m' = m'' /\ res = res')
  ) 
  /\(forall f sp e m s t e' m' out,
       exec_stmt ge f sp e m s t e' m' out ->
       (forall e'' m'' out' t',
           exec_stmt ge f sp e m s t'  e'' m'' out' ->
           m' = m'' /\ out = out' /\ e' = e'')).
Proof.
  intros ge.
  apply eval_funcall_exec_stmt_ind2; intros.

  
  inversion H5. subst.

  - (* Internal Call *)
  assert (m1 = m4 /\ sp = sp0) as m_sp_eq.
  cut ((m1, sp) = (m4, sp0)). intros tup_eq. inversion tup_eq. auto.
  rewrite <- H.
  rewrite <- H8.
  reflexivity.
  destruct m_sp_eq as [meq speq].
  subst.

  remember H2 as stmt_eq_ind.
  clear Heqstmt_eq_ind.

  specialize (H2 _ _ _ _  H10).
  destruct H2 as [meq [outeq eeq]].
  subst.


  assert(m3 = m'') as meq.
  eapply outcome_free_mem_is_function; eassumption.
  
  assert (vres = res') as reseq.
  eapply outcome_result_value_is_function; eassumption.

  auto.

  - (* External *)
    intros.
     inversion H0.
     subst.
     apply and_comm.
     eapply external_call_deterministic; eassumption.
     
     
  - (* Sskip *)
    inversion H. subst.
    auto.
    
  - inversion H0. subst.
    assert (v = v0) as veq.
    eapply eval_expr_is_function; eassumption.
    subst.
    auto.
    
  - (* Sstore *)
    inversion H2. subst.
    assert (v = v0) as veq.
    eapply eval_expr_is_function; eassumption.

    assert (vaddr = vaddr0) as vaddreq.
    eapply eval_expr_is_function; eassumption.

    subst.

    assert (Some m' = Some m'') as some_meq.
    rewrite <- H16.
    rewrite <- H1.
    reflexivity.
    inversion some_meq.
    subst.

    auto.

    
  - intros.
    inversion H6. subst.

    
    admit.
  - intros. admit.
  - intros. admit.
  - intros.
    inversion H4. subst.
    specialize (H0 _ _ _ _ H7).
    destruct H0 as [meq [_ eeq]].
    subst.

    
    specialize (H2 _ _ _ _ H12).
    destruct H2  as [meq [outeq eeq]].
    subst.

    auto.

    subst.
    specialize (H0 _ _ _ _ H11).
    destruct H0 as [meq [outeq eeq]].

    rewrite outeq in H16.
    contradiction.

  -  inversion H2. subst.
     specialize (H0 _ _ _ _ H5).
     destruct H0  as [meq [outeq eeq]].
     rewrite outeq in H1.
     contradiction.
     subst.
     specialize (H0 _ _ _ _ H9).
     destruct H0 as [meq [outeq eeq]].
     subst.
     auto.


  - admit.

  - intros. admit.
  - intros. admit.
   


    