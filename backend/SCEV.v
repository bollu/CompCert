Require Import Coqlib Maps.
Require Import AST Integers Values Events Memory Globalenvs Smallstep.
Require Import Op Registers.
Require Import AST.
Require Import Cop.
Require Import Cminor.
Require Import Integers.
Require Import Maps.

Definition nat_to_int (n: nat): int := (Int.repr (Z.of_nat n)).
Definition nat_to_val (n: nat): val := Vint (Int.repr (Z.of_nat n)).
Definition z_to_int (z: Z): int := (Int.repr z).
Definition z_to_val (z: Z) : val := Vint (Int.repr z).

Hint Unfold z_to_val.
Hint Unfold z_to_int.
Hint Unfold nat_to_int.
Hint Transparent z_to_val.
Hint Transparent z_to_int.
Hint Transparent nat_to_int.

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



Definition oned_loop_inner_block (n: int) (ivname: ident) (inner_stmt: Cminor.stmt): Cminor.stmt :=
    Sblock (
        Cminor.Sseq (Sifthenelse (Ebinop
                                    (Ocmpu Clt)
                                    (Evar ivname)
                                    (Econst (Ointconst n)))
                                 (Sskip)
                                 (Sexit 1)
                    )
                    (inner_stmt)
      ).

Definition oned_loop (n: int) (ivname: ident) (inner_stmt: Cminor.stmt): Cminor.stmt :=
  Sloop (
      oned_loop_inner_block n ivname inner_stmt
  ).

Definition z_init (ivname: ident) (z_init_val: Z): Cminor.stmt :=
  Sassign ivname (Econst (Ointconst (Int.repr z_init_val))).



Definition oned_loop_add_rec (n: int)
           (ivname: ident)
           (scevname: ident)
           (scev_init_val: Z)
           (scev_add_val: Z) : Cminor.stmt :=
  Cminor.Sseq
    (z_init ivname 0)
    (Cminor.Sseq
       (z_init scevname scev_init_val)
       (oned_loop n ivname (
                    Cminor.Sseq
                      (Sassign ivname (Ebinop Oadd (Evar ivname) (Econst (Ointconst (z_to_int 1)))))
                      (Sassign scevname (Ebinop Oadd (Evar scevname) (Econst (Ointconst (z_to_int scev_add_val)))))
       ))
    ).

Lemma z_init_sets_z_value: forall (ivname: ident)
                               (z_init_val: Z),
    
   forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv),
    exec_stmt ge f sp e m
              (z_init ivname z_init_val) E0
              e' m' Out_normal -> e' ! ivname = Some (z_to_val z_init_val).
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

Lemma destruct_trace_app_eq_E0:
  forall (t1 t2: trace),
    E0 = t1 ** t2 ->
    t1 = E0 /\ t2 = E0.
Proof.
  intros.
  induction t1.
  - induction t2.
    +  simpl. auto.
    +  inversion H.
  - inversion H.
Qed.
  


(* Note that this result is weaker than what I originally wanted to prove. This
just proves that two statements run in the same initial configuration,
**that have no trace** (that is, no external world interaction), will have
the same output.

Note that "external world interaction" is:
- volatile load, store
- external function call

This does not really matter for our polyhedral use case, since we would most likely
be fully blocked from analysing by either of those.

However, in principle, I should be able to prove that:

Two statements, s1 and s2, that start at the same initial configuaration and
** produce the same trace ** t will have the same output.

Note that "produce the same trace" is stronger than "no trace". This intuitively makes
sense. However, you get blocked in the SSeq case.

Roughly, what happens is:

conceptually,  this is the pairing we want
------------------------------------------
s1 (stmt) paired with t1 (trace)
s2 (stmt) paired with t2 (trace)

s1' -> t1'
s2' -> t2'

However,

this is the pairing we get
--------------------------

Sequence s1 s2 -> t1 ++ t2
Sequence s1' s2' -> t1' ++ t2'

Note that this __does not let us conclude__
s1 -> t1, s2 -> t2. s1' -> t1', s2' -> t2'.

(Obviously. It is possible that for example,
t1 = [], t2 = [1, 2]
t1' = [1], t2' = [2]).


So, we need to somehow strengthen Sequence such that we
can derive that the individual components must "match up"?
I am not sure how to do this.
*)

Lemma exec_stmt_funcall_with_no_effect_is_function: forall ge,
  (forall m fd args (t:trace) m' res,
      eval_funcall ge m fd args t m' res ->
      t = E0 ->
      (forall m'' res',
         eval_funcall ge m fd args E0 m'' res' ->  m' = m'' /\ res = res')
  ) 
  /\(forall f sp e m s  (t:trace) e' m' out,
       exec_stmt ge f sp e m s t e' m' out ->
       t = E0 ->
       (forall e'' m'' out',
           exec_stmt ge f sp e m s E0 e'' m'' out' ->
           m' = m'' /\ out = out' /\ e' = e'')).
Proof.
  intros genv.
  apply eval_funcall_exec_stmt_ind2; intros.

  - (* Internal call *)
    inversion H6. subst.
    assert ((m1, sp) = (m4, sp0)) as m_sp_eq.
    rewrite <- H.
    rewrite <- H8.
    reflexivity.
    inversion m_sp_eq.
    subst.
    clear m_sp_eq.

    specialize (H2 eq_refl _ _ _ H10).
    destruct H2 as [meq [outeq eeq]].
    subst.

    assert (m3 = m'') as meq.
    eapply outcome_free_mem_is_function; eassumption.
    subst.

    assert (vres = res') as vreseq.
    eapply outcome_result_value_is_function; eassumption.
    subst.
    auto.
    
  - (* External call *)
    inversion H1. subst.
    apply and_comm.
    eapply external_call_deterministic; eassumption.

  - (* Sskip *)
    inversion H0. subst. auto.

  - (* Sassign *)
    inversion H1. subst.
    assert (v = v0) as veq.
    eapply eval_expr_is_function; eassumption.
    subst.
    auto.
  - (* Sstore *)
    inversion H3. subst.
    assert (v = v0) as veq.
    eapply eval_expr_is_function; eassumption.

    assert (vaddr = vaddr0) as vaddreq.
    eapply eval_expr_is_function; eassumption.

    subst.

    assert (Some m' = Some m'') as meq.
    rewrite <- H16. rewrite <- H1.
    reflexivity.

    inversion meq.
    subst.
    auto.

  - (* Scall *)
    inversion H7. subst.

     assert (vf = vf0) as vfeq.
     eapply eval_expr_is_function; eassumption.
     subst.

     assert (vargs = vargs0) as vargseq.
     eapply eval_exprlist_is_function; eassumption.
     subst.

     assert (Some fd = Some fd0) as some_fdeq.
     rewrite <- H18.
     rewrite <- H1.
     reflexivity.

     inversion some_fdeq.
     subst.
     clear some_fdeq.

     specialize (H4 eq_refl).
     specialize (H4 _ _ H24).
     destruct H4 as [meq vreseq].
     subst.

     auto.

  - (* Sbuiltin *)
    inversion H3. subst.

     assert (vargs = vargs0) as vargs_eq.
     eapply eval_exprlist_is_function; eassumption.
     subst.
     
     assert (vres = vres0 /\ m' = m'') as vres_m_eq.
     eapply  external_call_deterministic; eassumption.
     destruct vres_m_eq as [vres_eq m_eq].
     subst.
     auto.

  -  (* Sifthenelse *)
    inversion H4. subst.
    assert (v0 = v) as veq.
    eapply eval_expr_is_function; eassumption.
    subst.

    assert (b = b0) as beq.
    eapply bool_of_val_is_function; eassumption.
    subst.

    specialize (H2 eq_refl _ _ _ H18).
    destruct H2 as [meq [outeq eeq]].
    subst.
    auto.

    
  - (* Sseq *)
    rewrite H4 in H3.
    assert (t1 = E0 /\ t2 = E0) as t1_t2_eq_E0.
    apply destruct_trace_app_eq_E0.
    auto.

    destruct t1_t2_eq_E0 as [t1_eq_E0 t2_eq_E0].
    subst.

    specialize (H0 eq_refl).
    specialize (H2 eq_refl).
    clear H3.
    rename m'' into mgoal.
    rename out' into outgoal.
    rename e'' into egoal.

    inversion H5; subst.
    + 
      assert (t1 = E0 /\ t2 = E0).
      apply destruct_trace_app_eq_E0. assumption.
      destruct H3. subst.

      
      specialize (H0 _ _ _ H6).
      destruct H0 as [meq [_ eeq]]. subst.

      specialize (H2 _ _ _ H11).
      destruct H2 as [meq [outeq eeq]]. subst.
      auto.
    +
      specialize (H0 _ _ _ H10).
      destruct H0 as [_ [outgoal_normal _]].
      assert(Out_normal <> Out_normal) as contra.
      rewrite outgoal_normal. auto.

      contradiction.

  - (* Sseq *)
    inversion H3. subst.
     assert  (t1 = E0 /\ t2 = E0) as t1_t2_eq_t0.
     apply destruct_trace_app_eq_E0. eassumption.
     destruct t1_t2_eq_t0. subst.

     specialize (H0 eq_refl).
     specialize (H0 _ _ _ H6).
     destruct H0 as [_ [out_eq_normal _]].
     contradiction.

     
     subst.
     specialize (H0 eq_refl _ _ _ H10).
     destruct H0 as [meq [outeq eeq]].
     subst.
     auto.
  -  (* Sloop *)
    subst.
    assert (t1 = E0 /\ t2 = E0) as t1_t2_eq_E0.
    eapply destruct_trace_app_eq_E0. auto.
    destruct t1_t2_eq_E0.
    subst.
    clear H4.
    specialize (H0 eq_refl).
    specialize (H2 eq_refl).

    inversion H5.

    + subst.

    assert (t1 = E0 /\ t2 = E0) as dest.
    eapply destruct_trace_app_eq_E0. auto.
    destruct  dest.
    subst.
    
    specialize (H0 _ _ _ H4).
    destruct H0 as [meq [_ eeq]].
    subst.

    
    specialize (H2  _ _ _ H6).
    auto.

    + subst.
      specialize (H0 _ _ _ H4) as contra.
      destruct contra as [_ [out_eq _]].
      assert (Out_normal = out' /\ Out_normal <> out') as contra.
      intuition.
      destruct contra.
      contradiction.

  - (* Sloop *)
    inversion H3; subst.
    + assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
    apply destruct_trace_app_eq_E0. eassumption.
    destruct t1_t2_E0. subst.
    clear H11.

    specialize (H0 eq_refl _ _ _ H5).
    destruct H0 as [_ [out_normal _]].
    contradiction.

    +  specialize (H0 eq_refl _ _ _ H5).
       auto.

  - (* Sloop *)
    subst.
    specialize (H0 eq_refl).
    inversion H2. subst.

    specialize (H0 _ _ _ H7).
    destruct H0 as [meq [outeq eeq]].
    subst.

    auto.

  - (* SExit *)
    inversion H0. subst.
     auto.

  - (* Sswitch *)
    inversion H2. subst.
     assert (v = v0) as veq.
     eapply eval_expr_is_function; eassumption.
     subst.

     assert (n = n0) as neq.
     eapply switch_argument_is_function; eassumption.
     subst.
     auto.

  - (* Sreturn *)
    inversion H0. subst.
    auto.

  -  (* Sreturn (some case) *)
    inversion H1. subst.
    assert (v = v0).
    eapply eval_expr_is_function; eassumption.
    subst.
    auto.

  - (* Stailcall *)
    inversion H7.
    subst.

    assert (vargs = vargs0) as vargseq.
    eapply eval_exprlist_is_function; eassumption.
    subst.

    assert (vf = vf0).
    eapply eval_expr_is_function; eassumption.
    subst.

    assert (Some m' = Some m'0) as m'_eq.
    rewrite <- H23.
    rewrite <- H3.
    auto.
    inversion m'_eq. subst.
    clear m'_eq.

    assert (Some fd = Some fd0) as fdeq.
    rewrite <- H15.
    rewrite <- H1.
    reflexivity.
    inversion fdeq. subst.

    specialize (H5 eq_refl _ _ H24).
    destruct H5 as [meq vreseq].
    subst.
    auto.
Qed.
    

Lemma bool_of_val_to_bool_false: forall (b: bool),
    Val.bool_of_val Vfalse b -> b = false.
Proof.
  intros b b_val_eq_false.
  inversion b_val_eq_false.
  assert (Int.eq Int.zero Int.zero = true) as Ieq.
  apply Int.eq_true.
  rewrite Ieq.
  simpl.
  reflexivity.
Qed.

(* Why do I need to phrase this as:
<hypothesis> -> aRb -> aRc -> b = c?

Why can I not simply say "<hypothesis> -> aRb"?
Intuitively, I should be able to, because I have shown that this relation
is a function, so I can talk about a unique aRb. However, I am not sure
how to convince Coq that I am allowed to talk aobut this unique aRb
*)
Lemma if_cond_with_failing_branch_will_return_else:
  forall (cond: expr) (sthen selse: Cminor.stmt),
  forall (m m' m'': mem)
    (e e' e'': env) (f: function) (sp: val) (ge: genv) (o o' o'': outcome),

    eval_expr ge sp e m cond Vfalse ->
    exec_stmt ge f sp e m (selse) E0 e' m' o' ->
    exec_stmt ge f sp e m
              (Cminor.Sifthenelse cond sthen selse) E0 e'' m'' o'' ->
     m' = m'' /\ o' = o'' /\ e' = e''. 
Proof.
  intros until o''.
  intros cond_false.
  intros exec_else.
  intros exec_sifthenelse.
  inversion exec_sifthenelse. subst.
  assert (v = Vfalse) as veq.
  eapply eval_expr_is_function; eassumption.
  subst.
  assert (b = false) as b_is_false.
  apply bool_of_val_to_bool_false. auto.
  subst.

  eapply exec_stmt_funcall_with_no_effect_is_function.
  eassumption.
  auto.
  eassumption.
Qed.

Lemma eval_constnat_val: forall (ge: genv) (sp: val) (e: env) (m: mem)
    (n: nat) (v: val),
    eval_expr ge sp e m (Econst (Ointconst (nat_to_int n))) v ->
    v = Vint (nat_to_int n).
Proof.
  intros until v.
  intros eval_v.
  inversion eval_v.
  subst.
  inversion H0.
  subst.
  reflexivity.
Qed.


Lemma eval_constint_val: forall (ge: genv) (sp: val) (e: env) (m: mem)
    (i: int) (v: val),
    eval_expr ge sp e m (Econst (Ointconst i)) v ->
    v = Vint (i).
Proof.
  intros until v.
  intros eval_v.
  inversion eval_v.
  subst.
  inversion H0.
  subst.
  reflexivity.
Qed.

Lemma eval_evar_val: forall (ge: genv) (sp: val) (e: env) (m: mem)
                       (ivname:  ident) (v v': val),
    e ! ivname = Some v' ->
  eval_expr ge sp e m (Evar ivname) v ->
  v = v'.
Proof.
  intros until v'.
  intros e_at_ivname.
  intros eval_evar.
  inversion eval_evar. subst.
  assert (Some v = Some v') as some_eq.
  rewrite <- H0. rewrite <- e_at_ivname.
  reflexivity.

  inversion some_eq.
  auto.
Qed.
  

Example exit_sexit:
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (o: outcome),
    forall (n: nat),
    exec_stmt ge f sp e m (Sexit n) E0 e' m' o ->
    o = Out_exit n /\ e = e' /\ m = m'.
Proof.
  intros.
  inversion H.
  subst.
  auto.
Qed.

Example exit_sif:
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (o: outcome),
  forall (n: nat) (econd: expr),
    eval_expr ge sp e m econd Vfalse ->
    exec_stmt ge f sp e m
              (Sifthenelse econd
                 (Sskip)
                 (Sexit n)
              )
              E0 e' m' o ->
    o = Out_exit n /\ e = e' /\ m = m'.
Proof.
  intros until econd.
  intros econd_is_false.
  intros execif.
  inversion execif.
  subst.
  rename H12 into execif_bool.

  assert (v = Vfalse).
  eapply eval_expr_is_function; eassumption.
  subst.
  
  assert (b = false) as bf.
  apply bool_of_val_to_bool_false. eassumption.
  subst.

  inversion execif_bool.
  subst.
  auto.
Qed.

(* Yes, this helped get me unstuck! I now realise that the first clause
provides us with a contradiciton that Out_normal = Out_exit n.
This is because of us inverting the "seq"
 *)
Example exit_sseq_sif:
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (o: outcome),
  forall (n: nat) (sinner: stmt) (econd: expr),
    eval_expr ge sp e m econd Vfalse ->
    exec_stmt ge f sp e m
              (Cminor.Sseq 
                 (Sifthenelse econd
                    (Sskip)
                    (Sexit n)
                 )
                 sinner)
              E0 e' m' o ->
    o = Out_exit n /\ e = e' /\ m = m'.
Proof.
  intros until econd.
  intros econd_false.
  intros seq.
  assert (forall o' m1 e1, exec_stmt ge f sp e m
         (Sifthenelse econd Sskip (Sexit n)) E0 e1
         m1 o' -> o' = (Out_exit n) /\ e = e1 /\ m = m1) as out_exit.
  intros.
  eapply exit_sif; eassumption.

  
  inversion seq.
  - (* normal trace of S1 in SSeq. not happening *)
    subst.
  assert (t1 = E0 /\ t2 = E0) as ht1t2. eapply destruct_trace_app_eq_E0; eassumption.
  destruct ht1t2 as [t1E0 t2E0]. subst.
  specialize (out_exit _ _ _  H1).
  destruct out_exit as [out_contra _].
  inversion out_contra.
  
  - (* Early quit of S1. correct case *)
    subst.
    specialize (out_exit _ _ _ H5).
    destruct out_exit as [oeq [eeq meq]].
    subst.
    auto.
Qed.

Example exit_sblock_sseq_sif:
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (o: outcome),
  forall (n: nat) (sinner: stmt) (econd: expr),
    (n > 0)%nat ->
    eval_expr ge sp e m econd Vfalse ->
    exec_stmt ge f sp e m
              (Cminor.Sblock
                 (Cminor.Sseq 
                    (Sifthenelse econd
                                 (Sskip)
                                 (Sexit n)
                    )
                    sinner)
              )
              E0 e' m' o ->
    o = Out_exit (n - 1) /\ e = e' /\ m = m'.
Proof.
  intros until econd.
  intros n_gt_0.
  intros econd_is_false.
  intros block.
  inversion block; subst.
  assert (out = Out_exit n /\ e = e' /\ m = m').
  eapply exit_sseq_sif; eassumption.
  destruct H as [outeq eeq meq].
  subst.
  destruct n.
  - (* n = 0 *)inversion n_gt_0.
  - (* n = S n' *)
    unfold outcome_block.
    simpl.
  assert ((n - 0 = n)%nat) as stupid. omega.
  rewrite stupid.
  auto.
Qed.

  
(* Definition oned_loop_inner_block
(n: nat) (ivname: ident) (inner_stmt: Cminor.stmt): Cminor.stmt := *)

Lemma exit_oned_loop_inner_block:
  forall (n: int) (ivname: ident) (inner_stmt: Cminor.stmt),
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (o: outcome),
    eval_expr ge sp e m (Ebinop
       (Ocmpu Clt)
       (Evar ivname)
       (Econst (Ointconst n))) Vfalse ->
    exec_stmt ge f sp e m (oned_loop_inner_block n ivname inner_stmt)
              E0 e' m' o ->
    o = Out_exit 0 /\ e = e' /\ m = m'.
Proof.
  intros until o.
  intros ivval_gt_n.
  intros exec_block.
  eapply exit_sblock_sseq_sif with (n := 1%nat).
  omega.
  eassumption.
  eassumption.
Qed.


Lemma exit_oned_loop:
  forall (n: int) (ivname: ident) (inner_stmt: Cminor.stmt),
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (o: outcome),
    eval_expr ge sp e m (Ebinop
       (Ocmpu Clt)
       (Evar ivname)
       (Econst (Ointconst n))) Vfalse ->
    exec_stmt ge f sp e m (oned_loop n ivname inner_stmt)
              E0 e' m' o ->
    o = Out_exit 0 /\ e = e' /\ m = m'.
Proof.
  intros until o.
  intros ivval_gt_n.
  intros exec_loop.

  inversion exec_loop; subst.

  - (* This case can't work, since it assumes the block exits with Out_normal, which
    it does not *)

    rename H0 into exec_block.
    rename H1 into eval_loop_iters.

    assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
    eapply destruct_trace_app_eq_E0; eassumption.
    destruct t1_t2_E0 as [t1_e0 t2_e0].
    subst.

    assert (forall e' m' o,
               exec_stmt ge f sp e m (oned_loop_inner_block n ivname inner_stmt) E0 e' m' o ->
               o = Out_exit 0) as force_out_exit.
    intros.
    eapply exit_oned_loop_inner_block.
    eassumption.
    eassumption.
    specialize (force_out_exit e1 m1 _ exec_block).
    inversion force_out_exit.

  unfold Int.cmpu.
  - (* The loop does not execute, since we exit from the previous loop iteration *)
    eapply exit_oned_loop_inner_block.
     eassumption.
     eassumption.
Qed.




Lemma oned_loop_with_iv_gt_ub_will_not_execute:
  forall (n: int) (ivname: ident) (innerstmt: Cminor.stmt),
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (o: outcome),
  forall (iv_cur: int),
    e ! ivname = Some (Vint iv_cur) ->
    (Int.cmpu Clt iv_cur n) = false ->
    exec_stmt ge f sp e m
              (oned_loop n ivname innerstmt) E0
              e' m' o -> o = Out_exit 0 /\ e = e' /\ m = m'.
Proof.
  intros until iv_cur.
  intros e_at_ivname.
  intros iv_gt_n.
  intros exec.
  assert (eval_expr ge sp e m (Ebinop
                                 (Ocmpu Clt)
                                 (Evar ivname)
                                 (Econst (Ointconst n))) Vfalse) as
      cond_is_false.
  eapply eval_Ebinop.
  eapply eval_Evar.
  eapply e_at_ivname.
  eapply eval_Econst.
  unfold eval_constant.
  auto.
  unfold eval_binop.
  unfold Val.cmpu.
  unfold Val.cmp_bool.
  unfold z_to_val.
  unfold Int.cmp.
  unfold Val.cmpu_bool.
  rewrite iv_gt_n.
  unfold Val.of_optbool.
  reflexivity.

  eapply exit_oned_loop; eassumption.
Qed.

(* Theorem on how a 1-D loop with match that of a SCEV Value *)

Theorem oned_loop_add_rec_matches_addrec_scev_n_eq_0:
  forall  (ivname scevname: ident),
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv),
  forall  (scevz scevinit scevrec: Z),
    scevname <> ivname ->
    scevz = eval_scev (SCEVAddRec scevinit scevrec) 0 ->
    exec_stmt ge f sp e m
              (oned_loop_add_rec 0 ivname scevname scevinit scevrec) E0
              e' m' Out_normal ->
    e' ! scevname =  Some (z_to_val (scevz)).
Proof.
  intros until scevrec.
  intros scevname_neq_ivname.
  intros scevzval.
  unfold eval_scev in scevzval.
  subst.
  intros exec.
  inversion exec. subst.
  rename H1 into ivinit.
  rename H6 into seq.

  assert (t1 = E0 /\ t2 = E0) as teq.
  eapply destruct_trace_app_eq_E0. eassumption.
  destruct teq as [t1eq t2eq].
  subst.
  clear H11.

  assert (e1 ! ivname = Some (Vint (Int.repr 0))) as e1_at_ivname_is_0.
  eapply z_init_sets_z_value.
  eassumption.

  
  inversion seq. subst.
  rename H1 into stmt_scevinit.
  rename H6 into oned_loop_empty.

  
  assert (t1 = E0 /\ t2 = E0) as teq.
  eapply destruct_trace_app_eq_E0. eassumption.
  destruct teq as [t1eq t2eq].
  subst.
  clear H11.

  assert (e2 ! scevname = Some (Vint (Int.repr scevinit))) as e2_at_scevname_is_init.
  eapply z_init_sets_z_value.
  eassumption.

  assert (e2 !ivname = Some (Vint (Int.repr 0))) as e2_at_ivname_is_0.
  inversion stmt_scevinit. subst.
  cut ((PTree.set scevname v e1) ! ivname = e1 ! ivname).
  intros ix_ivname.
  rewrite ix_ivname.
  eassumption.
  eapply PTree.gso.
  auto.

  assert (Out_normal = Out_exit 0).
  eapply exit_oned_loop with (ivname := ivname) (n := 0%nat).
  eapply eval_Ebinop.
  eapply eval_Evar.
  exact e2_at_ivname_is_0.
  assert (eval_expr ge sp e2 m2 (Econst (Ointconst (nat_to_int 0))) (Vint (Int.repr 0))) as eval_zero.
  eapply eval_Econst.
  unfold eval_constant.
  reflexivity.
  eassumption.
  unfold eval_binop.
  unfold Val.cmpu.
  unfold Val.cmpu_bool.
  unfold Int.cmpu.
  unfold Int.ltu.
  assert (0 >= 0) as zero_geq_zero. omega.
  rewrite zlt_false.
  unfold Val.of_optbool.
  reflexivity.
  auto.
  eassumption.

  inversion H.


  subst.
  contradiction.

  subst.
  contradiction.
Qed.
