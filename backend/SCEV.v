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
  induction o;
  intros until v';
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

  
  
Check (eval_funcall).
(* Check out how "eval_funcall_exec_stmt_steps" does this in CMinor *)
Check (eval_funcall_exec_stmt_ind2).
Lemma eval_stmt_funcall_is_function: forall ge,
  (forall m fd args t m' res,
      eval_funcall ge m fd args t m' res ->
      (forall m'' res',
          eval_funcall ge m fd args t m'' res' -> m' = m'' /\ res = res'
  )) 
  /\(forall f sp e m s t e' m' out,
       exec_stmt ge f sp e m s t e' m' out ->
       (forall e'' m'' out',
           exec_stmt ge f sp e m s t e'' m'' out' ->
           m' = m'' /\ out = out' /\ e' = e'')).
Proof.
  intros ge.
  apply eval_funcall_exec_stmt_ind2; intros.

(* genv -> mem -> fundef -> list val -> trace -> mem -> val -> Prop

Lemma eval_funcall_is_function:
  forall (f: fundef),
  forall (ge: genv) (m mo mo': mem)(params: list val) (tr: trace) (v v': val),
    eval_funcall ge m f params tr mo v ->
    eval_funcall ge m f params tr mo' v' ->
    mo = mo' /\ v = v'.
  intro f.
  induction f;
    intros until v';
    intros eval_mo_v;
    intros eval_mo_v';
    inversion eval_mo_v;
    inversion eval_mo_v';
    subst; try auto.

  (* equate the outputs of Mem.alloc *)
  assert (m1 = m5 /\ sp = sp0).
  cut ((m1, sp) = (m5, sp0)). intro tuple_eq.
  inversion tuple_eq. auto.
  rewrite <- H0.
  rewrite <- H11.
  auto.
  inversion H as [m1_eq_m5 sp_eq_sp0].
  rewrite m1_eq_m5 in *. rewrite sp_eq_sp0 in *.
  clear H. clear m1_eq_m5. clear sp_eq_sp0.


  assert(out = out0) as out_eq_out0.
  assert (v = v').
  eapply outcome_result_value_is_function.
  exact H3.
  exact H14.
*) 

  
    
                                                              
  
  
    

(* Note to self: finish eval_expr_is_function first *)
Lemma exec_stmt_is_function:
  forall (s: Cminor.stmt),
  forall (m m' m'': mem) (e e' e'': env) (f: function) (sp: val) (ge: genv) (tr: trace) (o: outcome),
    exec_stmt ge f sp e m
              s tr e' m' o ->
    exec_stmt ge f sp e  m
              s tr e'' m'' o ->
    e' = e'' /\ m' = m''.
Proof.
  induction s using exec_stmt_ind2; try(intros until o; intros exec_s1; intros exec_s2).

  (* skip *)
  - inversion exec_s1. inversion exec_s2. subst. auto.
  (* assign *)
  - inversion exec_s1. inversion exec_s2. subst.
    assert (v = v0).
    eapply eval_expr_is_function.
    apply H9. apply H20.
    rewrite H.
    auto.
  (* Sstore *)
  -  inversion exec_s1. inversion exec_s2. subst.
     assert (v = v0) as v_eq_v0.
     + eapply eval_expr_is_function; eassumption.

     + assert (vaddr = vaddr0) as vaddr_eq_vaddr0.
     eapply eval_expr_is_function; eassumption.

       
     rewrite v_eq_v0 in *.
     rewrite vaddr_eq_vaddr0 in *.
       
     assert (Some m' = Some m'') as some_m'_eq_some_m''.
     rewrite <- H26. rewrite <- H12.
     auto.
     inversion some_m'_eq_some_m''.
     auto.
  (* Scall *)
  - intros until o0.
    intros exec_s1. intros exec_s2.
    inversion exec_s1. inversion exec_s2. subst.

    assert (vargs = vargs0) as vargs_eq_vargs0.
    eapply eval_exprlist_is_function; eassumption.
    
    rewrite vargs_eq_vargs0 in *. clear vargs_eq_vargs0.
    
    assert(vf = vf0) as vf_eq_vf0.
    eapply eval_expr_is_function; eassumption.

    rewrite vf_eq_vf0 in *. clear vf_eq_vf0.

    
    assert (fd = fd0) as fd_eq_fd0.
    cut (Some fd = Some fd0). intros some_eq. inversion some_eq. auto.
    rewrite <- H9. rewrite <- H27. reflexivity.
    rewrite fd_eq_fd0 in *. clear fd_eq_fd0.

    (* this is part where I ope up eval_funcall *)
     
    

Lemma if_cond_with_failing_branch_will_return_else:
  forall (cond: expr) (sthen selse: Cminor.stmt),
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv) (tr: trace) (o: outcome),
    eval_expr ge sp e m cond Vfalse ->
    exec_stmt ge f sp e m (selse) tr e' m' o ->
    exec_stmt ge f sp e m
              (Cminor.Sifthenelse cond sthen selse) tr e' m' o.
  intros until o.
  intros exprval.
  intros elseval.
  assert(forall mif eif, exec_stmt ge f sp e m (Sifthenelse cond sthen selse) tr eif mif o ->
                    eif = e' /\ mif = m').
  intros.
  inversion H.
  subst.

  inversion exprval.
  subst.
  rename H13 into ite_bool.
  inversion H7.
  subst.
  rewrite H2 in H0.
  inversion H0. subst.
  inversion H12.
  assert (b = false).
  rewrite <- H1.
  unfold negb.
  rewrite Int.eq_true.
  reflexivity.
  rewrite H4 in *.
  split.
  
    


Lemma oned_loop_with_iv_gt_ub_will_not_execute:
  forall (n: nat) (ivname: ident) (innerstmt: Cminor.stmt),
  forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv),
  forall (iv_cur_z: Z),
    e ! ivname = Some (z_to_val iv_cur_z) ->
    Int.lt (z_to_int iv_cur_z) (nat_to_int n) = false ->
    exec_stmt ge f sp e m
              (oned_loop n ivname innerstmt) E0
              e' m' (Out_exit 1) -> e = e' /\ m = m'.
  intros until iv_cur_z.
  intros e_at_ivname_is_iv_cur_z.
  intros iv_cur_z_gt_n.
  intros exec.
  inversion exec.
  subst.
  
  rename H0 into eval_sblock.
  rename H1 into eval_sloop.
  inversion eval_sblock. subst.
  rename H9 into eval_sseq.
  inversion eval_sseq.
  subst.
  rename H1 into exec_if.
  rename H8 into exec_inner.
  inversion exec_if.
  subst.
  rename H14 into exec_if_bool.
  rename H8 into eval_cond.
  inversion eval_cond.
  subst.
  rename H2 into eval_iv.
  rename H5 into eval_n.
  rename H7 into eval_cmp.
  inversion eval_iv.
  subst.
  rewrite e_at_ivname_is_iv_cur_z in H0.
  inversion H0.
  rewrite <- H1 in *.
  clear H1. clear H0.
  inversion eval_cmp.

  inversion eval_n.
  subst.
  rename H1 into eval_constant_n.
  inversion eval_constant_n.
  rename H0 into v2_value.
  subst.
  subst.


  assert (b = false) as b_eq_false.
  inversion eval_cond.
  subst.
  inversion H13.
  subst.
  unfold Val.cmp in H0.
  unfold Val.of_optbool in H0.
  unfold Val.cmp_bool in H0.
  simpl in H0.
  simpl in iv_cur_z_gt_n.
  unfold z_to_int in iv_cur_z_gt_n.
  rewrite iv_cur_z_gt_n in H0.
  inversion H0.
  auto.
  rewrite b_eq_false in *.
  inversion exec_if_bool.
  subst.
  rewrite <- H4 in H12.
  inversion H7.
  subst.
  rename H7 into exec_ite.
  rename H16 into exec_ite_b.
  rename H9 into exec_binop.
  inversion exec_binop.
  subst.
  inversion H2.
  subst.
  rewrite  e_at_ivname_is_iv_cur_z in  H0.
  inversion H0.
  rewrite <- H1 in *.
  clear H0 H1.
  inversion H5.
  subst.
  inversion H0.
  unfold nat_to_int in H1.
  rewrite <- H1 in *.
  clear H1.
  clear H0.
  inversion H7.
  unfold Val.cmp in H0. simpl in H0.
  unfold z_to_int,nat_to_int in iv_cur_z_gt_n.
  rewrite iv_cur_z_gt_n in H0.
  rewrite <- H0 in *.
  inversion H15.
  assert (b = false).
  rewrite <- H3. auto.
  clear H3.
  subst.
  inversion exec_ite_b.
  subst.
  inversion eval_sloop.
  subst.

  



  
                              
    


Lemma 



  

(* Theorem on how a 1-D loop with match that of a SCEV Value *)
Theorem oned_loop_add_rec_matches_addrec_scev:
  forall (n: nat) (ivname: ident) (iv_init_val iv_add_val: Z),
   forall (m m': mem) (e e': env) (f: function) (sp: val) (ge: genv),
    exec_stmt ge f sp e m
              (oned_loop_add_rec n ivname iv_init_val iv_add_val) E0
              e' m' Out_normal ->
    e' ! ivname =  Some (z_to_val (eval_scev (SCEVAddRec iv_init_val iv_add_val) n)).
    
    
    
Hint Transparent cm_loop_0_to_ub.