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
  
  
    

(* Note to self: finish eval_expr_is_function first *)
Lemma exec_stmt_is_function:
  forall (m m' m'': mem) (e e' e'': env) (f: function) (sp: val) (ge: genv) (tr: trace) (o: outcome),
  forall (s: Cminor.stmt),
    exec_stmt ge f sp e m
              s tr e' m' o ->
    exec_stmt ge f sp e  m
              s tr e'' m'' o ->
    e' = e'' /\ m' = m''.
Proof.
  intros until s.
  intros exec_s1.
  intros exec_s2.
  induction s.
  (* skip *)
  - inversion exec_s1. inversion exec_s2. subst. auto.
  (* assign *)
  - inversion exec_s1. inversion exec_s2. subst.

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