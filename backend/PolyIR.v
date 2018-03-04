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
Require Import ExtensionalityFacts.
Require Import Equivalence EquivDec.
Require Import Coqlib.


(* Useful facts about functions that are inverses *)
Theorem is_inverse_injective: forall (A B:Set) (f: A -> B) (g: B -> A) (a b: A), is_inverse f g -> f a = f b -> a = b.
Proof.
  intros.
  assert (g (f a) = g (f b)) as gcall.
  rewrite H0. reflexivity.
  unfold is_inverse in H. destruct H.
  cut (a = g (f a)).
  cut (b = g (f b)).
  intros.
  rewrite H2. rewrite H3. auto.
  intuition. intuition.
Qed.

Theorem injective_preimg_neq_implies_img_neq: forall (A B: Set)
                                    (f: A -> B)
                                    (g: B -> A)
                                    (a b: A),
    (forall (b1 b2: B), {b1 = b2} + {b1 <> b2}) ->
    is_inverse f g -> a <> b -> f a <> f b.
Proof.
  intros until b.
  intros dec.
  intros inv.
  intros preimg_neq.
  assert ({f a = f b} + {f a <> f b}) as decide_f.
  eapply dec.

  destruct decide_f as [f_eq | f_neq].
  assert (a = b) as contra.
  eapply is_inverse_injective; eassumption.

  contradiction.

  assumption.
Qed.

Theorem is_inverse_symmetric: forall (A B:Set) (f: A -> B) (g: B -> A), is_inverse f g -> is_inverse g f.
Proof.
  intros.
  unfold is_inverse in *.
  intuition.
Qed.


Theorem is_inverse_cancellation: forall (A: Set) (s s': A -> A) (a: A),
    is_inverse s s' -> ((s (s' a)) = a).
Proof.
  intros.
  unfold is_inverse in H.
  destruct H.
  apply H0.
Qed.


Inductive affineexpr: Type :=
| Eindvar: affineexpr
| Econstoffset: ptrofs -> affineexpr.

Definition STORE_CHUNK_SIZE: memory_chunk := Mint8unsigned.
Inductive stmt: Type :=
| Sstore:  affineexpr -> int -> stmt.


Notation vindvar := nat.
Notation indvar := nat.
Notation upperbound := nat.

(* Definition nat_to_int (n: nat): int := (Int.repr (Z.of_nat n)). *)
Definition nat_to_int64 (n: nat): int64 := (Int64.repr (Z.of_nat n)).
Definition nat_to_ptrofs (n: nat): ptrofs := (Ptrofs.repr (Z.of_nat n)).
Definition nat_to_vlong (n: nat): val := Vlong (nat_to_int64  n).

Lemma nat_to_int64_inj:
  forall (n n': nat),
    Z.of_nat n < Int64.modulus ->
    Z.of_nat n' < Int64.modulus -> 
    nat_to_int64 n = nat_to_int64 n' -> n = n'.
Proof.
  intros until n'.
  intros n_inrange n'_inrange.
  
  intros eq_as_int.
  unfold nat_to_int in eq_as_int.
  apply Int64.repr_of_nat_inj.
  omega.
  omega.
  eassumption.
Qed.

Lemma nat_to_int64_neq:
  forall (n n': nat),
    Z.of_nat n < Int64.modulus ->
    Z.of_nat n' < Int64.modulus ->
    n <> n' ->
    nat_to_int64 n <> nat_to_int64 n'.
  intros until n'.
  intros n_inrange n'_inrange.

  intros neq_as_nat.
  assert ({nat_to_int64 n = nat_to_int64 n'} +
          {nat_to_int64 n <> nat_to_int64 n'}) as nat_to_int_cases.
  apply Int64.eq_dec.
  destruct nat_to_int_cases as [n_eq | n_neq].

  - assert (n = n') as contra.
  apply nat_to_int64_inj; assumption.
  omega.
  -  auto.
Qed.



Lemma nat_to_vlong_inj:
  forall (n n': nat),
    Z.of_nat n < Int64.modulus ->
    Z.of_nat n' < Int64.modulus -> 
    nat_to_vlong n = nat_to_vlong n' -> n = n'.
Proof.
  intros until n'.
  intros untiil n_lt_mod n'_lt_mod.
  unfold nat_to_vlong in n'_lt_mod.

  assert (forall i j, Vlong i = Vlong j -> i = j) as inversion_Vlong.
  intros until j.
  intros eq.
  inversion eq.
  reflexivity.
  
  (* TODO: why do I need this? *)
  assert (nat_to_int64 n = nat_to_int64 n').
  eapply inversion_Vlong.
  assumption.

  apply nat_to_int64_inj; assumption.
Qed.

  
Lemma nat_to_vlong_neq_1:
  forall (n n': nat),
    nat_to_vlong n <> nat_to_vlong n' -> n <> n'.
Proof.
  intros until n'.

  intros nat_to_vlong_neq.

  assert (n = n' \/ n <> n') as ncases.
  omega.
  destruct ncases as [n_eq | n_neq].
  - assert (nat_to_vlong n = nat_to_vlong n') as contra.
    rewrite n_eq. reflexivity.
    contradiction.
  -  auto.
Qed.


Lemma nat_to_vlong_neq_2:
  forall (n n': nat),
    Z.of_nat n < Int64.modulus ->
    Z.of_nat n' < Int64.modulus ->
    n <> n' ->
    nat_to_vlong n <> nat_to_vlong n'.
Proof.
  intros until n'.
  intros n_lt_mod.
  intros n'_lt_mod.

  intros neq.

  assert (nat_to_vlong n = nat_to_vlong n' \/ nat_to_vlong n <> nat_to_vlong n') as
      nat_to_vlong_cases.
  apply val_eq_dec.

  destruct nat_to_vlong_cases as [v_eq | v_neq].
  - assert (n = n') as contra.
    apply nat_to_vlong_inj; assumption.
    omega.
  -  auto.
Qed.

Lemma transfer_nat_add_to_int_add:
  forall (n: nat),
    Z.of_nat n < Int64.max_unsigned ->
    Int64.repr (Z.of_nat (n + 1)%nat) =
    (Int64.add (Int64.repr (Z.of_nat n)) Int64.one).
Proof.
  intros n.
  intros n_lt_unsigned.
  rewrite Int64.add_unsigned.
  unfold Int.one.
  rewrite Int64.unsigned_repr.
  rewrite Nat2Z.inj_add.
  simpl.
  reflexivity.
  split.
  omega.
  omega.

Qed.

Lemma transfer_nat_lt_to_int_lt:
  forall (n1 n2: nat),
    (n1 < n2)%nat ->
    Z.of_nat n1 <= Int64.max_unsigned ->
    Z.of_nat n2 <= Int64.max_unsigned ->
    Int64.ltu (nat_to_int64 n1) (nat_to_int64 n2) = true.
Proof.
  intros until n2.
  intros n1_lt_n2.

  intros n1_lt_max_unsigned.
  intros n2_lt_max_unsigned.
  
  unfold nat_to_int64.
  unfold Int64.ltu.
  rewrite Int64.unsigned_repr.
  rewrite Int64.unsigned_repr.
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
    Z.of_nat n1 <= Int64.max_unsigned ->
    Z.of_nat n2 <= Int64.max_unsigned ->
    Int64.ltu (nat_to_int64 n1) (nat_to_int64 n2) = false.
Proof.
  intros until n2.
  intros n1_lt_n2.

  intros n1_lt_max_unsigned.
  intros n2_lt_max_unsigned.
  
  unfold nat_to_int64.
  unfold Int64.ltu.
  rewrite Int64.unsigned_repr.
  rewrite Int64.unsigned_repr.
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



Record inverseTillUb (ub: upperbound)
           (a: vindvar -> vindvar)
           (ainv: vindvar -> vindvar) :=
  mkInverseTillUb {
      inverse_forward: forall (n: vindvar), (n < ub)%nat -> a  (ainv n) = n;
      inverse_backward: forall (n: vindvar), (n < ub)%nat -> ainv (a n) = n;
      inrange_forward: forall (n: vindvar), (n < ub)%nat -> (a n < ub)%nat;
      inrange_backward: forall (n: vindvar), (n < ub)%nat ->  (ainv n < ub)%nat;
    }.

Lemma inverseTillUb_symmetry:
  forall (ub: upperbound)
    (a ainv: vindvar -> vindvar),
    inverseTillUb ub a ainv <-> inverseTillUb ub ainv a.
Proof.
  assert (
      forall (ub: upperbound)
        (a ainv: vindvar -> vindvar),
        inverseTillUb ub a ainv -> inverseTillUb ub ainv a) as
      proof_onedir.
  intros ub a ainv.
  intros isinv.
  destruct isinv.
  apply mkInverseTillUb; auto.
  
  split; apply proof_onedir.
Qed.

Lemma inverseTillUb_inj_1:
  forall (ub: upperbound) (a ainv: vindvar -> vindvar)
    (iv iv': vindvar),
    inverseTillUb ub a ainv ->
    (iv < ub)%nat ->
    (iv' < ub)%nat ->
    a iv = a iv' -> iv = iv'.
Proof.
  intros until iv'.
  intros isinv ivinrange iv'inrange aeq.
  inversion isinv.

  assert (ainv (a iv) = ainv (a iv')) as ainveq.
  rewrite aeq.
  reflexivity.

  assert (ainv (a iv) = iv /\ ainv (a iv') = iv') as simpl_inv.
  split; apply isinv; eassumption.

  destruct simpl_inv as [simpl_iv simpl_iv'].
  rewrite <- simpl_iv.
  rewrite <- simpl_iv'.
  assumption.
Qed.


Lemma inverseTillUb_inj_2:
  forall (ub: upperbound) (a ainv: vindvar -> vindvar)
    (iv iv': vindvar),
    inverseTillUb ub a ainv ->
    (iv < ub)%nat ->
    (iv' < ub)%nat ->
    iv <> iv' -> a iv <> a iv'.
Proof.
  intros until iv'.
  intros isinv ivinrange iv'inrange aneq.
  inversion isinv.

  assert (a iv = a iv' \/ a iv <> a iv') as a_iv_cases.
  omega.

  destruct a_iv_cases as [a_iv_eq | a_iv_neq].
  - assert (iv = iv').
    eapply inverseTillUb_inj_1;
      eassumption.
    omega.
  - auto.
Qed.

(* For any type A on which equality is decidable, it lets us convert
inequality in the codomain to inequality in the domain.
TODO: what is this called? *)
Lemma eq_decidable_implies_fn_pointwise_eq_decidable:
  forall (A B: Set) (f: A -> B) (a1 a2: A)
    (adec: forall (a a': A), a = a' \/ a <> a'),
    f a1 <> f a2 -> a1 <> a2.
Proof.
  intros.
  assert (a1 = a2 \/ a1 <> a2).
  auto.
  destruct H0.
  apply (f_equal f) in H0.
  contradiction.
  assumption.
Qed.
  
    
    
Record loop : Type :=
  mkLoop {
      loopub: upperbound;
      loopub_in_range_witness: Z.of_nat loopub < Int64.max_unsigned;
      loopivname: ident;
      looparrname: ident;
      loopstmt: stmt;
      loopschedule: vindvar -> vindvar;
      loopscheduleinv: vindvar -> vindvar;
      loopschedulewitness: inverseTillUb loopub loopschedule loopscheduleinv;
    }.


Definition id_vindvar : vindvar -> vindvar := id.

Lemma id_vindvar_self_inverse: forall (n: nat),
    inverseTillUb n id_vindvar id_vindvar.
Proof.
  intros n.
  apply mkInverseTillUb;
  intros;
  unfold id_vindvar;
  unfold id;
  omega.
Qed.

Definition loop_id_schedule (loopub: upperbound)
           (loopub_in_range_witness: Z.of_nat loopub < Int64.max_unsigned)
           (loopivname: ident)
           (looparrname: ident)
           (loopstmt: stmt) :=
  mkLoop loopub
         loopub_in_range_witness
         loopivname
         looparrname
         loopstmt
         id
         id
         (id_vindvar_self_inverse loopub).


Definition n_minus_x (n x: nat) := (n - x - 1)%nat.

Lemma n_minus_x_self_inverse: forall n,
    inverseTillUb n (n_minus_x n) (n_minus_x n).
Proof.
  intros n.
  apply mkInverseTillUb;
    intros;
    (* really weird, omega number crunches for a *while* here *)
    unfold n_minus_x; omega.

Qed.



Definition loop_reversed_schedule (loopub: upperbound)
           (loopub_in_range_witness: Z.of_nat loopub < Int64.max_unsigned)
           (loopivname: ident)
           (looparrname: ident)
           (loopstmt: stmt) :=
  mkLoop loopub
         loopub_in_range_witness
         loopivname
         looparrname
         loopstmt
         (n_minus_x loopub)
         (n_minus_x loopub)
         (n_minus_x_self_inverse loopub).

Record loopenv : Type := mkLenv { viv: vindvar }.
Definition loopenv_bump_vindvar (le: loopenv) : loopenv :=
  mkLenv ((viv le) + 1)%nat.

Definition loopenv_reduce_vindvar (le: loopenv) : loopenv :=
  mkLenv (viv le - 1)%nat.

Lemma loopenv_bump_reduce_vindvar: forall (le: loopenv),
    (viv le > 0)%nat ->
    le = loopenv_bump_vindvar (loopenv_reduce_vindvar le).
Proof.
  intros.
  destruct le.
  unfold loopenv_bump_vindvar.
  unfold loopenv_reduce_vindvar.
  simpl in *.
  assert (viv0 = viv0 - 1 + 1)%nat.
  omega.
  auto.
Qed.

Section EVAL_AFFINEEXPR.
  Variable ge: genv.
  Variable le: loopenv.
  Variable l: loop.

  Inductive eval_affineexpr: affineexpr -> val -> Prop :=
  | eval_Eindvar: eval_affineexpr
                    Eindvar
                    (Genv.symbol_address ge
                                         (looparrname l)
                                         (nat_to_ptrofs (loopschedule l (viv le))))
  | eval_Econstoffset: forall (ofs: ptrofs),
      eval_affineexpr (Econstoffset ofs)
                      (Genv.symbol_address ge
                                           (looparrname l)
                                           ofs)
  .
End EVAL_AFFINEEXPR.

Section EXEC_STMT.
  Inductive exec_stmt: genv -> loopenv -> loop -> mem -> stmt -> mem -> Prop := 
  | exec_Sstore: forall (ge: genv)
                   (le: loopenv)
                   (l: loop)
                   (m m': mem)
                   (eaddr: affineexpr) (i: int) (vaddr: val),
      (viv le < loopub l)%nat ->
      eval_affineexpr ge le l eaddr vaddr  ->
      Mem.storev STORE_CHUNK_SIZE
                 m
                 vaddr
                 (Vint i) = Some m' ->
      exec_stmt ge le l m (Sstore eaddr i) m'.

  Lemma exec_stmt_is_useless:
    forall ge le l m s m',
      exec_stmt ge le l m s m' -> m = m'.
  Proof.
    intros until m'.
    intros execs.
    inversion execs. subst.

    - rename H0 into eval_expr.
      rename H1 into memstore.

      unfold Mem.storev in memstore.
  Abort.
      
End EXEC_STMT.

Section EXEC_LOOP.

  Inductive exec_loop: genv -> loopenv -> mem -> loop -> mem -> loopenv -> Prop :=
  | eval_loop_stop: forall ge le m l,
      (viv le >= loopub l)%nat ->
      exec_loop ge le m l m le
  | eval_loop_loop: forall ge le le' m m' m'' l,
      (viv le < loopub l)%nat ->
      (viv le < viv le')%nat -> 
      exec_stmt ge le l m (loopstmt l) m' ->
      exec_loop ge (loopenv_bump_vindvar le) m' l m'' le' ->
      exec_loop ge le m l m'' le'.
End EXEC_LOOP.

Lemma exec_loop_viv_nondecreasing:
  forall (ge: genv) (le le': loopenv) (m m': mem) (l: loop),
    exec_loop ge le m l m' le' ->
    (viv le' >= viv le)%nat.
Proof.
  intros until l.
  intros execl.
  induction execl.
  - auto.
  - unfold loopenv_bump_vindvar in *. simpl in *. omega.
Qed.

Lemma exec_loop_env_equal_implies_memory_equal:
  forall (ge: genv) (le le': loopenv) (m m': mem) (l: loop),
    exec_loop ge le m l m' le' ->
    le = le' -> m = m'.
Proof.
  intros.
  subst.
  inversion H; subst; try auto.
  omega.
Qed.
  

Theorem eval_affineexpr_is_function:
  forall (ge: genv) (le: loopenv) (l: loop) (ae: affineexpr) (a a': val),
    eval_affineexpr ge le l ae a ->
    eval_affineexpr ge le l ae a' ->
    a = a'.
Proof.
  intros until a'.
  intros eval_a.
  intros eval_a'.
  induction ae; inversion eval_a; inversion eval_a'; subst; try auto.
Qed.


Theorem exec_stmt_is_function:
  forall (ge: genv)
    (le: loopenv) (l: loop) (m m' m'': mem) (s: stmt),
    exec_stmt ge le l m s m' ->
    exec_stmt ge le l m s m'' ->
    m' = m''.
Proof.
  intros until s.
  intros eval_m.
  intros eval_m'.
  induction s; inversion eval_m;inversion eval_m'; subst; try auto.
  assert(vaddr0 = vaddr) as veq.
  eapply eval_affineexpr_is_function; eassumption.
  subst.

  
  rename H8 into store_m'.
  rename H18 into store_m''.
  assert (Some m' = Some m'') as meq.

  
  rewrite <- store_m'. rewrite <- store_m''.

  reflexivity.
  inversion meq. subst.
  auto.
Qed.

Theorem exec_loop_is_function:
  forall (ge: genv) (le' le'': loopenv) (viv: vindvar) (l: loop) (m m' m'': mem),
    exec_loop ge (mkLenv viv) m l m' le' ->
    exec_loop ge (mkLenv viv) m l m'' le'' ->
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
    e ! (loopivname  l) = Some (nat_to_vlong (loopschedule l (viv le))).

Definition env_incr_iv_wrt_loop (le: loopenv) (l: loop) (e: env) : env :=
  PTree.set (loopivname l)
            (nat_to_vlong(loopschedule l (viv le + 1)%nat))
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

End MATCHENV.
  



Section MATCHAFFINEEXPR.
  Variable le: loopenv.
  Variable l: loop.


  (*int32['A' +l 4LL *l longofint ('i' + 10)] =  *)


  Inductive match_affineexpr: expr -> affineexpr -> Prop :=
  | match_Evar: match_affineexpr (Ebinop Oaddl
                                         (Econst
                                            (Oaddrsymbol (looparrname l)
                                                         (nat_to_ptrofs 0)))     
                                              (Evar (loopivname l)))
                                    Eindvar
                                    
  | match_Econstoffset: forall i,match_affineexpr
                              (Econst
                                 (Oaddrsymbol (looparrname l)
                                              i))     
                             (Econstoffset i). 
End MATCHAFFINEEXPR.

Theorem match_expr_have_same_value:
  forall (l:loop) (le:loopenv) (a:expr) (sp: val) (m: mem) (ae:affineexpr) (e:env) (ge: genv) (v v':val),
    Archi.ptr64 = true ->
    (viv le < loopub l)%nat ->
    match_affineexpr l a ae ->
    match_env l e le ->
    eval_expr ge sp e m a v ->
    eval_affineexpr ge le l ae v' ->
    v = v'.
Proof.
  intros until v'.
  intros archi_ptr64_true.
  intros viv_in_range.
  intros match_exprs.
  intros match_envs.
  intros eval_expr.
  intros eval_affineexpr.
  
  induction match_exprs;
    inversion eval_expr;
    inversion eval_affineexpr;
    inversion match_envs;
    subst.

  - rename H2 into eval_baseptr.
    rename H4 into eval_loopiv.
    rename H5 into eval_baseptr_plus_loopiv.
    rename H8 into loopiv_eq_sched.
    rename v1 into vbaseptr.
    rename v2 into loopiv.

    assert (Genv.symbol_address ge (looparrname l) (nat_to_ptrofs 0) = vbaseptr) as
        vbseptr_val.
    inversion eval_baseptr; subst.
    inversion H0.
    auto.
    subst.

    inversion eval_baseptr_plus_loopiv.
    subst.

    inversion eval_loopiv. subst.



    assert (Some loopiv = Some (nat_to_vlong (loopschedule l (viv le)))) as loopivnameq.
    rename H0 into e_at_loopivname.
    rewrite <- loopiv_eq_sched.
    rewrite <- e_at_loopivname.
    reflexivity.

    inversion loopivnameq.
    subst.

    unfold Genv.symbol_address.

    remember (Genv.find_symbol ge (looparrname l)) as maybe_arrbase.
    destruct (maybe_arrbase).
    unfold Val.addl.
    simpl.
    destruct Archi.ptr64.
  + unfold Ptrofs.add.
    unfold nat_to_ptrofs.
    simpl.
    rewrite Ptrofs.unsigned_repr.
    simpl.
    unfold nat_to_int64.
    rewrite Ptrofs.repr_unsigned.
    unfold Ptrofs.of_int64.
    rewrite Int64.unsigned_repr.
    reflexivity.
    split.
    omega.

    assert (Z.of_nat (loopschedule l (viv le)) < Z.of_nat (loopub l)) as iv_in_range.
    apply Znat.inj_lt.
    eapply inrange_forward.
    exact (loopschedulewitness l).
    assumption.
    assert (Z.of_nat (loopub l) < Int64.max_unsigned) as loopub_in_range.
    eapply (loopub_in_range_witness l).
    omega.
    split.
    omega.
    unfold Ptrofs.max_unsigned.
    rewrite Ptrofs.modulus_eq64.
    unfold Int64.modulus.
    simpl.
    omega.
    eassumption.

  +  inversion archi_ptr64_true.

  + unfold Val.addl.
    reflexivity.
  - inversion eval_expr; subst. inversion H1. subst.
    reflexivity.
Qed.

Theorem match_expr_have_same_value':
  forall (l:loop)
    (le:loopenv)
    (a:expr)
    (sp: val)
    (m: mem)
    (ae:affineexpr)
    (e:env)
    (ge: genv)
    (v:val),
    Archi.ptr64 = true ->
    (viv le < loopub l)%nat ->
    match_affineexpr l a ae ->
    match_env l e le ->
    eval_affineexpr ge le l ae v ->
    eval_expr ge sp e m a v.
Proof.
  intros until v.
  intros arch64.
  intros viv_in_range.
  intros match_exprs.
  intros match_envs.
  intros eval_affineexpr.
  
  induction match_exprs;
    inversion eval_affineexpr;
    inversion match_envs;
    subst.
  rename H1 into e_at_loopivname.
  - eapply eval_Ebinop.
    eapply eval_Econst.
    unfold eval_constant.
    auto.
    eapply eval_Evar.
    apply e_at_loopivname.
    unfold Genv.symbol_address.

    remember (Genv.find_symbol ge (looparrname l))
      as genv_at_arrname.
    destruct genv_at_arrname.

    + unfold eval_binop.
      unfold Val.addl.
      unfold nat_to_vlong.
      rewrite arch64.
      unfold nat_to_ptrofs.
      rewrite Ptrofs.add_unsigned.
      rewrite Ptrofs.unsigned_repr.
      simpl.
      rewrite Ptrofs.repr_unsigned.
      unfold nat_to_int64.
      unfold Ptrofs.of_int64.

      remember (Z.of_nat (loopschedule l (viv le))) as innerval.

      rewrite Int64.unsigned_repr.
      auto.

      (* innerval is in Int64.max_unsigned *)
      split.
      omega.

      assert (Z.of_nat (loopub l) < Int64.max_unsigned) as loopubinrange.
      eapply loopub_in_range_witness.
      assert (Z.of_nat (loopschedule l (viv le)) < Z.of_nat (loopub l)) as loopschedinrange.
      apply Znat.inj_lt.
      eapply inrange_forward.
      exact (loopschedulewitness l).
      assumption.
      omega.

      split; try omega.
      Check (Ptrofs.max_unsigned).
      cut (Ptrofs.max_unsigned > 0).
      intros.
      unfold Z.of_nat.
      omega.
      eapply Ptrofs.ptrofs_max_unsigned_gt_0.
      assumption.

    + unfold eval_binop.
      unfold Val.addl.
      reflexivity.

  - apply eval_Econst.
    unfold eval_constant.
    reflexivity.
Qed.
   






Section MATCHSTMT.
  Variable le: loopenv.
  Variable l: loop.
  Inductive match_stmt: Cminor.stmt -> stmt -> Prop :=
  | match_Sstore: forall (addre: expr) (i: int)
                    (addrae: affineexpr),
      match_affineexpr l addre addrae ->
      match_stmt (Cminor.Sstore
                    STORE_CHUNK_SIZE
                    addre
                    (Econst (Ointconst i)))
                 (Sstore addrae i).
End MATCHSTMT.

Theorem match_stmt_has_same_effect:
  forall (le: loopenv) (l: loop)(f: function) (sp: val) (cms: Cminor.stmt) (s: stmt) (m m' m'': mem) (ge: genv) (e e': env) (t: trace) (o: outcome),
    Archi.ptr64 = true ->
    match_env l e le ->
    Cminor.exec_stmt ge f sp e m cms t e' m' o ->
    exec_stmt ge le l m s m'' ->
    match_stmt l  cms s ->
    m' = m'' /\ e = e' /\ t = E0 /\ o = Out_normal.
Proof.
  intros until o.
  intros arch64.
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
  rename H22 into eval_v.
  inversion eval_v.
  subst.
  inversion H1. subst.
  reflexivity.
  subst.
  
  assert (Some m' = Some m'') as meq.
  rename H23 into store_into_m'.
  rename H9 into store_into_m''.
  
  rewrite <- store_into_m'.
  rewrite <- store_into_m''.
  
  auto.
  inversion meq. subst.
  auto.
Qed.



Theorem match_stmt_has_same_effect':
  forall (le: loopenv) (l: loop)(f: function) (sp: val) (cms: Cminor.stmt) (s: stmt) (m m':mem) (ge: genv) (e: env),
    Archi.ptr64 = true ->
    match_env l e le ->
    exec_stmt ge le l m s m' ->
    match_stmt l  cms s ->
    Cminor.exec_stmt ge f sp e m cms E0 e m' Out_normal.
Proof.
  intros until e.
  intros arch64.
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
    eapply match_expr_have_same_value'; try eassumption.

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

Lemma eval_iv_lt_ub_false:
  forall (ge: genv) (sp: val) (m: mem),
  forall (e: env) (ivname: ident) (viv: nat) (ub: upperbound),
    Z.of_nat viv <= Int64.max_unsigned ->
    Z.of_nat ub <= Int64.max_unsigned ->
    (viv >= ub)%nat ->
    e ! ivname = Some (nat_to_vlong viv) ->
    eval_expr ge sp e m 
              (Ebinop
                 (Ocmplu Clt)
                 (Evar ivname)
                 (Econst (Olongconst (nat_to_int64 ub)))) Vfalse.
Proof.
  intros until ub.
  intros viv_le_max_unsigned.
  intros ub_le_max_unsigned.
  intros viv_lt_ub.
  intros e_at_ivname_is_viv.
  eapply eval_Ebinop.
  eapply eval_Evar.
  eassumption.
  eapply eval_Econst.
  unfold eval_constant.
  auto.

  unfold eval_binop.
  unfold Val.cmplu.
  unfold Val.cmplu_bool.
  unfold nat_to_vlong.
  unfold Int.cmpu.
  simpl.

  assert (Int64.ltu (nat_to_int64 viv0) (nat_to_int64 ub) = false).
  rewrite transfer_nat_ge_to_int_ltu; try assumption; try auto.
  rewrite H.
  reflexivity.
Qed.

Lemma eval_iv_lt_ub_true:
  forall (ge: genv) (sp: val) (m: mem),
  forall (e: env) (ivname: ident) (viv: nat) (ub: upperbound),
    Z.of_nat ub < Int64.max_unsigned ->
    (viv < ub)%nat ->
    e ! ivname = Some (nat_to_vlong viv) ->
    eval_expr ge sp e m 
              (Ebinop
                 (Ocmplu Clt)
                 (Evar ivname)
                 (Econst (Olongconst (nat_to_int64 ub)))) Vtrue.
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
  unfold Val.cmplu.
  unfold Val.cmplu_bool.
  unfold nat_to_vlong.
  unfold Int64.cmpu.

  assert (Int64.ltu (nat_to_int64 viv0)
                    (nat_to_int64 ub) = true) as int_viv_ltu_ub.
  eapply  transfer_nat_lt_to_int_lt; try assumption; try omega.
  rewrite int_viv_ltu_ub.
  reflexivity.
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



Theorem exec_loop_when_iv_gt_ub_has_no_effect:
  forall (ub: nat) (iv: nat) (ge: genv),
  forall (le le': loopenv) (l: loop) (m m': mem),
    loopub l = ub ->
    viv le = iv ->
    (iv >= ub)%nat -> 
    exec_loop ge le  m l  m' le' ->
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
  forall ge le m l mloop le',
    exec_loop ge le m l  mloop le' ->
    forall (lub: nat)
      (iv: vindvar)
      (ivname arrname: ident)
      (lsched lschedinv: vindvar -> vindvar)
      (lub_in_range: Z.of_nat lub < Int64.max_unsigned)
      (lub_in_range': Z.of_nat lub + 1 < Int64.max_unsigned)
      (viv_in_range: Z.of_nat iv < Int64.max_unsigned)
      (loopstmt: stmt)
      (lschedwitness: inverseTillUb lub lsched lschedinv),
    forall (f: function)
      (sp: val)
      (cms: Cminor.stmt)
      (mblock: mem)
      (ge: genv)
      (e eblock: env),
    le = mkLenv iv ->
    l = mkLoop lub lub_in_range ivname arrname loopstmt lsched lschedinv lschedwitness ->
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
    rename H2 into match_cm_inner_stmt.
    rename H4 into exec_cms_inner_block.
    rename H5 into exec_cms_loop.
    rename H10 into t1t2val.

    assert (t1 = E0 /\ t2 = E0) as t1_t2_e0.
    apply destruct_trace_app_eq_E0.
    assumption.
    destruct t1_t2_e0.
    subst.
    clear t1t2val.

    
    intros lval leval.

    assert (eval_expr ge sp e m 
                      (Ebinop (Ocmpu Clt)
                              (Evar (loopivname l))
                              (Econst (Ointconst (nat_to_int (loopub l)))))
                      Vtrue) as iv_lt_ub_true.
    eapply eval_iv_lt_ub_true.
    rewrite lval. simpl.
    eassumption.
    eassumption.
    inversion matchenv. rewrite H0.
    rewrite loopsched.
    unfold id.
    reflexivity.

    
    
    eapply IHexecl with (iv := (iv+ 1)%nat).
    exact lub_in_range'.

    assert (Z.of_nat iv < Z.of_nat lub) as iv_lt_ub_over_int.
    rewrite <- Z.compare_lt_iff.
    rewrite Nat2Z.inj_compare.
    rewrite Nat.compare_lt_iff.
    rewrite lval, leval in viv_inbounds.
    simpl in viv_inbounds.
    exact viv_inbounds.

    assert (Z.of_nat iv + 1 < Z.of_nat lub + 1) as
        iv_plus_1_lt_ub_plus_1_over_int.
    omega.

    eapply Z.lt_trans.
    rewrite Nat2Z.inj_add.
    exact iv_plus_1_lt_ub_plus_1_over_int.
    eassumption.

    unfold loopenv_bump_vindvar.
    rewrite leval. simpl. reflexivity.
    exact lval.
    eapply match_env_incr_iv_wrt_loop'. eassumption.

    (* this should be matched with exec_cms_loop *)
    assert (m1 = m') as meq.
    eapply continue_sblock_incr_by_1_sseq_sif.
    eapply iv_lt_ub_true.
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
    eapply iv_lt_ub_true.
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
    unfold nat_to_vlong.
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




    + rename H9 into out_neq_normal.
      contradiction.
Qed.

(* =================================== *)
(* Using proof sketch to show that loop reversal works *)




(* show that indvar across loop iterations take distinct values *)
Lemma indvar_distinct_per_iteration:
  forall (l: loop) (le le':loopenv) ,
    le <> le' ->
    (viv le < loopub l)%nat ->
    (viv le' < loopub l)%nat ->
    loopschedule l (viv le) <> loopschedule l (viv le').
Proof.
  intros until le'.
  intros le_neq_le'.
  intros viv_inrange viv'_inrange.
  assert (viv le <> viv le') as viv_neq.
  destruct le.
  destruct le'.
  simpl.
  auto.
  eapply inverseTillUb_inj_2.
  apply (loopschedulewitness l); eassumption.
  eassumption.
  eassumption.
  auto.
Qed.

Lemma indvar_in_range_1:
  forall (l: loop) (le: loopenv),
    (viv le < loopub l)%nat ->
    (loopschedule l (viv le) < loopub l)%nat.
Proof.
  intros until le.
  intros viv_in_range.
  assert (inverseTillUb (loopub l) (loopschedule l) (loopscheduleinv l))
         as loop_inverse_till_ub.
  apply (loopschedulewitness l).

  destruct loop_inverse_till_ub.
  apply inrange_forward0.
  assumption.
Qed.


Lemma indvar_in_range_2:
  forall (l: loop) (le: loopenv),
    (viv le < loopub l)%nat ->
    (loopscheduleinv l (viv le) < loopub l)%nat.
Proof.
  intros until le.
  intros viv_in_range.
  assert (inverseTillUb (loopub l) (loopschedule l) (loopscheduleinv l))
         as loop_inverse_till_ub.
  apply (loopschedulewitness l).

  destruct loop_inverse_till_ub.
  apply inrange_backward0.
  assumption.
Qed.
  


(* An expression ae takes a value v in loop l,
if there exists a value for the virtual loop indvar such that
if executed, the loop will take that value *)
Definition affineexpr_takes_value_in_loop
           (l: loop)
           (ae: affineexpr)
           (v: val) : Prop :=
  exists (vivval: nat), (0 <= vivval < (loopub l))%nat /\
                 eval_affineexpr (mkLenv vivval) l ae v.



Definition affineexpr_does_not_take_value_in_loop
           (l: loop)
           (ae: affineexpr)
           (val_notake: val) : Prop :=
  forall (vivval: nat) (v: val), (0 <= vivval < (loopub l))%nat /\
                          eval_affineexpr (mkLenv vivval) l ae v ->
                          v <> val_notake.
  

(* Show constructive proof equivalence between the forall form and the exists form
of loop induction variable not taking a value *)
Lemma not_affineexpr_takes_value_equivalence:
  forall (l: loop)
    (ae: affineexpr)
    (v: val),
    ~affineexpr_takes_value_in_loop l ae v <->  affineexpr_does_not_take_value_in_loop l ae v.
Proof.
  intros until v.
  split.

  (* -> *)
  - unfold affineexpr_takes_value_in_loop.
  unfold affineexpr_does_not_take_value_in_loop.
  intros not_takes_value_in_loop.

  intros.
  unfold not in not_takes_value_in_loop.
  assert (v0 = v \/ v0 <> v) as v0_cases.
  apply val_eq_dec.

  destruct v0_cases as [v0_eq | v0_neq].
  + subst.
  cut (False).
  contradiction.
  eapply not_takes_value_in_loop.
  exists vivval.
  auto.

  + eassumption.

    (* <- *)

  - unfold affineexpr_takes_value_in_loop.
    unfold affineexpr_does_not_take_value_in_loop.
    unfold not.
    intros all_v exists_v.
    
    destruct exists_v as [viv viv_conditions].
    destruct viv_conditions as [viv_inrange eval_viv_is_v].
    eapply all_v.
    split.
    exact viv_inrange.
    exact eval_viv_is_v.
    reflexivity.
Qed.

                        
Definition stmt_does_not_write_to_ix_in_loop
           (l: loop)
           (s: stmt)
           (val_notake: val) : Prop :=
  match s with
  | Sstore ae _ => affineexpr_does_not_take_value_in_loop l ae val_notake
  end.

(* A statement writes to an index in a loop if
it is a store statement, and the index expression takes
on the value in the loop
 *) 
Definition stmt_writes_ix_in_loop
           (l: loop)
           (s: stmt)
           (v: val) : Prop :=
  match s with
  | Sstore ae _ => affineexpr_takes_value_in_loop l ae v
  end.

Lemma not_stmt_writes_ix_in_loop_equivalence:
  forall (l: loop) (s: stmt) (v: val),
    ~ (stmt_writes_ix_in_loop l s v) <-> stmt_does_not_write_to_ix_in_loop l s v.
Proof.
  intros.
  unfold not.
  unfold stmt_writes_ix_in_loop.
  unfold stmt_does_not_write_to_ix_in_loop.

  destruct s.
  -  eapply not_affineexpr_takes_value_equivalence.
Qed.



(* The implications from two Vptrs being unequal *)
Lemma vptr_neq_implications:
  forall (b b' : block) (i i': ptrofs),
    Vptr b i <> Vptr b' i' ->
    (b <> b' \/ i <> i').
Proof.
  intros until i'.
  intros neq.

  assert ({b = b'} + {b <> b'}) as bcases.
  eapply Pos.eq_dec.

  assert ({i = i'} + {i <> i'}) as icases.
  eapply Ptrofs.eq_dec.

  destruct bcases as [beq | bneq];
    destruct icases as [ieq | ineq]; try auto.

  - assert (Vptr b i = Vptr b' i') as contra.
    subst.
    reflexivity.
    contradiction.
Qed.

(* WIP: currently working on this lemma *)
Lemma loadv_storev_other:
  forall (m m': mem) (writeaddr readaddr writeval: val),
    Mem.storev STORE_CHUNK_SIZE m writeaddr writeval = Some m' ->
    writeaddr <> readaddr ->
    Mem.loadv STORE_CHUNK_SIZE m' readaddr = Mem.loadv STORE_CHUNK_SIZE m readaddr.
Proof.
  intros until writeval.
  intros write.
  intros noalias.

  unfold Mem.loadv in *; destruct readaddr; try auto.
  unfold Mem.storev in *.

  destruct writeaddr; try (inversion write).

  eapply Mem.load_store_other.
  eassumption.

  assert (b <> b0 \/ i <> i0) as b_i_cases.
  apply vptr_neq_implications.
  auto.

  unfold STORE_CHUNK_SIZE.
  unfold size_chunk.
  
  destruct b_i_cases as [bneq | ineq].
  auto.
  right.
  assert (Ptrofs.unsigned i < Ptrofs.unsigned i0 \/
          Ptrofs.unsigned i > Ptrofs.unsigned i0 \/
          Ptrofs.unsigned i = Ptrofs.unsigned i0)as pi_cases.
  omega.
  destruct pi_cases as [pl | [pg | peq]];
    try omega.
  assert (i = i0).
  apply Ptrofs.unsigned_eq_to_int_eq.
  assumption.
  contradiction.
Qed.

  

Lemma loadv_storev_same:
  forall (m m': mem) (chunk: memory_chunk) (writeaddr readaddr writeval readval_new: val),
    Mem.storev STORE_CHUNK_SIZE m writeaddr writeval = Some m' ->
    Mem.loadv STORE_CHUNK_SIZE m' readaddr = Some readval_new ->
    writeaddr = readaddr ->
    readval_new = (Val.load_result STORE_CHUNK_SIZE writeval).
Proof.
  intros until readval_new. intros write.
  intros read.
  intros alias.

  unfold Mem.loadv in *.
  unfold Mem.storev in *.

  destruct readaddr; try(inversion read).
  destruct writeaddr; try (inversion write).

  (* Good, now we have load, store, and not loadv, storev. We can now start using
     Memory machinery *)
  assert (Mem.load STORE_CHUNK_SIZE m' b (Ptrofs.unsigned i) = Some (Val.load_result STORE_CHUNK_SIZE writeval)) as load_eq_store.
  inversion alias. subst.
  eapply Mem.load_store_same.
  eassumption.

  rewrite read in load_eq_store.

  assert (forall {A: Type} (x y: A), Some x = Some y -> x = y) as some_inversion.
  intros. inversion H. auto.

  eapply some_inversion.
  assumption.
Qed.

  

(* After the loop is run, when we access the final state of
memory, if the index of access memix has *not* been written to
by the loop, then the memory remains the same *)
Lemma mem_unchanged_if_stmt_does_not_write_to_ix_in_loop:
  forall (l: loop) (le le': loopenv) (m m': mem)
    (readix: val),
    exec_loop le m l m' le' ->
    (stmt_does_not_write_to_ix_in_loop l (loopstmt l) readix) ->
    Mem.loadv STORE_CHUNK_SIZE m readix = Mem.loadv STORE_CHUNK_SIZE m' readix.
Proof.
  intros until readix.
  intros execl.
  intros nowrite.
  induction execl.
  -  reflexivity.
  -
    rename H into viv_inrange.
    rename H1 into execstmt.
    destruct (loopstmt l) as [wchunk writeae writeix].
    specialize (IHexecl nowrite).
    assert (Mem.loadv STORE_CHUNK_SIZE m' readix = Mem.loadv STORE_CHUNK_SIZE m readix ).

    inversion execstmt. subst.
    rename ofs into writeaddr.
    rename H6 into evalwriteexpr.
    rename H8 into m'_as_store_m.

    eapply loadv_storev_other.
    eassumption.
    

    assert (writeaddr <> readix) as write_ix_neq_readix.
    unfold stmt_does_not_write_to_ix_in_loop in nowrite.
    unfold affineexpr_does_not_take_value_in_loop in nowrite.
    eapply nowrite  with (vivval := (viv le)).
    split.
    omega.

    assert ({| viv := viv le|} = le) as viv_le_eq.
    destruct le. simpl. reflexivity.
    rewrite viv_le_eq.
    eassumption.
    unfold Mem.loadv.

    auto.
    rewrite <- H.
    rewrite IHexecl.
    auto.
Qed.
    
    

(* Wow, I actually proved the useful induction principle that lets us
peel of a loop iteration from the beginning of the loop
*)

Definition injective_affineexpr_b (ae: affineexpr) : bool :=
  match ae with
  | Eindvar => true
  | Econstoffset _ => false
  end.

Definition injective_stmt_b (s: stmt) : bool :=
  match s with
  | Sstore ae _ => injective_affineexpr_b ae
  end.

Lemma injective_affineexpr_1:
  forall (ae: affineexpr) (l: loop) (le1 le2: loopenv)
    (v1 v2: val),
    injective_affineexpr_b ae = true ->
    le1 <> le2 ->
    (viv le1 < loopub l)%nat ->
    (viv le2 < loopub l)%nat ->
    eval_affineexpr le1 l ae v1 ->
    eval_affineexpr le2 l ae v2 ->
    v1 <> v2.
Proof.
  intros until v2.
  intros inj.
  intros le_neq.
  intros le1_inrange le2_inrange.
  intros eval_le1 eval_le2.

  induction ae.

  - (* Eindvar *)
    inversion eval_le1.
    inversion eval_le2.

    assert (loopschedule l (viv le1) <>
            loopschedule l (viv le2)) as indvar_neq. 
    apply indvar_distinct_per_iteration;
      eassumption.

    assert (loopschedule l (viv le1) < loopub l)%nat as indvar1_inrange.
    apply indvar_in_range_1. assumption.

    
    assert (loopschedule l (viv le2) < loopub l)%nat as indvar2_inrange.
    apply indvar_in_range_1. assumption.

    assert (Z.of_nat (loopub l) < Int64.max_unsigned).
    apply (loopub_in_range_witness l).

    
    assert (Int64.max_unsigned < Int64.modulus).
    unfold Int64.max_unsigned.
    omega.
    
    apply nat_to_vlong_neq_2; omega.

  - (* Econstoffset, not injective *)
    inversion inj.
Qed.
    
  

Lemma injective_affineexpr_2:
  forall (ae: affineexpr) (l: loop) (le1 le2: loopenv)
    (v: val),
    injective_affineexpr_b ae = true ->
    (viv le1 < loopub l)%nat ->
    (viv le2 < loopub l)%nat ->
    eval_affineexpr le1 l ae v ->
    eval_affineexpr le2 l ae v ->
    le1 = le2.
Proof.
  intros until v.
  intros inj.
  intros le1_inrange le2_inrange.
  intros eval_le1 eval_le2.


  induction ae.

  - (* Eindvar *)
    inversion eval_le1.
    inversion eval_le2.

    rename H0 into v_as_le1.
    rename H1 into v_as_le2.

    assert (Int64.max_unsigned < Int64.modulus).
    unfold Int64.max_unsigned.
    omega.

    
    destruct (loopschedulewitness l).

    assert ((loopschedule l (viv le1)) < loopub l)%nat.
    apply inrange_forward0. auto.

    
    assert ((loopschedule l (viv le2)) < loopub l)%nat.
    apply inrange_forward0. auto.

    assert (Z.of_nat (loopub l) < Int64.max_unsigned).
    apply (loopub_in_range_witness l).


    
    assert (loopschedule l (viv le1) = loopschedule l (viv le2)) as indvar_eq.
    apply nat_to_vlong_inj.
    omega.
    omega.
    rewrite v_as_le1, v_as_le2.
    auto.

    assert (viv le1 = viv le2) as viv_eq.
    eapply inverseTillUb_inj_1.
    apply (loopschedulewitness l).
    auto.
    auto.
    auto.

    destruct le1, le2.
    simpl in viv_eq.
    rewrite viv_eq.
    reflexivity.



  - (* Econstoffset, not injective *)
    inversion inj.
Qed.

(* Find the lenv *for* lnew that will give the same iteration variable
    as that of lold.

That is:

viv --loldscheudle--> i1
? --lnewschedule--> i1

answer: ? = lnewschedule_inv(i1)
i1 = loldschedule(viv)

answer := lnewschedule_inv(loldschedule(viv))
*)


Definition equivalent_lenv (leold: loopenv)
           (lold: loop)
           (lnew: loop) : loopenv :=
  mkLenv ((loopscheduleinv lnew) ((loopschedule lold)(viv leold))).

(* Equivalent lenv actually gives us the correct value for affine expressions *)
Lemma equivalent_lenv_equal_affineexpr: forall (leold: loopenv) (lold: loop) (lnew: loop),
    forall (ae: affineexpr) (v: val),
      (viv leold < loopub lold)%nat ->
      (* TODO: this maybe too tight a requirement *)
      (loopub lold = loopub lnew) ->
    eval_affineexpr leold lold ae v ->
    eval_affineexpr (equivalent_lenv leold lold lnew) lnew ae v.
Proof.
  intros until v.
  intros viv_inrange.
  intros loopub_equal.
  intros eval_old.
  induction ae.
  - remember (equivalent_lenv leold lold lnew) as lenew.
    assert (v = nat_to_vlong (loopschedule lnew (viv lenew))) as v_eq_indvar.
    inversion eval_old. subst.
    unfold equivalent_lenv.
    simpl.
    destruct (loopschedulewitness lnew).
    rewrite inverse_forward0.
    reflexivity.

    rewrite <- loopub_equal.

    destruct (loopschedulewitness lold).
    apply inrange_forward1.
    assumption.

    rewrite v_eq_indvar.
    apply eval_Eindvar.

  - inversion eval_old.
    subst.
    apply eval_Econstoffset.
Qed.
    

(* if we take an equivalent statement in the new loop, then we will compute the same result *)
Lemma equivalent_lenv_equal_stmt: forall (leold: loopenv) (lold: loop) (lnew: loop),
    forall (s:stmt) (m m': mem),
      (viv leold < loopub lold)%nat ->
      (* TODO: this maybe too tight a requirement *)
      (loopub lold = loopub lnew) ->
    exec_stmt leold lold m s m' ->
    exec_stmt (equivalent_lenv leold lold lnew) lnew m s m'.
Proof.
  intros until m'.
  intros viv_old_inrange.
  intros loopub_equal.
  intros exec_old.

  induction s.
  inversion exec_old. subst.

  - eapply exec_Sstore.
    unfold equivalent_lenv.
    simpl.

    destruct (loopschedulewitness lnew).
    apply inrange_backward0.
    rewrite <- loopub_equal.

    destruct (loopschedulewitness lold).
    apply inrange_forward1.

    assumption.


    apply  equivalent_lenv_equal_affineexpr; eassumption.
    auto.
Qed.

Section MEMORYINLOOP.
  Definition memStructureEq (m m': mem) : Prop :=
    Mem.mem_access m = Mem.mem_access m' /\
    Mem.nextblock m = Mem.nextblock m'.

  Lemma memStructureEq_refl:
    forall (m: mem),
      memStructureEq m m.
  Proof.
    intros m.
    unfold memStructureEq.
    auto.
  Qed.

  Lemma memStructureEq_sym:
    forall (m m': mem),
      memStructureEq m m' ->
      memStructureEq m' m.
  Proof.
    intros until m'.
    unfold memStructureEq.
    intros eqs.
    destruct eqs.
    auto.
  Qed.

  Lemma memStructureEq_trans:
    forall (m m' m'': mem),
      memStructureEq m m' ->
      memStructureEq m' m'' ->
      memStructureEq m m''.
  Proof.
    intros.
    unfold memStructureEq in *.
    destruct m, m', m''.
    simpl in *.
    intuition;
      subst; reflexivity.
   Qed.
    

  (* A view of memory where they are structurally equal, but only differ on
     memory content *)
  Lemma memStructureEq_mem_equal: forall (m m': mem),
      memStructureEq m m'->
      Mem.mem_contents m = Mem.mem_contents m' ->
      m = m'.
  Proof.
    intros until m'.
    intros structureq.
    intros contenteq.
    unfold memStructureEq in *.
    destruct structureq as [accesseq nextblockeq].
             
    destruct m, m'. simpl in *.
    apply Mem.mkmem_ext; auto.
  Qed.

  Lemma memStructureEq_store:
    forall  (m m': mem)
       (chunk: AST.memory_chunk)
       (b: Values.block) (ofs: Z) (v: val),
      Mem.store chunk m b ofs v = Some m' ->
      memStructureEq m m'.
  Proof.
    intros until v.
    intros store.
    unfold memStructureEq.
    split.
    symmetry.
    eapply Mem.store_access.
    eassumption.

    symmetry.
    eapply Mem.nextblock_store.
    eassumption.
  Qed.

  Lemma memStructureEq_storev:
    forall (m m': mem)
      (chunk: memory_chunk)
      (addr v: val),
      Mem.storev chunk m addr v = Some m' ->
      memStructureEq m m'.
  Proof.
    intros until v.
    intros store.
    unfold Mem.storev in store.
    induction addr; try inversion store.

    eapply memStructureEq_store.
    eassumption.
  Qed.

  Lemma memStructureEq_exec_stmt:
    forall (m m': mem)
      (s: stmt)
      (le : loopenv)
      (l: loop),
      exec_stmt le l m s m' ->
      memStructureEq m m'.
  Proof.
    intros until l.
    intros execs.
    induction s.
    - (* Sstore *)
      inversion execs; subst.
      eapply memStructureEq_storev.
      eassumption.
   Qed.


  Lemma memStructureEq_exec_loop:
    forall (m m': mem)
      (le le': loopenv)
      (l: loop),
      exec_loop le m l m' le' ->
      memStructureEq m m'.
  Proof.
    intros until l.
    intros execl.
    induction execl; subst.
    - eapply memStructureEq_refl.
    - assert (memStructureEq m m') as m_seq_m'.
      eapply memStructureEq_exec_stmt.
      eassumption.
      eapply memStructureEq_trans; eassumption.
  Qed.

  Definition id_inj (m m': mem): Val.meminj :=
    fun (b: block) =>
      if plt b (Mem.nextblock m)
      then Some (b, 0)
      else None.
  
  Lemma memStructureEq_perm_eq: forall (m m': mem)
                               (b: block)
                               (ofs: Z)
                               (k: perm_kind)
                               (p: permission),
      memStructureEq m m'->
      Mem.perm m b ofs k p ->
      Mem.perm m' b ofs k p.
  Proof.
    unfold Mem.perm.
    unfold memStructureEq.
    intros until p.
    intros structureeq.
    destruct structureeq as [acceq nextblockeq].
    intros perm_m.
    rewrite <- acceq.
    assumption.
  Qed.

  Lemma memval_inject_id_inj_refl: forall (m m': mem) (mval: memval),
      (forall (b:block) (ofs:ptrofs),
          Val.inject
            (id_inj m m')
            (Vptr b ofs)
            (Vptr b ofs)) ->
      memval_inject (id_inj m m') mval mval.
  Proof.
    intros until mval.
    intros ptr_injector.
    destruct mval.
    eapply memval_inject_undef.
    eapply memval_inject_byte.
    eapply memval_inject_frag.
    induction v.
    - apply Val.val_inject_undef.
    - apply Val.inject_int.
    - apply Val.inject_long.
    - apply Val.inject_float.
    - apply Val.inject_single.
    - apply ptr_injector.
  Qed.

  
  (* mem_inj is some sort of "generic injection", that is less specific
     than Mem.inject *)
  Lemma memStructureEq_extensional_mem_inj:
    forall (m m': mem),
      memStructureEq m m' ->
      (forall (b: block) (ofs: positive), (Mem.mem_contents m )#b # ofs = (Mem.mem_contents m')#b # ofs) ->
      (forall (b: block) (i:ptrofs), Val.inject (id_inj m m') (Vptr b i) (Vptr b i)) ->
      Mem.mem_inj (id_inj m m') m m'.
  Proof.
    intros until m'.
    intros structureeq.
    intros pointwise_eq.
    intros inject_pointer.
    apply Mem.mk_mem_inj.
    - intros until p.
      unfold id_inj.
      intros b1_b2_rel.

      destruct (plt b1 (Mem.nextblock m)); inversion b1_b2_rel.
      inversion b1_b2_rel.
      subst.
      assert (ofs + 0 = ofs) as ofseq.
      omega.
      rewrite ofseq.
      
      unfold memStructureEq in structureeq.
      intros m_perm.

      
      eapply memStructureEq_perm_eq.
      eassumption.
      assumption.

    -  intros until p.
       intros b1_b2_rel.
       unfold id_inj in b1_b2_rel.
       destruct (plt b1 (Mem.nextblock m)); inversion b1_b2_rel.
       
       inversion b1_b2_rel.
       subst.

       intros mem_perm.
       (* I was fucking around, I did not know that this would work.
       TODO: what is this "|" operator anyway? "(X | Y)")
        *)
       exists 0.
       omega.
       

    - intros until delta.
      intros b1_b2_rel.
      unfold id_inj in b1_b2_rel.

      
      destruct (plt b1 (Mem.nextblock m)); inversion b1_b2_rel.
      subst.
      clear b1_b2_rel.

      intros perm_readable.

      
      cut (ofs + 0 = ofs).
      intros ofs_plus_0_eq.
      rewrite ofs_plus_0_eq.
      clear ofs_plus_0_eq.

      remember (ZMap.get ofs (Mem.mem_contents m) # b2) as vinj1.
      remember (ZMap.get ofs (Mem.mem_contents m') # b2) as vinj2.

      assert (vinj1 = vinj2) as vinj_eq.
      rewrite Heqvinj1.
      rewrite Heqvinj2.
      eapply pointwise_eq.

      rewrite vinj_eq in *.

      destruct vinj2.

      +  eapply memval_inject_undef.
      + eapply memval_inject_byte.
      + eapply memval_inject_frag.
        induction v.
        * apply Val.val_inject_undef.
        * apply Val.inject_int.
        * apply Val.inject_long.
        * apply Val.inject_float.
        * apply Val.inject_single.
        * apply inject_pointer.
      +  omega.
  Qed.

  Lemma memStructureEq_nextblock_eq:
    forall (m m': mem),
      memStructureEq m m' ->
      Mem.nextblock m = Mem.nextblock m'.
  Proof.
    intros until m'.
    intros structureeq.
    unfold memStructureEq in structureeq.
    destruct structureeq.
    auto.
  Qed.
    

  Lemma id_inj_no_overlap: forall (m m': mem),
      Mem.meminj_no_overlap (id_inj m m') m.
  Proof.
    intros until m'.
    unfold id_inj; intros; red; intros.
    destruct (plt b1 (Mem.nextblock m)); inversion H0; subst.
    destruct (plt b2 (Mem.nextblock m)); inversion H1; subst.
    auto.
  Qed.
  
  Lemma memStructureEq_extensional_inject:
    forall (m m': mem),
      memStructureEq m m' ->
      (forall (b: block) (ofs: positive),
          (Mem.mem_contents m )#b# ofs =
          (Mem.mem_contents m')#b#ofs) ->
      Mem.mem_inj (id_inj m m') m m' ->
      Mem.inject (id_inj m m') m m'.
  Proof.
    intros until m'.
    intros structureeq.
    intros extensional_eq.
    constructor.
    - auto.
    - intros.
      unfold id_inj.
      apply pred_dec_false.
      auto.
    - intros until delta.
      intros id_inj_val.
      unfold Mem.valid_block.
      unfold id_inj in id_inj_val.
      destruct (plt b (Mem.nextblock m));
        inversion id_inj_val.
      subst.
      cut (Mem.nextblock m = Mem.nextblock m' ).
      intros nextblockeq.
      rewrite <- nextblockeq.
      assumption.

      apply memStructureEq_nextblock_eq.
      assumption.

    -  (* no overlap *)
      apply id_inj_no_overlap.

    - (* range *)
      unfold id_inj; intros.
      destruct (plt b (Mem.nextblock m)); inv H0.
      generalize (Ptrofs.unsigned_range_2 ofs). omega.

    -  (* perm inv *)
      unfold id_inj; intros.
      destruct (plt b1 (Mem.nextblock m)); inv H0.
      rewrite Z.add_0_r in H1.
      assert (Mem.perm m b2 ofs k p).
      eapply memStructureEq_perm_eq.
      cut (memStructureEq m' m).
      intros.
      eassumption.
      apply memStructureEq_sym.
      auto.
      auto.
      auto.
  Qed.
End MEMORYINLOOP.


(* Theory of locations that a loop writes to, so we can later check if
a loop writes to a memory location or not, and reason about this fact
*)
Section LOOPWRITELOCATIONS.
  Definition StmtWriteLocation (s: stmt) (viv: vindvar) : block * positive.
        
      
    

(* locations that are written to by a loop *)
Definition LoopWriteLocations_rec (l: loop) (viv: vindvar) : list (block * positive) :=
  if (loopub l <=? viv)%nat
  then List.nil
  else List.nil.
         
                                                                  
Definition LoopWriteLocations (l: loop):list (block * positive) :=
  LoopWriteLocations_rec l 0%nat.

End LOOPWRITELOCATIONS.
      
  
      
Lemma exec_stmt_matches_in_loop_reversal_if_ix_injective:
  forall (lub: upperbound)
    (lub_in_range: Z.of_nat lub < Int64.max_unsigned)
    (ivname: ident)
    (le: loopenv)
    (m: mem)
    (s: stmt),
    injective_stmt_b s = true ->
    forall (l: loop)
      (mid: mem),
      l = (loop_id_schedule lub lub_in_range ivname s) ->
      exec_stmt le l m s mid ->
      forall (lrev: loop)
        (mrev: mem),
    lrev =  (loop_reversed_schedule lub lub_in_range ivname s) ->
    exec_stmt le lrev m s mrev ->
    Mem.inject (id_inj mid mrev) mid mrev.
Proof.
  intros until s.
  intros s_inj.
  intros until mid.
  intros l_id.
  intros exec_lid.

  intros until mrev.
  intros l_rev.
  intros exec_lrev.

  eapply memStructureEq_extensional_inject.

  assert (memStructureEq mid mrev) as structure_eq.
  eapply memStructureEq_trans.
  eapply memStructureEq_sym.
  eapply memStructureEq_exec_stmt.
  eassumption.
  eapply memStructureEq_exec_stmt.
  eassumption.

  exact structure_eq.

  intros.
  

  

  
