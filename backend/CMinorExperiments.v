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
Require Import Floats.
Require Import Archi.

Definition nat_to_int32 (n: nat): int := (Int.repr (Z.of_nat n)).
Definition nat_to_int64 (n: nat): int64 := (Int64.repr (Z.of_nat n)).
Definition nat_to_ptrofs (n: nat): ptrofs := (Ptrofs.repr (Z.of_nat n)).
Definition nat_to_long_expr(n: nat): expr := Econst (Olongconst (nat_to_int64 n)).
Definition nat_to_int_expr(n: nat): expr := Econst (Ointconst (nat_to_int32 n)).

Definition STORE_CHUNK_SIZE: memory_chunk := Mint8unsigned.

(* We need this so we don't have to reason about fucking pointers to pointers
and whatnot *)
Definition mem_no_pointers (m: mem) : Prop :=
  forall bptr i q n b ofs,
    Fragment (Vptr bptr i) q n <> ZMap.get ofs (Mem.mem_contents m) # b.


Lemma encode_int32_hd_error:
  forall n,
    hd_error
      (encode_val STORE_CHUNK_SIZE (Vint (nat_to_int32 n))) = 
      Some ((Byte (Byte.repr (Int.unsigned (nat_to_int32 n))))).
Proof.
  intros.
  simpl.
  unfold encode_int.
  unfold inj_bytes.
  unfold bytes_of_int.
  simpl.
  unfold hd_error.
  unfold rev_if_be.
  assert (Archi.big_endian = false).
  auto.
  rewrite H.
  simpl.
  auto.
Qed.


Definition arrofs_expr (arrname: ident) (ofs: nat) : expr :=
  Econst (Oaddrsymbol arrname (nat_to_ptrofs ofs)).

(* a handy alias for storing 1 byte value *)
Definition SstoreValAt (arrname: ident) (v: nat) (ix: nat) :=
  Cminor.Sstore STORE_CHUNK_SIZE (arrofs_expr arrname ix)
                (nat_to_int_expr v).
Lemma eval_expr_arrofs: forall (arrname: ident) (ofs: nat),
    forall (ge: genv) (sp: val) (e: env) (m: mem),
    forall (arrblock: block),
      Genv.find_symbol ge arrname = Some arrblock ->
      eval_expr ge sp e m
                (arrofs_expr arrname ofs)
                (Vptr arrblock (nat_to_ptrofs ofs)).
Proof.
  intros until arrblock.
  intros GENV_AT_ARRNAME.
  eapply eval_Econst.
  simpl.

  unfold Genv.symbol_address.
  rewrite GENV_AT_ARRNAME.
  auto.
Qed.

(*
Error:
Unexpected error during scheme creation: Anomaly
                                         "Uncaught exception Type_errors.TypeError(_, _)."
Please report at http://coq.inria.fr/bugs/.
Scheme Equality for memval.
*)

Lemma val_eq_dec: forall (v1 v2: val), {v1 = v2} + {v1 <> v2}.
Proof.
  intros.
  decide equality.
  apply Int.eq_dec.
  apply Int64.eq_dec.
  apply Float.eq_dec.
  apply Float32.eq_dec.
  apply Ptrofs.eq_dec.
  apply eq_block.
Qed.
Lemma memval_eq_dec: forall (mv1 mv2: memval), {mv1 = mv2} + {mv1 <> mv2}.
Proof.
  intros.
  decide equality.
  apply Byte.eq_dec.
  apply Nat.eq_dec.
  apply Memdata.quantity_eq.
  apply val_eq_dec.
Qed.
   
    

(* I have no idea why I need to prove this as a separate theorem *)
Lemma integer_split_number_line:
  forall (y z: Z), y <> z -> y < z \/ y >= z + 1.
Proof.
  intros.
  omega.
Qed.



Definition val_no_pointer (v: val) : Prop :=
  forall bptr i, v <> Vptr bptr i.

Definition val_no_undef (v: val) : Prop := v <> Vundef.

Hint Transparent val_no_pointer.
Hint Transparent val_no_undef.


Section VAL_INJECT.
  
  Variable ma: mem.
  Variable injf: meminj.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock ma).
  
  Lemma val_inject_trans:
    forall v1 v2 v3,
      Val.inject injf v1 v2 ->
      Val.inject injf v2 v3 ->
      Val.inject injf v1 v3.
  Proof.
    intros until v3.
    intros INJ12 INJ23.

    inversion INJ12; subst; inversion INJ23; subst; try constructor.

    unfold Mem.flat_inj in H.
    unfold Mem.flat_inj in H2.

    destruct (plt b2 (Mem.nextblock ma)); try congruence.
    destruct (plt b1 (Mem.nextblock ma)); try congruence.
    inversion H2. inversion H. subst.
    replace (Ptrofs.add (Ptrofs.add ofs1 (Ptrofs.repr 0)) (Ptrofs.repr 0)) with ofs1.
    eapply Val.inject_ptr.
    unfold Mem.flat_inj.
    destruct (plt b3 (Mem.nextblock ma)); try congruence.
    auto.

    simpl.
    symmetry.
    apply Ptrofs.add_zero.
    symmetry.
    rewrite Ptrofs.add_zero.
    rewrite Ptrofs.add_zero.
    auto.
  Qed.
    
End VAL_INJECT.

    
    


Section MEMVAL_INJECT.
  Variable ma: mem.
  Variable injf: meminj.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock ma).

  (* When we disallow pointers, we can make memval_inject reflexive *)
  Lemma memval_inject_refl:
    forall (mv: memval),
      (forall b ptrofs q n, mv <> Fragment (Vptr b ptrofs) q n) -> 
      memval_inject injf mv mv.
  Proof.
    intros.
    destruct mv; try constructor.

    (* val inject *)
    destruct v; try constructor.
    (* pointer injection *)
    specialize (H b i q n). contradiction.
  Qed.




    
End MEMVAL_INJECT.

Section MEMSTORE.

  Variable m m': mem.

  Variable wb: block.
  Variable rb: block.

  Variable wofs: Z.
  Variable wv: val.


  Variable MSTORE: Mem.store STORE_CHUNK_SIZE m wb wofs wv = Some m'.

  Variable ma: mem.
  Variable injf: meminj.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock ma).



End MEMSTORE.

Section STMT.
  Variable m m': mem.
  (* Variable NOPOINTERS : mem_no_pointers m. *)
  
  
  Variable arrname: ident.
  Variable wix: nat.
  Variable wval: nat.

  Variable s: Cminor.stmt.
  Variable sVAL: s = SstoreValAt arrname wval wix.

  
  Variable ge: genv.
  Variable f: function.
  Variable sp: val.
  Variable e e': env.
  Variable EXECS: exec_stmt ge f sp e m s E0 e' m' Out_normal.


  Variable injf: meminj.
  Variable ma: mem.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock ma).

  Variable wb: block.
  Variable wofs: ptrofs.
  (* the array offset has a concrete value,
   which is the pointer wb with offset wofs *)
  Variable WBVAL: eval_expr ge sp e m (arrofs_expr arrname wix) (Vptr wb wofs).

  (* Hypothesis STORE: store chunk       m1 b  ofs v = Some m2. *)
  (* STOREV : Mem.store STORE_CHUNK_SIZE m wb (Ptrofs.unsigned wofs) v = Some m' *)
  Lemma mem_contents_sstore:
    Mem.mem_contents m' = 
    PMap.set wb
             (Mem.setN
                (encode_val
                   STORE_CHUNK_SIZE
                   (Vint (nat_to_int32 wval)))
                (Ptrofs.unsigned wofs)
                m.(Mem.mem_contents)#wb)
             m.(Mem.mem_contents).
  Proof.
    rewrite sVAL in EXECS.
    inversion EXECS. subst.

    rename H10 into STOREV.
    unfold Mem.storev in STOREV.

    assert (VADDR: vaddr = Vptr wb wofs).
    eapply eval_expr_is_function; eassumption.
    subst.

    rename H7 into VAL.
    inversion VAL. subst.

    rename H0 into VAL_CONSTANT.
    simpl in VAL_CONSTANT.
    inversion VAL_CONSTANT.
    subst.

    apply Mem.store_mem_contents.
    auto.
  Qed.
    


  
  Lemma mem_contents_equal_no_block_alias_for_sstore:
    forall rb ,
      rb <> wb ->
      (Mem.mem_contents m') # rb = (Mem.mem_contents m) # rb.
  Proof.
    intros rb.
    intros NOALIAS.

    
    rewrite sVAL in EXECS.
    inversion EXECS. subst.

    
    assert (vaddr = Vptr wb wofs) as VADDR_EQ_WBVAL.
    eapply eval_expr_is_function; eassumption.
    subst.

    rename H10 into STOREM.
    unfold Mem.storev in STOREM.



    erewrite Mem.store_mem_contents with (m1 := m)
                                         (chunk := STORE_CHUNK_SIZE)
                                         (b := wb)
                                         (v := v);
      try eassumption.
    erewrite PMap.gso; try eassumption.
    reflexivity.
  Qed.

  
  
  Lemma mem_contents_equal_no_offset_alias_for_sstore:
    forall (rb: block) (ofs: Z),
      rb = wb ->
      ofs <> (Ptrofs.unsigned wofs) ->
      (ZMap.get ofs (Mem.mem_contents m') # rb) =
      (ZMap.get ofs (Mem.mem_contents m) # rb).
  Proof.
    intros until ofs.
    intros WBALIAS.
    subst.
    intros OFS_NOALIAS.

    
    inversion EXECS. subst.

    
    assert (vaddr = Vptr wb wofs) as VADDR_EQ_WBVAL.
    eapply eval_expr_is_function; eassumption.
    subst.

    rename H10 into STOREM.
    unfold Mem.storev in STOREM.



    erewrite Mem.store_mem_contents with (m1 := m)
                                         (chunk := STORE_CHUNK_SIZE)
                                         (b := wb)
                                         (v := v);
      try eassumption.
    erewrite PMap.gss; try eassumption.
    try erewrite Mem.setN_outside; try auto.

    rewrite Memdata.encode_val_length.
    simpl.
    omega.
  Qed.

  
  Lemma mem_contents_offset_alias_for_sstore:
    forall (rb: block) (ofs: Z),
      rb = wb ->
      ofs = (Ptrofs.unsigned wofs) ->
      ZMap.get ofs (Mem.mem_contents m') # rb =
      Byte (Byte.repr (Int.unsigned (nat_to_int32 wval))).
  Proof.
    intros until ofs.
    intros WBALIAS.
    subst.
    intros OFS_NOALIAS.

    
    inversion EXECS. subst.

    
    assert (vaddr = Vptr wb wofs) as VADDR_EQ_WBVAL.
    eapply eval_expr_is_function; eassumption.
    subst.

    rename H10 into STOREM.
    unfold Mem.storev in STOREM.


    erewrite Mem.store_mem_contents with (m1 := m)
                                         (chunk := STORE_CHUNK_SIZE)
                                         (b := wb)
                                         (v := v);
      try eassumption.
    erewrite PMap.gss; try eassumption.

    
   remember (ZMap.get (Ptrofs.unsigned wofs)
    (Mem.setN (encode_val STORE_CHUNK_SIZE v) (Ptrofs.unsigned wofs)
       (Mem.mem_contents m) # wb)) as M'_AT_OFFSET.

   assert (ENCODEV: Some (M'_AT_OFFSET) =
                    List.hd_error (encode_val Mint8unsigned v)).
   rewrite HeqM'_AT_OFFSET.
   erewrite Mem.get_setN_at_base_chunk_Mint8unsigned;
     try eauto;
     try eassumption.

   assert (VVAL: v = Vint (nat_to_int32 wval)).
   rename H7 into EVALV.
   inversion EVALV. subst.
   rename H0 into EVALV_CONST.
   simpl in EVALV_CONST.
   inversion EVALV_CONST.
   reflexivity.

   
   rewrite VVAL in ENCODEV.

   rewrite encode_int32_hd_error in ENCODEV.
   inversion ENCODEV.
   reflexivity.
  Qed.


  

  Lemma sstore_valid_block:
    forall (b: block), Mem.valid_block m b -> Mem.valid_block m' b.
  Proof.
    intros b.
    intros B_VALID_IN_M.

    rewrite sVAL in EXECS. inversion EXECS. subst.

    assert (VADDR: vaddr = Vptr wb wofs).
    eapply eval_expr_is_function; eassumption.
    subst.


    rename H10 into STOREV.
    unfold Mem.storev in STOREV.

    eapply Mem.store_valid_block_1; eassumption.
  Qed.

  
  Lemma sstore_invalid_block_2:
    forall (b: block), ~ Mem.valid_block m' b -> ~ Mem.valid_block m b.
  Proof.
    intros b.
    intros B_INVALID_IN_M.

    rewrite sVAL in EXECS. inversion EXECS. subst.

    assert (VADDR: vaddr = Vptr wb wofs).
    eapply eval_expr_is_function; eassumption.
    subst.


    rename H10 into STOREV.
    unfold Mem.storev in STOREV.

    assert (MCASES: Mem.valid_block m b \/ ~Mem.valid_block m b).
    unfold Mem.valid_block. unfold Plt. 
    zify.
    omega.

    destruct MCASES as [MVALID | MINVALID]; try auto.

    assert (CONTRA: Mem.valid_block m' b).
    eapply Mem.store_valid_block_1; try eassumption.
    contradiction.
  Qed.

  
  Lemma sstore_perm_1:
    forall (b': block) (ofs':Z) (k: perm_kind) (p: permission),
      Mem.perm m b' ofs' k p -> Mem.perm m' b' ofs' k p.
  Proof.
    intros until p.
    intros PERM.

    
    rewrite sVAL in EXECS. inversion EXECS. subst.

    assert (VADDR: vaddr = Vptr wb wofs).
    eapply eval_expr_is_function; eassumption.
    subst.


    rename H10 into STOREV.
    unfold Mem.storev in STOREV.

    eapply Mem.perm_store_1; eassumption.
  Qed.

  
  Lemma sstore_perm_2:
    forall (b': block) (ofs':Z) (k: perm_kind) (p: permission),
      Mem.perm m' b' ofs' k p -> Mem.perm m b' ofs' k p.
  Proof.
    intros until p.
    intros PERM.

    
    rewrite sVAL in EXECS. inversion EXECS. subst.

    assert (VADDR: vaddr = Vptr wb wofs).
    eapply eval_expr_is_function; eassumption.
    subst.


    rename H10 into STOREV.
    unfold Mem.storev in STOREV.

    eapply Mem.perm_store_2; eassumption.
  Qed.
  
  
End STMT.

  


Section STMTSEQ.
  Variable m m': mem.
  (* Variable NOPOINTERS: mem_no_pointers m. *)
  (* Variable NOUNDEF: mem_no_undef m. *)
  Variable arrname: ident.

  Variable wix1 wix2 : nat.
  Variable wval1 wval2: nat.


  (* a[wix1] = wval1] *)
  Variable s1: Cminor.stmt.
  Variable s1DEFN : s1 = SstoreValAt arrname wval1 wix1.

  (* a[wix2] = wval2 *)
  Variable s2: Cminor.stmt.
  Variable s2DEFN : s2 = SstoreValAt arrname wval2 wix2.

  Variable s12 : Cminor.stmt.
  Variable s12DEFN : s12 = Sseq s1 s2.

  Variable ge: genv.
  Variable f: function.
  Variable sp: val.
  Variable e e': env.
  Variable EXECSSEQ: exec_stmt ge f sp e m s12 E0 e' m' Out_normal.
  
  Variable injf: meminj.
  Variable ma: mem.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock ma).

   
  Variable arrblock : block.
  Variable GENV_AT_ARR: Genv.find_symbol ge arrname = Some arrblock.

  
  (* 
  Variable wb1 wb2: block.
  Variable wofs1 wofs2: ptrofs.
  (* the array offset has a concrete value,
   which is the pointer wb with offset wofs *)
  Variable WB1VAL: eval_expr ge sp e m
                             (arrofs_expr arrname wix1)
                             (Vptr wb1 wofs1).
  
  (* Variable WB2VAL: eval_expr ge sp e1 m1
                             (arrofs_expr arrname wix2)
                             (Vptr wb2 wofs2). *)
   *)

  Lemma mem_contents_equal_no_block_alias_for_sseq:
    forall rb ,
      rb <> arrblock ->
      (Mem.mem_contents m') # rb = (Mem.mem_contents m) # rb.
  Proof.
    intros rb NOALIAS.

    
    inversion EXECSSEQ; subst; try congruence.


    assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
    apply destruct_trace_app_eq_E0. assumption.

    destruct t1_t2_E0 as [t1E0 t2E0].
    subst.

    rename H6 into Sseq_EQUIV.
    inversion Sseq_EQUIV.
    subst.

    rename H into EXECS1.
    rename H0 into EXECS2.

    assert ((Mem.mem_contents m1) # rb =
            (Mem.mem_contents m) # rb) as M1_EQ_M.
    eapply mem_contents_equal_no_block_alias_for_sstore; try eassumption; try auto.
    eapply eval_expr_arrofs. eassumption.

    

    assert ((Mem.mem_contents m') # rb =
            (Mem.mem_contents m1) # rb) as M1_EQ_M'.
    eapply mem_contents_equal_no_block_alias_for_sstore with
        (arrname := arrname)
        (wix := wix2)
        (wval := wval2); try eassumption; try auto.
    eapply eval_expr_arrofs. eassumption.

    rewrite <- M1_EQ_M.
    rewrite M1_EQ_M'.
    reflexivity.
  Qed.

  Lemma mem_contents_equal_no_offset_alias_for_sseq:
    forall (rb: block) (ofs: Z),
      rb = arrblock ->
      ofs <> Ptrofs.unsigned (nat_to_ptrofs wix1) ->
      ofs <> Ptrofs.unsigned (nat_to_ptrofs wix2) ->

      (ZMap.get ofs (Mem.mem_contents m') # rb) =
      (ZMap.get ofs (Mem.mem_contents m) # rb).
  Proof.
    intros until ofs.
    intros RB_ALIAS. subst.
    intros OFS_NO_ALIAS_WIX1 OFS_NO_ALIAS_WIX2.
    
    inversion EXECSSEQ; subst; try congruence.


    assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
    apply destruct_trace_app_eq_E0. assumption.

    destruct t1_t2_E0 as [t1E0 t2E0].
    subst.


    rename H1 into EXECS1.
    rename H6 into EXECS2.

    assert (ZMap.get ofs (Mem.mem_contents m1) # arrblock =
            (ZMap.get ofs (Mem.mem_contents m) # arrblock)) as M1_EQ_M.
    
    eapply mem_contents_equal_no_offset_alias_for_sstore with
        (wval := wval1) (wix := wix1); try auto.
    exact EXECS1.
    eapply eval_expr_arrofs; try eassumption; try auto.
    eassumption.

    
    assert (ZMap.get ofs (Mem.mem_contents m') # arrblock =
            (ZMap.get ofs (Mem.mem_contents m1) # arrblock)) as M1_EQ_M'.
    
    eapply mem_contents_equal_no_offset_alias_for_sstore with
        (wval := wval2) (wix := wix2); try auto.
    exact EXECS2.
    eapply eval_expr_arrofs; try eassumption; try auto.
    eassumption.

    rewrite  M1_EQ_M'.
    rewrite  M1_EQ_M.
    reflexivity.
  Qed.

  
  Lemma mem_contents_offset_alias_for_sseq_1:
    forall (rb: block) (ofs: Z),
      rb = arrblock ->
      ofs = Ptrofs.unsigned (nat_to_ptrofs wix1) ->
      ofs <> Ptrofs.unsigned (nat_to_ptrofs wix2) ->
      ZMap.get ofs (Mem.mem_contents m') # rb =
      Byte (Byte.repr (Int.unsigned (nat_to_int32 wval1))).
  Proof.
    intros until ofs.
    intros RBALIAS OFS_ALIAS_WIX1 OFS_NOALIAS_WIX2.

    
    rewrite s12DEFN in EXECSSEQ.
    rewrite s1DEFN in EXECSSEQ.
    rewrite s2DEFN in EXECSSEQ.

    inversion EXECSSEQ; try contradiction. subst.

    rename H1 into EXECS1.
    rename H6 into EXECS2.

    assert (t1_t2_E0: t1 = E0 /\ t2 = E0).
    apply destruct_trace_app_eq_E0. assumption.

    destruct t1_t2_E0 as [t1E0 t2E0].
    subst.

    assert (M'_EQ_M_AT_BLOCK_OFS:
    (ZMap.get (Ptrofs.unsigned (nat_to_ptrofs wix1))
              (Mem.mem_contents m') # arrblock) =
    (ZMap.get (Ptrofs.unsigned (nat_to_ptrofs wix1))
              (Mem.mem_contents m1) # arrblock)).
    eapply mem_contents_equal_no_offset_alias_for_sstore;
      try eauto; try eassumption.
    eapply eval_expr_arrofs; try eassumption; try auto.

    rewrite M'_EQ_M_AT_BLOCK_OFS.

    eapply mem_contents_offset_alias_for_sstore;
      try eassumption; try eauto.
    eapply eval_expr_arrofs; try eassumption; try auto.
  Qed.

  
  Lemma mem_contents_offset_alias_for_sseq_2:
    forall (rb: block) (ofs: Z),
      rb = arrblock ->
      ofs = Ptrofs.unsigned (nat_to_ptrofs wix2) ->
      ZMap.get ofs (Mem.mem_contents m') # rb =
      Byte (Byte.repr (Int.unsigned (nat_to_int32 wval2))).
  Proof.
    intros until ofs.
    intros RBALIAS OFS_ALIAS_WIX2.

    
    rewrite s12DEFN in EXECSSEQ.
    rewrite s1DEFN in EXECSSEQ.
    rewrite s2DEFN in EXECSSEQ.

    inversion EXECSSEQ; try contradiction. subst.

    rename H1 into EXECS1.
    rename H6 into EXECS2.

    assert (t1_t2_E0: t1 = E0 /\ t2 = E0).
    apply destruct_trace_app_eq_E0. assumption.

    destruct t1_t2_E0 as [t1E0 t2E0].
    subst.

    eapply mem_contents_offset_alias_for_sstore;
      try eassumption; try eauto.
    eapply eval_expr_arrofs; try eassumption; try auto.
  Qed.
    
             

      
      


  Lemma sseq_valid_block:
    forall (b: block), Mem.valid_block m b -> Mem.valid_block m' b.
  Proof.
    intros b VALIDBLOCK.

    rewrite s12DEFN in EXECSSEQ.
    inversion EXECSSEQ; try congruence; subst.

    assert (t1_t2_E0: t1 = E0 /\ t2 = E0).
    apply destruct_trace_app_eq_E0. assumption.
    destruct t1_t2_E0. subst.

    assert (VALIDM1: Mem.valid_block m1 b).
    eapply sstore_valid_block; try eassumption; try auto;
      apply eval_expr_arrofs; try eassumption.

    
    eapply sstore_valid_block; try eassumption; try auto;
      apply eval_expr_arrofs; try eassumption.
  Qed.

  Lemma sseq_invalid_block_2:
    forall (b: block), ~ Mem.valid_block m' b -> ~ Mem.valid_block m b.
  Proof.
    intros b INVALIDBLOCK.

    rewrite s12DEFN in EXECSSEQ.
    inversion EXECSSEQ; try congruence; subst.

    assert (t1_t2_E0: t1 = E0 /\ t2 = E0).
    apply destruct_trace_app_eq_E0. assumption.
    destruct t1_t2_E0. subst.

    assert (VALIDM1: ~ Mem.valid_block m1 b).
    eapply sstore_invalid_block_2; try eassumption; try auto;
      apply eval_expr_arrofs; try eassumption.

    
    eapply sstore_invalid_block_2; try eassumption; try auto;
      apply eval_expr_arrofs; try eassumption.
  Qed.

  
  Lemma sseq_perm_1:
    forall (b': block) (ofs':Z) (k: perm_kind) (p: permission),
      Mem.perm m b' ofs' k p -> Mem.perm m' b' ofs' k p.
  Proof.
    intros until p.
    intros PERM.

    
    rewrite s12DEFN in EXECSSEQ.
    inversion EXECSSEQ; try congruence; subst.

    assert (t1_t2_E0: t1 = E0 /\ t2 = E0).
    apply destruct_trace_app_eq_E0. assumption.
    destruct t1_t2_E0. subst.

    assert (m1PERM: Mem.perm m1 b' ofs' k p).
    eapply sstore_perm_1; try eassumption; try auto.
      apply eval_expr_arrofs; eassumption.

    eapply sstore_perm_1; try eassumption; try auto.
      apply eval_expr_arrofs; eassumption.
    
  Qed.
  
  Lemma sseq_perm_2:
    forall (b': block) (ofs':Z) (k: perm_kind) (p: permission),
      Mem.perm m' b' ofs' k p -> Mem.perm m b' ofs' k p.
  Proof.
    intros until p.
    intros PERM.

    
    rewrite s12DEFN in EXECSSEQ.
    inversion EXECSSEQ; try congruence; subst.

    assert (t1_t2_E0: t1 = E0 /\ t2 = E0).
    apply destruct_trace_app_eq_E0. assumption.
    destruct t1_t2_E0. subst.

    assert (m1PERM: Mem.perm m1 b' ofs' k p).
    eapply sstore_perm_2; try eassumption; try auto.
      apply eval_expr_arrofs; eassumption.

    eapply sstore_perm_2; try eassumption; try auto.
      apply eval_expr_arrofs; eassumption.
    
  Qed.


End STMTSEQ.

Section MEMSTRUCTURE.
  
  Record mem_structure_eq (f: meminj) (m1 m2: mem) :=
    mk_mem_structure_eq {
        mseq_perm:
          forall b1 b2 delta ofs k p,
            f b1 = Some(b2, delta) ->
            Mem.perm m1 b1 ofs k p ->
            Mem.perm m2 b2 (ofs + delta) k p;
        mseq_align:
          forall b1 b2 delta chunk ofs p,
            f b1 = Some(b2, delta) ->
            Mem.range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
            (align_chunk chunk | delta);
      }.

  Lemma mem_inj_mem_structure_eq:
    forall g m m',
      Mem.mem_inj g m m' ->
      mem_structure_eq g m m'.
  Proof.
    intros.
    inversion H.
    constructor; eassumption.
  Qed.

  Lemma mem_structure_eq_store:
    forall f ge sp  e e' m m' injf minj,
    forall chunk addr a,
      injf =  Mem.flat_inj (Mem.nextblock minj) ->
      exec_stmt ge f sp e m
                (Sstore chunk addr a)
                E0 e' m' Out_normal ->
      mem_structure_eq injf m m'.
  Proof.
    intros until a.
    intros injfVAL.
    intros EXECS.
    inversion EXECS; subst.

    rename H10 into store.
    unfold Mem.storev in store.
    destruct vaddr; try inversion store.


    constructor.
    - intros until p.
      intros inj.
      intros perm_m.

      unfold Mem.flat_inj in inj.
      destruct (plt b1 (Mem.nextblock minj)); inversion inj; subst.
      replace (ofs + 0) with ofs.

      eapply Mem.perm_store_1; try eassumption.
      omega.
    - intros until p.
      intros inj.
      intros range_perm_m.
      
      
      unfold Mem.flat_inj in inj.
      destruct (plt b1 (Mem.nextblock minj)); inversion inj; subst.

      exists 0.
      omega.
  Qed.

  
  Lemma mem_structure_eq_store_sym:
    forall m1 m2 minj,
    forall chunk b ofs v,
    forall injf,  injf =  Mem.flat_inj (Mem.nextblock minj) ->
                  mem_structure_eq injf m1 m2  ->
                  Mem.store chunk m1 b ofs v = Some m2 ->
                  mem_structure_eq injf m2 m1.
  Proof.
    intros until v.
    intros injf. intros injfVAL.
    intros eq_m1_m2.
    intros m2_as_store_m1.

    
    inversion eq_m1_m2.
    constructor.
    - intros until p.
      intros inj_b1.
      rewrite injfVAL in inj_b1.
      unfold Mem.flat_inj in inj_b1.
      destruct (plt b1 (Mem.nextblock minj));  inversion inj_b1.

      intros m2_perm.
      subst.

      replace (ofs + 0) with ofs.
      eapply Mem.perm_store_2.
      eassumption.
      replace (ofs0 + 0) with ofs0.
      assumption.
      omega.
      omega.

    - intros until p.
      intros inj_b1.
      rewrite injfVAL in inj_b1.
      unfold Mem.flat_inj in inj_b1.
      destruct (plt b1 (Mem.nextblock minj));  inversion inj_b1.
      subst.
      intros range_perm.
      exists 0.
      omega.
  Qed.
  

  Lemma mem_structure_eq_trans:
    forall m1 m2 m3 minj,
    forall injf, injf =  Mem.flat_inj (Mem.nextblock minj) ->
                 mem_structure_eq injf m1 m2  ->
                 mem_structure_eq injf m2 m3 ->
                 mem_structure_eq injf m1 m3.
  
  Proof.
    intros until minj.
    intros injf. intros injfVAL.
    intros eq12 eq23.

    inversion eq12.
    inversion eq23.
    
    constructor.

    - intros until p.
      intros inj_b1.
      intros perm.
      eapply mseq_perm1.
      eassumption.

      replace ofs with (ofs + 0).
      eapply mseq_perm0 with (b1 := b1).
      rewrite injfVAL in *.
      unfold Mem.flat_inj in *.
      destruct (plt b1 (Mem.nextblock minj));
        inversion inj_b1.
      reflexivity.
      eassumption.
      omega.

    - intros until p.
      intros inj_b1.
      intros perm.
      exists 0.
      rewrite injfVAL in inj_b1.
      unfold Mem.flat_inj in inj_b1.
      destruct (plt b1 (Mem.nextblock minj)); inversion inj_b1; try omega.
  Qed.

End MEMSTRUCTURE.


Section STMTINTERCHANGE.
  Variable m m12 m21: mem.
  Variable NOPOINTERSM: mem_no_pointers m.

  (*  No undef
  Variable NOUNDEFM: mem_no_undef m.
  Variable NOUNDEFFRAGMENT: mem_no_undef_fragment m.
  *)
  
  Variable arrname: ident.

  Variable wval1 wval2: nat.
  Variable wix1 wix2: nat.
  Variable WIX_NOALIAS:
    Ptrofs.unsigned (nat_to_ptrofs wix1) <> Ptrofs.unsigned (nat_to_ptrofs wix2).


  Variable s1 s2 s12 s21: Cminor.stmt.
  
  Variable s1VAL: s1 = SstoreValAt arrname wval1 wix1.
  Variable s2VAL: s2 = SstoreValAt arrname wval2 wix2.


  Variable s12val: s12 = Cminor.Sseq s1 s2.
  Variable s21val: s21 = Cminor.Sseq s2 s1.

  Variable injf : meminj.
  Variable injfVAL: injf = Mem.flat_inj (Mem.nextblock m).
  
  Variable begininj: Mem.inject injf m m.


  Variable ge: genv.
  Variable f: function.
  Variable sp: val.
  Variable e e': env.
  Variable exec_s12: exec_stmt ge f sp  e m s12 E0 e' m12 Out_normal.
  Variable exec_s21: exec_stmt ge f sp  e m s21 E0 e' m21 Out_normal.

  Variable arrblock : block.

  Variable GENV_AT_ARR: Genv.find_symbol ge arrname = Some arrblock.

  Lemma mem_structure_eq_m_m12:
    mem_structure_eq injf m m12.
  Proof.
    subst.
    unfold SstoreValAt in *.

    inversion exec_s12; subst; try congruence.
    assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
    apply destruct_trace_app_eq_E0. assumption.
    destruct t1_t2_E0.
    subst.

    assert (mem_structure_eq (Mem.flat_inj (Mem.nextblock m)) m m1) as eq_m_m1.
    + eapply mem_structure_eq_store.
      auto.
      eassumption.

    + assert (mem_structure_eq (Mem.flat_inj (Mem.nextblock m)) m1 m12) as eq_m1_m12.
      eapply mem_structure_eq_store.
      auto.
      eassumption.


      eapply mem_structure_eq_trans; try auto; try eassumption.
  Qed.

  
  Lemma mem_structure_eq_m_m21:
    mem_structure_eq injf m m21.
  Proof.
    subst.
    inversion exec_s21; subst; try congruence.
    assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
    apply destruct_trace_app_eq_E0. assumption.
    destruct t1_t2_E0.
    subst.

    rename m1 into m2.

    unfold SstoreValAt in *.

    assert (mem_structure_eq (Mem.flat_inj (Mem.nextblock m)) m m2) as eq_m_m2.
    + eapply mem_structure_eq_store.
      auto.
      eassumption.

    + assert (mem_structure_eq (Mem.flat_inj (Mem.nextblock m)) m2 m21) as eq_m2_m21.
      eapply mem_structure_eq_store.
      auto.
      eassumption.


      eapply mem_structure_eq_trans; try auto; eassumption.
  Qed.

  Lemma mem_structure_eq_m12_m:
    mem_structure_eq injf m12 m.
  Proof.
    constructor.

    - intros until p.
      rewrite injfVAL.
      unfold Mem.flat_inj.

      intros b2_as_b1.

      destruct (plt b1 (Mem.nextblock m)); inversion b2_as_b1; subst.
      intros perm_ma'.

      inversion exec_s12; subst; try contradiction.
      rename H1 into exec1.
      rename H6 into exec2.

      assert(t1 = E0 /\ t2 = E0) as t1_t2_E0.
      apply destruct_trace_app_eq_E0.
      eassumption.
      destruct t1_t2_E0.
      subst.

      inversion exec1. subst.
      inversion exec2. subst.

      
      rename H10 into STOREV_INTO_MA.
      rename H14 into STOREV_INTO_M1.

      rename H6 into EVALVADDR.
      rename H8 into EVALVADDR0.

      inversion EVALVADDR. subst.
      inversion EVALVADDR0. subst.

      unfold eval_constant in H0.
      unfold eval_constant in H1.

      inversion H0. inversion H1. subst.


      
      unfold Mem.storev in *.
      unfold Genv.symbol_address  in *.
      rewrite GENV_AT_ARR in *.


      assert (Mem.perm m1 b2 ofs k p) as M1_PERM.
      eapply Mem.perm_store_2; eassumption.

      
      assert (Mem.perm m b2 ofs k p) as MA_PERM.
      eapply Mem.perm_store_2; eassumption.

      replace (ofs + 0) with ofs.
      assumption.
      omega.


    - (* second theorem *)
      intros until p.
      intros INJF_B1_B2.
      intros RANGE_PERM.
      rewrite injfVAL in INJF_B1_B2.
      unfold Mem.flat_inj in INJF_B1_B2.
      destruct (plt b1 (Mem.nextblock m)); inversion INJF_B1_B2; subst.
      exists 0. omega.
  Qed.

  

  Lemma mem_structure_eq_m12_m21:
    mem_structure_eq injf m12 m21.
  Proof.
    assert (mem_structure_eq injf m m) as MEMSTRUCTURE_EQ_MA_MB.
    eapply mem_inj_mem_structure_eq. inversion begininj. eassumption.


    eapply mem_structure_eq_trans with (m2 := m). rewrite injfVAL. auto.
    eapply mem_structure_eq_m12_m.
    eapply mem_structure_eq_m_m21.
  Qed.

  

  Lemma meminj_m12_m21_no_undef: Mem.mem_inj injf m12 m21.
    
    assert (mem_structure_eq injf m12 m21) as structureeq.

    apply mem_structure_eq_m12_m21.
    constructor.

    
    - intros.
      inversion structureeq.
      eapply mseq_perm0; eassumption.

    - (* permission *)
      intros.
      inversion structureeq.
      eapply mseq_align0; eassumption.

    - (* content matching, the difficult part *)
      intros until delta.
      intros injf_b1.
      intros ma'_readable.
      rewrite injfVAL in injf_b1.
      unfold Mem.flat_inj in injf_b1.
      destruct (plt b1 (Mem.nextblock m)); try contradiction.
      inversion injf_b1.
      subst.

      
      replace (ofs + 0) with ofs.

      assert ({b2 = arrblock} + {b2 <> arrblock}) as b2CASES.
      apply Pos.eq_dec.

      destruct b2CASES as  [b2_EQ_ARRBLOCK | b2_NEQ_ARRBLOCK].
      + (* we're accessing arrblock *)

        subst.
        assert (ofs = Ptrofs.unsigned (nat_to_ptrofs wix1) \/
                ofs =  Ptrofs.unsigned (nat_to_ptrofs wix2) \/
                (ofs <>  Ptrofs.unsigned (nat_to_ptrofs wix1) /\
                 ofs <>  Ptrofs.unsigned (nat_to_ptrofs wix2))) as OFS_CASES.
        omega.

        destruct OFS_CASES as [OFS_EQ_WIX1 | [OFS_EQ_WIX2 | OFS_NEQ_BOTH]].

        ** (* ARRBLOCK, WIX1 ACCESS *)
          
          
          assert (M12: (ZMap.get
                          ofs
                          (Mem.mem_contents m12) # arrblock) =
                       Byte (Byte.repr (Int.unsigned (nat_to_int32 wval1)))).
          eapply mem_contents_offset_alias_for_sseq_1;
            try eauto; try eassumption.
          omega.

          
          assert (M21: (ZMap.get ofs (Mem.mem_contents m21) # arrblock) =
                       Byte (Byte.repr (Int.unsigned (nat_to_int32 wval1)))).
          eapply mem_contents_offset_alias_for_sseq_2
            with (wval2 := wval1) (wix2 := wix1)
                 (wval1 := wval2) (wix1 := wix2);
            try eauto; try eassumption.

          rewrite M12. rewrite M21.

          eapply memval_inject_refl;
            try eassumption; try auto.
          intros.
          congruence.

          
        ** (* ARRBLOCK, WIX2 ACCESS *)

          assert (M12: (ZMap.get
                          ofs
                          (Mem.mem_contents m12) # arrblock) =
                       Byte (Byte.repr (Int.unsigned (nat_to_int32 wval2)))).
          eapply mem_contents_offset_alias_for_sseq_2;
            try eauto; try eassumption.

          
          assert (M21: (ZMap.get ofs (Mem.mem_contents m21) # arrblock) =
                       Byte (Byte.repr (Int.unsigned (nat_to_int32 wval2)))).
          eapply mem_contents_offset_alias_for_sseq_1
            with (wval2 := wval1) (wix2 := wix1)
                 (wval1 := wval2) (wix1 := wix2);
            try eauto; try eassumption.
          omega.

          rewrite M12. rewrite M21.

          eapply memval_inject_refl;
            try eassumption; try auto.
          intros.
          congruence.

        **  (* ARRBLOCK, NO OFS ALIAS WITH WIX1 OR WIX2 *)
          intros.
          assert ((ZMap.get ofs (Mem.mem_contents m12) # arrblock) =
                  (ZMap.get ofs (Mem.mem_contents m) # arrblock))
            as M12_EQ_M.

          destruct OFS_NEQ_BOTH.
          eapply mem_contents_equal_no_offset_alias_for_sseq;
            try auto;
            try eassumption.

          
          assert ((ZMap.get ofs (Mem.mem_contents m21) # arrblock) =
                  (ZMap.get ofs (Mem.mem_contents m) # arrblock))
            as M21_EQ_M.

          destruct OFS_NEQ_BOTH.
          eapply mem_contents_equal_no_offset_alias_for_sseq;
            try auto;
            try eassumption.

          rewrite M12_EQ_M.
          rewrite M21_EQ_M.

          eapply memval_inject_refl; try eassumption; try eauto.
          
      + (* WE're NOT ACCESSING ARRBLOCK *)
         assert (M12_EQ_M: (Mem.mem_contents m12) #b2 =
                          (Mem.mem_contents m) # b2).
        eapply mem_contents_equal_no_block_alias_for_sseq;
          try eauto; try eassumption.

        
        assert (M21_EQ_M: (Mem.mem_contents m21) #b2 =
                          (Mem.mem_contents m) # b2).
        eapply mem_contents_equal_no_block_alias_for_sseq;
          try eauto; try eassumption.

        rewrite M12_EQ_M. rewrite M21_EQ_M.
        eapply memval_inject_refl; eauto; eassumption.

        + omega.
        +  congruence.
  Qed.
          
  
  Lemma meminject_m12_m21:
    Mem.inject injf m12 m21.
  Proof.
    constructor.
    - apply meminj_m12_m21_no_undef; eassumption.

    - intros.

      assert (B_INVALID_IN_M: ~Mem.valid_block m b).
      eapply sseq_invalid_block_2.
      exact s1VAL.
      exact s2VAL.
      auto.
      rewrite s12val in exec_s12.
      exact exec_s12.
      eassumption.
      eassumption.

      rewrite injfVAL.
      unfold Mem.flat_inj.

      destruct (plt b (Mem.nextblock m)); try contradiction; auto.

    - intros b b' delta INJF_AT_B.
      rewrite injfVAL in INJF_AT_B.
      unfold Mem.flat_inj in INJF_AT_B.
      destruct (plt b (Mem.nextblock m)); try congruence.
      inversion INJF_AT_B.
      subst.

      eapply sseq_valid_block; try eassumption; try auto.

    - rewrite injfVAL.
      (* TODO: READ THIS PROOF! *)
      apply Mem.flat_inj_no_overlap.

    - intros until ofs.
      intros INJF_AT_B.
      intros PERM.

      rewrite injfVAL in INJF_AT_B.
      unfold Mem.flat_inj in INJF_AT_B.

      
      destruct (plt b (Mem.nextblock m)); try congruence; auto.
      inversion INJF_AT_B.
      subst.

        rewrite Z.add_0_r.

        assert (UNSIGNED_RANGE: 0 <= Ptrofs.unsigned ofs < Ptrofs.modulus).
        apply Ptrofs.unsigned_range.
        assert (Ptrofs.modulus <= Ptrofs.max_unsigned + 1).
        unfold Ptrofs.max_unsigned.
        omega.
        omega.
    -  intros until p.
       intros INJF_AT_B1.
       intros PERM_m21.
       rewrite injfVAL in INJF_AT_B1.
       unfold Mem.flat_inj in INJF_AT_B1.
       destruct (plt b1 (Mem.nextblock m)); try congruence.
       inversion INJF_AT_B1.
       subst.
       replace (ofs + 0) with ofs in PERM_m21.
       left.

    (* transmit permissions like m21 -> m -> m12 *)
       assert (MPERM: Mem.perm m b2 ofs k p).
       eapply sseq_perm_2; try eassumption; try auto.
       eapply sseq_perm_1; try eassumption; try auto.

       omega.
       Qed.

End STMTINTERCHANGE.