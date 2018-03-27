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

Definition nat_to_int64 (n: nat): int64 := (Int64.repr (Z.of_nat n)).
Definition nat_to_ptrofs (n: nat): ptrofs := (Ptrofs.repr (Z.of_nat n)).
Definition nat_to_expr(n: nat): expr := Econst (Olongconst (nat_to_int64 n)).

Check (nat_to_ptrofs).
Definition STORE_CHUNK_SIZE: memory_chunk := Mint8unsigned.

Definition arrofs_expr (arrname: ident) (ofs: nat) : expr :=
  Econst (Oaddrsymbol arrname (nat_to_ptrofs ofs)).

(* a handy alias for storing 1 byte value *)
Definition SstoreValAt (arrname: ident) (v: nat) (ix: nat) :=
  Cminor.Sstore STORE_CHUNK_SIZE (arrofs_expr arrname ix)
                (nat_to_expr v).
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


(* We need this so we don't have to reason about fucking pointers to pointers
and whatnot *)
Definition mem_no_pointers (m: mem) : Prop :=
  forall bptr i q n b ofs,
    Fragment (Vptr bptr i) q n <> ZMap.get ofs (Mem.mem_contents m) # b.

Definition mem_no_undef (m: mem) : Prop :=
  forall b ofs,
    Undef <> ZMap.get ofs (Mem.mem_contents m) # b.

Definition mem_no_undef_fragment (m: mem) : Prop :=
  forall b ofs q n,
    Fragment (Vundef) q n <> ZMap.get ofs (Mem.mem_contents m) # b.

Definition val_no_pointer (v: val) : Prop :=
  forall bptr i, v <> Vptr bptr i.

(* If we have a mem_inj, then we can continue to claim that memory does not
contain pointers *)
(* This was so fucking painful, to reason about the case of Get (SetN (encode...)).
I will probably need to extract that case out *)
Lemma mem_no_pointers_forward_on_storev:
  forall (m m': mem) (addr v : val),
    val_no_pointer v ->
    mem_no_pointers m ->
    Mem.storev STORE_CHUNK_SIZE m addr v = Some m' ->
    mem_no_pointers m'.
Proof.
  intros until v.
  intros V_NO_POINTER.
  intros M_NO_POINTERS.
  intros M'_AS_STORE_M.
  unfold mem_no_pointers in *.
  intros until ofs.
  unfold Mem.storev in M'_AS_STORE_M.

  induction addr; try congruence.

  erewrite Mem.store_mem_contents with (m1 := m)
                                       (chunk := STORE_CHUNK_SIZE)
                                       (ofs := (Ptrofs.unsigned i0))
                                       (b := b0)
                                       (v := v).
  assert ({b = b0} + {b <> b0}) as BCASES.
  apply Pos.eq_dec.

 
 destruct BCASES as [BEQ | BNEQ].
  + subst.
    rewrite PMap.gss.
    assert ({ofs = Ptrofs.unsigned i0} +  {ofs <> Ptrofs.unsigned i0}) as
        ofs_cases.
    apply Z.eq_dec.

    destruct ofs_cases as [OFSEQ | OFSNEQ].
    * subst.
      remember (Ptrofs.unsigned i0) as i0ofs.

      (* we are reading and writing from the same block at the same offset.
         Convince the damn proof system that we cannot have a fragment by
       analysing such a load.

       We cannot have a fragment ptr since we same V_NO_PTR*)
      remember (ZMap.get i0ofs (Mem.setN (encode_val STORE_CHUNK_SIZE v)
                               i0ofs (Mem.mem_contents m) # b0)) as MNEW.

      assert (ENCODEV: Some MNEW = List.hd_error (encode_val Mint8unsigned v)).
      rewrite HeqMNEW.
      erewrite Mem.get_setN_at_base_chunk_Mint8unsigned;
        try auto;
        try eassumption.

      induction v;
        simpl in *;
        inversion ENCODEV;
        simpl in *;
        try congruence.

         unfold inj_bytes.
         unfold encode_int.
         unfold rev_if_be.
         simpl in *.
         destruct (Archi.big_endian); simpl; congruence.
      
    * rewrite Mem.setN_outside.
      apply M_NO_POINTERS.
      rewrite encode_val_length.
      simpl.
      apply integer_split_number_line.
      eassumption.
      
    
  + rewrite PMap.gso.
    apply M_NO_POINTERS.
    auto.

  + auto.
 Qed.

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


  (* Note that this is NOT TRUE!
  We can inject a Vundef into whatever we want *)
  Lemma memval_inject_trans:
    forall (ofs: Z) (rb: block) (m1 m2 m3: mem),
      mem_no_pointers m1 ->
      mem_no_undef m1 ->
      memval_inject injf (ZMap.get ofs (Mem.mem_contents m1) # rb)
                    (ZMap.get ofs (Mem.mem_contents m2) # rb) ->
      memval_inject injf (ZMap.get ofs (Mem.mem_contents m2) # rb)
                    (ZMap.get ofs (Mem.mem_contents m3) # rb) ->
      memval_inject injf (ZMap.get ofs (Mem.mem_contents m1) # rb)
                    (ZMap.get ofs (Mem.mem_contents m3) # rb).
  Proof.
    intros until m3.
    intros NOPOINTERS.
    intros NOUNDEF.
    intros INJ_M1_M2.
    intros INJ_M2_M3.
    remember (ZMap.get ofs (Mem.mem_contents m1) # rb) as M1_AT_RB.

    induction M1_AT_RB.
    - unfold mem_no_undef in NOUNDEF. congruence.

    - inversion INJ_M1_M2; subst;
        inversion INJ_M2_M3; subst; try congruence.
    - inversion INJ_M1_M2; subst;
        inversion INJ_M2_M3; subst; try congruence.

      assert (Fragment v2 q n = Fragment v1 q0 n0) as FRAG_EQ.
      rewrite H3. rewrite H.
      reflexivity.

      inv FRAG_EQ.
      apply memval_inject_frag.
      eapply val_inject_trans; try eassumption.
      auto.
  Qed.

  
  Lemma memval_inject_sym:
    forall (ofs: Z) (rb: block) (m1 m2: mem),
      mem_no_pointers m1 ->
      mem_no_undef m1 ->
      mem_no_undef_fragment m1 ->
      memval_inject injf (ZMap.get ofs (Mem.mem_contents m1) # rb)
                    (ZMap.get ofs (Mem.mem_contents m2) # rb) ->
      memval_inject injf (ZMap.get ofs (Mem.mem_contents m2) # rb)
                    (ZMap.get ofs (Mem.mem_contents m1) # rb).
  Proof.
    intros until m2.
    intros NOPOINTERS.
    intros NOUNDEF.
    intros NOUNDEFFRAG.
    intros INJ_M1_M2.
    remember (ZMap.get ofs (Mem.mem_contents m1) # rb) as M1_AT_RB.

    induction M1_AT_RB.
    - unfold mem_no_undef in NOUNDEF. congruence.
    - inversion INJ_M1_M2; subst;try congruence.
    - inversion INJ_M1_M2; subst;try congruence.
      apply memval_inject_frag.
      induction v2; inversion H0; subst;
        try(unfold mem_no_undef_fragment in NOUNDEFFRAG;
        specialize (NOUNDEFFRAG rb ofs q n);
        congruence).

      rename H4 into MEM_INJ_B1.
      unfold Mem.flat_inj in MEM_INJ_B1.
      destruct (plt b1 (Mem.nextblock ma)); try congruence.
      inversion MEM_INJ_B1.
      subst.
      replace (Ptrofs.add ofs1 (Ptrofs.repr 0)) with ofs1.
      eapply Val.inject_ptr.
      unfold Mem.flat_inj.
      destruct (plt b (Mem.nextblock ma)); try congruence; try auto.
      rewrite Ptrofs.add_zero. auto.
      rewrite Ptrofs.add_zero. auto.
  Qed.


    
End MEMVAL_INJECT.

Section MEMSTORE.

  Variable m m': mem.
  Variable NOPOINTERS: mem_no_pointers m.

  Variable wb: block.
  Variable rb: block.

  Variable wofs: Z.
  Variable wv: val.


  Variable MSTORE: Mem.store STORE_CHUNK_SIZE m wb wofs wv = Some m'.

  Variable ma: mem.
  Variable injf: meminj.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock ma).


  Lemma memval_inject_store_no_alias:
    forall ofs,
      wb <> rb -> 
      memval_inject injf (ZMap.get ofs (Mem.mem_contents m) # rb)
                    (ZMap.get ofs (Mem.mem_contents m') # rb).
  Proof.
    intros until ofs.
    intros NOALIAS.

    assert (M'CONTENTS: Mem.mem_contents m' =
                        PMap.set wb
                                 (Mem.setN (encode_val STORE_CHUNK_SIZE wv) wofs
                                           m.(Mem.mem_contents)# wb)
                                 m.(Mem.mem_contents)).
    apply Mem.store_mem_contents. assumption.


    assert (M'CONTENTSEQ: (Mem.mem_contents m') # rb = (Mem.mem_contents m)# rb).
    rewrite M'CONTENTS.
    apply PMap.gso.
    auto.

    rewrite M'CONTENTSEQ.

    apply memval_inject_refl.
    intros.

    assert (M_AT_RB_CASES: {ZMap.get ofs (Mem.mem_contents m) # rb = Fragment (Vptr b ptrofs) q n} +
            {ZMap.get ofs (Mem.mem_contents m) # rb <> Fragment (Vptr b ptrofs) q n}).
    apply memval_eq_dec.
    destruct M_AT_RB_CASES as [M_AT_RB_FRAG | M_AT_RB_NOT_FRAG].
    unfold mem_no_pointers in NOPOINTERS.
    (* M at frag *)
    specialize (NOPOINTERS b ptrofs q n rb ofs).
    congruence.
    auto.

  Qed.

  
  Lemma memval_inject_store_no_alias_same_block:
        forall ofs,
          ofs <> wofs ->
      memval_inject injf (ZMap.get ofs (Mem.mem_contents m) # wb)
                    (ZMap.get ofs (Mem.mem_contents m') # wb).
  Proof.
    intros until ofs.
    intros NOALIASOFS.

    assert (M'CONTENTS: Mem.mem_contents m' =
                        PMap.set wb
                                 (Mem.setN (encode_val STORE_CHUNK_SIZE wv) wofs
                                           m.(Mem.mem_contents)# wb)
                                 m.(Mem.mem_contents)).
    apply Mem.store_mem_contents. assumption.



    assert (M'CONTENTSEQ: (Mem.mem_contents m') # wb =
            Mem.setN (encode_val STORE_CHUNK_SIZE wv) wofs m.(Mem.mem_contents) # wb).
    rewrite M'CONTENTS.
    apply PMap.gss.

    rewrite M'CONTENTSEQ.

    (* memval_inject *)
    remember (ZMap.get ofs (Mem.mem_contents m') # wb) as mval.
    remember (encode_val STORE_CHUNK_SIZE wv) as WVENC.
    
    assert (M'_AT_OFS: ZMap.get ofs (Mem.setN WVENC wofs (Mem.mem_contents m) # wb) =
            ZMap.get ofs (Mem.mem_contents m) # wb).
    apply Mem.setN_outside.
    rewrite HeqWVENC.
    rewrite Memdata.encode_val_length.
    simpl.
    omega.

    rewrite M'_AT_OFS.

    
    apply memval_inject_refl.
    intros.
    assert (M_AT_RB_CASES: {ZMap.get ofs (Mem.mem_contents m) # rb = Fragment (Vptr b ptrofs) q n} +
            {ZMap.get ofs (Mem.mem_contents m) # rb <> Fragment (Vptr b ptrofs) q n}).
    apply memval_eq_dec.
    destruct M_AT_RB_CASES as [M_AT_RB_FRAG | M_AT_RB_NOT_FRAG].
    unfold mem_no_pointers in NOPOINTERS.
    (* M at frag *)
    specialize (NOPOINTERS b ptrofs q n rb ofs).
    congruence.
    auto.
  Qed.
  

End MEMSTORE.

Section STMT.
  Variable m m': mem.
  Variable NOPOINTERS : mem_no_pointers m.
  
  
  Variable arrname: ident.
  Variable wix: nat.
  Variable wval: nat.

  Variable s: Cminor.stmt.
  Variable sVAL: s= SstoreValAt arrname wval wix.

  
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

  Lemma memval_inject_store_no_alias_for_sstore:
    forall rb ofs,
      rb <> wb ->
      memval_inject injf
                    (ZMap.get ofs (Mem.mem_contents m) # rb)
                    (ZMap.get ofs (Mem.mem_contents m') # rb).
  Proof.
    intros until ofs.
    intros NOALIAS.

    rewrite sVAL in EXECS.
    inversion EXECS. subst.

    assert (vaddr = Vptr wb wofs) as VADDR_EQ_WBVAL.
    eapply eval_expr_is_function; eassumption.
    subst.

    rename H10 into STOREM.
    unfold Mem.storev in STOREM.
    
    eapply memval_inject_store_no_alias;
      try eassumption.
    auto.
  Qed.

  
  Lemma memval_inject_store_no_alias_for_sstore_same_block:
    forall ofs,
      ofs <> Ptrofs.unsigned wofs ->
      memval_inject injf
                    (ZMap.get ofs (Mem.mem_contents m) # wb)
                    (ZMap.get ofs (Mem.mem_contents m') # wb).
  Proof.
    intros until ofs.
    intros NOALIASWIX.

    rewrite sVAL in EXECS.
    inversion EXECS. subst.

    assert (vaddr = Vptr wb wofs) as VADDR_EQ_WBVAL.
    eapply eval_expr_is_function; eassumption.
    subst.

    rename H10 into STOREM.
    unfold Mem.storev in STOREM.
    
    eapply memval_inject_store_no_alias_same_block;
      try eassumption.
  Qed.

  Lemma mem_no_pointers_forward_on_sstore:
    mem_no_pointers m'.
  Proof.
    rewrite sVAL in EXECS.
    inversion EXECS. subst.

    
    assert (VNOPTR: val_no_pointer v).
    rename H7 into EVALV.
    inversion EVALV. subst.
    rename H0 into EVAL_CONSTANT_V.
    simpl in EVAL_CONSTANT_V.
    inversion EVAL_CONSTANT_V.
    unfold val_no_pointer.
    intros. congruence.

    eapply mem_no_pointers_forward_on_storev; eassumption.
  Qed.


  
End STMT.

Section STMTSEQ.
  Variable m m': mem.
  Variable NOPOINTERS: mem_no_pointers m.
  Variable NOUNDEF: mem_no_undef m.
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

  Lemma memval_inject_store_no_alias_for_sseq:
    forall rb ofs,
      rb <> arrblock ->
      memval_inject injf
                    (ZMap.get ofs (Mem.mem_contents m) # rb)
                    (ZMap.get ofs (Mem.mem_contents m') # rb).
  Proof.
    intros until ofs.
    intros NOALIAS_RB_ARRBLOCK.
    (* intros NOALIAS_WB1.
    intros NOALIAS_WB2.
     *)
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

    assert (memval_inject (Mem.flat_inj (Mem.nextblock ma))
                          (ZMap.get ofs (Mem.mem_contents m) # rb)
                          (ZMap.get ofs (Mem.mem_contents m1) # rb))
      as INJ_M_M1.
    eapply memval_inject_store_no_alias_for_sstore with
        (arrname := arrname)
        (wix := wix1)
        (wval := wval1); try eassumption; try auto.
    eapply eval_expr_arrofs. eassumption.

    
    assert (memval_inject (Mem.flat_inj (Mem.nextblock ma))
                          (ZMap.get ofs (Mem.mem_contents m1) # rb)
                          (ZMap.get ofs (Mem.mem_contents m') # rb))
      as INJ_M1_M'.
    eapply memval_inject_store_no_alias_for_sstore with
        (arrname := arrname)
        (wix := wix2)
        (wval := wval2); try eassumption; try auto.

    inversion EXECS2. subst.
    inversion EXECS1. subst.
    eapply mem_no_pointers_forward_on_storev with (m := m) (m' := m1) (v := v0).

    assert (val_no_pointer v0) as V0_NO_PTR.
    unfold val_no_pointer.
    intros.
    rename H10 into eval_v0.
    inversion eval_v0. subst.
    rename H0 into eval_v0_const.
    simpl in eval_v0_const.
    inversion eval_v0_const.
    congruence.

    apply V0_NO_PTR.
    eassumption.
    exact H14.
    eapply eval_expr_arrofs. eassumption.

    eapply memval_inject_trans; try eassumption.
    auto.
  Qed.

  
  Lemma memval_inject_store_no_alias_for_sseq_same_block:
    forall ofs,
      ofs <> Ptrofs.unsigned (nat_to_ptrofs wix1) ->
      ofs <> Ptrofs.unsigned (nat_to_ptrofs wix2) ->
      memval_inject injf
                    (ZMap.get ofs (Mem.mem_contents m) # arrblock)
                    (ZMap.get ofs (Mem.mem_contents m') # arrblock).
  Proof.
    intros until ofs.
    intros NOALIAS_WIX1 NOALIAS_WIX2.

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

    assert (memval_inject (Mem.flat_inj (Mem.nextblock ma))
                          (ZMap.get ofs (Mem.mem_contents m) # arrblock)
                          (ZMap.get ofs (Mem.mem_contents m1) # arrblock))
      as INJ_M_M1.
    eapply memval_inject_store_no_alias_for_sstore_same_block with
        (arrname := arrname)
        (wix := wix1)
        (wval := wval1).
    eassumption. auto. eassumption. auto. 
    eapply eval_expr_arrofs; eassumption.
    eassumption.

    
    assert (memval_inject (Mem.flat_inj (Mem.nextblock ma))
                          (ZMap.get ofs (Mem.mem_contents m1) # arrblock)
                          (ZMap.get ofs (Mem.mem_contents m') # arrblock))
      as INJ_M1_M'.
    eapply memval_inject_store_no_alias_for_sstore_same_block with
        (arrname := arrname)
        (wix := wix2)
        (wval := wval2); try eassumption; try auto.

    inversion EXECS2. subst.
    inversion EXECS1. subst.
    eapply mem_no_pointers_forward_on_storev with (m := m) (m' := m1) (v := v0).

    assert (val_no_pointer v0) as V0_NO_PTR.
    unfold val_no_pointer.
    intros.
    rename H10 into eval_v0.
    inversion eval_v0. subst.
    rename H0 into eval_v0_const.
    simpl in eval_v0_const.
    inversion eval_v0_const.
    congruence.

    apply V0_NO_PTR.
    eassumption.
    exact H14.
    eapply eval_expr_arrofs. eassumption.

    eapply memval_inject_trans; try eassumption.
    auto.
  Qed.

  
  Lemma mem_no_pointers_forward_on_sseq:
    mem_no_pointers m'.
  Proof.
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

    assert (M1_NO_POINTERS: mem_no_pointers m1).
    inversion EXECS1. subst.
    eapply mem_no_pointers_forward_on_sstore; try eassumption; try auto.
    apply eval_expr_arrofs. eassumption.

    assert (M'_NO_POINTERS: mem_no_pointers m').
    inversion  EXECS2. subst.
    eapply mem_no_pointers_forward_on_sstore; try eassumption; try auto.
    apply eval_expr_arrofs. eassumption.

    assumption.
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
  Variable NOUNDEFM: mem_no_undef m.
  Variable NOUNDEFFRAGMENT: mem_no_undef_fragment m.
  
  Variable arrname: ident.

  Variable wval1 wval2: nat.
  Variable wix1 wix2: nat.
  Variable WIX_NOALIAS: wix1 <> wix2.

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

  
  Lemma meminj_ma'_mb': Mem.mem_inj injf m12 m21.
  Proof.
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

        ** (* arrblock, wix1 access *)
          admit.

        ** (* arrblock, wix2 access *)
          admit.
        ** (* arrblock, neither wix access *)
          destruct OFS_NEQ_BOTH as [OFS_NEQ_WIX1 OFS_NEQ_WIX2].
        assert (memval_inject (Mem.flat_inj (Mem.nextblock m))
                              (ZMap.get ofs (Mem.mem_contents m) # arrblock)
                              (ZMap.get ofs (Mem.mem_contents m12) # arrblock))
          as MEMVALINJ_m_m12.
        eapply memval_inject_store_no_alias_for_sseq_same_block; try auto; try eassumption.

        
        assert (memval_inject (Mem.flat_inj (Mem.nextblock m))
                              (ZMap.get ofs (Mem.mem_contents m) # arrblock)
                              (ZMap.get ofs (Mem.mem_contents m21) # arrblock))
          as MEMVALINJ_m_m21.
        eapply memval_inject_store_no_alias_for_sseq_same_block; try auto; try eassumption.

        assert (memval_inject (Mem.flat_inj (Mem.nextblock m))
                              (ZMap.get ofs (Mem.mem_contents m12) # arrblock)
                              (ZMap.get ofs (Mem.mem_contents m) # arrblock))
          as MEMVALINJ_m12_m.
        eapply memval_inject_sym; try eassumption; try auto.

        
        eapply memval_inject_trans; try eassumption; try auto.
        admit. admit.
          
      + (* we're not accessing ARRBLOCK *)
        assert (memval_inject (Mem.flat_inj (Mem.nextblock m))
                              (ZMap.get ofs (Mem.mem_contents m) # b2)
                              (ZMap.get ofs (Mem.mem_contents m12) # b2))
          as MEMVALINJ_m_m12.
        eapply memval_inject_store_no_alias_for_sseq; try auto; try eassumption.

        
        assert (memval_inject (Mem.flat_inj (Mem.nextblock m))
                              (ZMap.get ofs (Mem.mem_contents m) # b2)
                              (ZMap.get ofs (Mem.mem_contents m21) # b2))
          as MEMVALINJ_m_m21.
        eapply memval_inject_store_no_alias_for_sseq; try auto; try eassumption.


        
        
  Admitted.
  
  Lemma meminject_ma'_mb': Mem.inject injf m12 m21.
  Proof.
    constructor.

    assert (Mem.inject injf m12 m21) as INJECT_M12_M21.
    admit.
    
    - apply INJECT_M12_M21.
    - intros b bINVALID_M12.
      rewrite injfVAL.
      admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

End STMTINTERCHANGE.