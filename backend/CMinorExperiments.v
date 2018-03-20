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

Definition STORE_CHUNK_SIZE: memory_chunk := Mint8unsigned.

Definition arrofs_expr (arrname: ident) (ofs: nat) : expr :=
    Econst (Oaddrsymbol arrname (nat_to_ptrofs ofs)).

(* a handy alias for storing 1 byte value *)
Definition SstoreValAt (arrname: ident) (v: nat) (ix: nat) :=
  Cminor.Sstore STORE_CHUNK_SIZE (arrofs_expr arrname ix)
                (nat_to_expr v).


(* We need this so we don't have to reason about fucking pointers to pointers
and whatnot *)
Definition mem_no_pointers (m: mem) : Prop :=
  forall bptr i q n b ofs,
  Fragment (Vptr bptr i) q n <> ZMap.get ofs (Mem.mem_contents m) # b.

Section MEMSTORE.

  Variable m m': mem.
  Variable NOPOINTERS: mem_no_pointers m.

  Variable wb: block.
  Variable rb: block.

  Variable wchunk: memory_chunk.
  Variable wofs: Z.
  Variable wv: val.


  Variable MSTORE: Mem.store wchunk m wb wofs wv = Some m'.

  Variable injf: meminj.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock m).


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
                                 (Mem.setN (encode_val wchunk wv) wofs
                                           m.(Mem.mem_contents)# wb)
                                 m.(Mem.mem_contents)).
  apply Mem.store_mem_contents. assumption.


  assert (M'CONTENTSEQ: (Mem.mem_contents m') # rb = (Mem.mem_contents m)# rb).
  rewrite M'CONTENTS.
  apply PMap.gso.
  auto.

  rewrite M'CONTENTSEQ.

  (* memval_inject *)
  remember (ZMap.get ofs (Mem.mem_contents m) # rb) as mval.
  destruct mval; try constructor.

  (* val inject *)
  destruct v; try constructor.
  (* pointer injection *)
  unfold mem_no_pointers in NOPOINTERS.
  specialize (NOPOINTERS b i q n rb ofs).
  contradiction.
Qed.

End MEMSTORE.

Section STMT.
  Variable m m': mem.
  Variable NOPOINTERS : mem_no_pointers m.
  
    
  Variable arrname: ident.
  Variable wix: nat.
  Variable wval: nat.

  Definition s: Cminor.stmt := SstoreValAt arrname wval wix.

  
  Variable ge: genv.
  Variable f: function.
  Variable sp: val.
  Variable e e': env.
  Variable EXECS: exec_stmt ge f sp e m s E0 e' m' Out_normal.


  Variable injf: meminj.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock m).

  Variable wb: block.
  Variable wofs: ptrofs.
  (* the array offset has a concrete value,
   which is the pointer wb with offset wofs *)
  Variable WBVAL: eval_expr ge sp e m (arrofs_expr arrname wix) (Vptr wb wofs).
  
  Lemma memval_inject_store_no_alias_for_stmt:
    forall rb,
      rb <> wb ->
      memval_inject injf
                    (ZMap.get (Ptrofs.unsigned wofs) (Mem.mem_contents m) # rb)
                    (ZMap.get (Ptrofs.unsigned wofs) (Mem.mem_contents m') # rb).
  Proof.
    intros until rb.
    intros NOALIAS.
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
End STMT.

Section STMTSEQ.
  Variable m m': mem.
  Variable arrname: ident.

  Variable wix1 wix2 : nat.
  Variable wval1 wval2: nat.


  
  (* a[wix1] = wval1] *)
  Definition s1: Cminor.stmt := SstoreValAt arrname wval1 wix1.

  (* a[wix2] = wval2 *)
  Definition s2: Cminor.stmt :=  SstoreValAt arrname wval2 wix2.

  Definition s12 : Cminor.stmt := Sseq s1 s2.

  Variable ge: genv.
  Variable f: function.
  Variable sp: val.
  Variable e e': env.
  Variable EXECS12: exec_stmt ge f sp e m s12 E0 e' m' Out_normal.
  
  Variable injf: meminj.
  Variable INJF_FLAT_INJ: injf =  Mem.flat_inj (Mem.nextblock m).


End STMTSEQ.

  
Section STMTINTERCHANGE.
  Variable ma mb ma' mb': mem.
  
  Variable arrname: ident.
  Definition STORE_CHUNK_SIZE: memory_chunk := Mint8unsigned.

  Definition nat_to_expr (n: nat) : expr :=
    Econst (Ointconst (Int.repr (Z.of_nat n))).
  Definition nat_to_ptrofs (n: nat) : ptrofs :=
    Ptrofs.repr (Z.of_nat n).
  Definition arrofs_expr(ofs: nat) : expr :=
    Econst (Oaddrsymbol arrname (nat_to_ptrofs ofs)).
  

  
  (* a[0] = 1*)
  Definition s1: Cminor.stmt :=
    Cminor.Sstore STORE_CHUNK_SIZE (arrofs_expr 0)
                  (nat_to_expr 1).

  (* a[1] = 2 *)
  Definition s2: Cminor.stmt :=
    Cminor.Sstore STORE_CHUNK_SIZE (arrofs_expr 1)
                  (nat_to_expr 2).


  Definition s12: Cminor.stmt := Cminor.Sseq s1 s2.
  Definition s21: Cminor.stmt := Cminor.Sseq s2 s1.

  Definition injf : meminj := Mem.flat_inj (Mem.nextblock ma).
  Variable begininj: Mem.inject injf ma mb.


  Variable ge: genv.
  Variable f: function.
  Variable sp: val.
  Variable e e': env.
  Variable exec_s12: exec_stmt ge f sp  e ma s12 E0 e' ma' Out_normal.
  Variable exec_s21: exec_stmt ge f sp  e mb s21 E0 e' mb' Out_normal.

  Variable arrbase : block.

  Variable GENV_AT_ARR: Genv.find_symbol ge arrname = Some arrbase.

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
    forall f ge sp  e e' m m',
    forall chunk addr a,
      exec_stmt ge f sp e m
                (Sstore chunk addr a)
                E0 e' m' Out_normal ->
      mem_structure_eq injf m m'.
  Proof.
    unfold injf.
    intros until a.
    intros execs.
    inversion execs; subst.

    rename H10 into store.
    unfold Mem.storev in store.
    destruct vaddr; try inversion store.


    constructor.
    - intros until p.
      intros inj.
      intros perm_m.

      unfold Mem.flat_inj in inj.
      destruct (plt b1 (Mem.nextblock ma)); inversion inj; subst.
      replace (ofs + 0) with ofs.

      eapply Mem.perm_store_1; try eassumption.
      omega.
    - intros until p.
      intros inj.
      intros range_perm_m.
      
      
      unfold Mem.flat_inj in inj.
      destruct (plt b1 (Mem.nextblock ma)); inversion inj; subst.

      exists 0.
      omega.
  Qed.

  
  Lemma mem_structure_eq_store_sym:
    forall m1 m2,
    forall chunk b ofs v,
      mem_structure_eq injf m1 m2  ->
      Mem.store chunk m1 b ofs v = Some m2 ->
      mem_structure_eq injf m2 m1.
  Proof.
    intros until v.
    intros eq_m1_m2.
    intros m2_as_store_m1.

    
    inversion eq_m1_m2.
    constructor.
    - intros until p.
      intros inj_b1.
      unfold injf in inj_b1.
      unfold Mem.flat_inj in inj_b1.
      destruct (plt b1 (Mem.nextblock ma));  inversion inj_b1.

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
      unfold injf in inj_b1.
      unfold Mem.flat_inj in inj_b1.
      destruct (plt b1 (Mem.nextblock ma));  inversion inj_b1.
      subst.
      intros range_perm.
      exists 0.
      omega.
  Qed.
      

  Lemma mem_structure_eq_trans:
    forall m1 m2 m3, mem_structure_eq injf m1 m2  ->
                 mem_structure_eq injf m2 m3 ->
                 mem_structure_eq injf m1 m3.
  Proof.
    intros until m3.
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
      unfold injf in *.
      unfold Mem.flat_inj in *.
      destruct (plt b1 (Mem.nextblock ma));
        inversion inj_b1.
      reflexivity.
      eassumption.
      omega.

    - intros until p.
      intros inj_b1.
      intros perm.
      exists 0.
      unfold injf in inj_b1.
      unfold Mem.flat_inj in inj_b1.
      destruct (plt b1 (Mem.nextblock ma)); inversion inj_b1; try omega.
  Qed.

  Lemma mem_structure_eq_ma_ma':
    mem_structure_eq injf ma ma'.
      inversion exec_s12; subst; try contradiction.
      assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
      apply destruct_trace_app_eq_E0. assumption.
      destruct t1_t2_E0.
      subst.

      assert (mem_structure_eq injf ma m1) as eq_ma_m1.
      + eapply mem_structure_eq_store.

      unfold s1 in *.
      eassumption.

      + assert (mem_structure_eq injf m1 ma') as eq_m1_ma'.
      eapply mem_structure_eq_store.
      unfold s2 in *.
      eassumption.


      eapply mem_structure_eq_trans; eassumption.
      Qed.

  
  Lemma mem_structure_eq_mb_mb':
    mem_structure_eq injf mb mb'.
    inversion exec_s21; subst; try contradiction.
    assert (t1 = E0 /\ t2 = E0) as t1_t2_E0.
    apply destruct_trace_app_eq_E0. assumption.
    destruct t1_t2_E0.
    subst.

    assert (mem_structure_eq injf mb m1) as eq_ma_m1.
    + eapply mem_structure_eq_store.

      unfold s2 in *.
      eassumption.

    + assert (mem_structure_eq injf m1 mb') as eq_m1_ma'.
      eapply mem_structure_eq_store.
      unfold s2 in *.
      eassumption.


      eapply mem_structure_eq_trans; eassumption.
  Qed.

  Lemma mem_structure_eq_ma'_ma:
    mem_structure_eq injf ma' ma.
    constructor.

    - intros until p.
      unfold injf.
      unfold Mem.flat_inj.

      intros b2_as_b1.

      destruct (plt b1 (Mem.nextblock ma)); inversion b2_as_b1; subst.
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

      
      assert (Mem.perm ma b2 ofs k p) as MA_PERM.
      eapply Mem.perm_store_2; eassumption.

      replace (ofs + 0) with ofs.
      assumption.
      omega.


    - (* second theorem *)
      intros until p.
      intros INJF_B1_B2.
      intros RANGE_PERM.
      unfold injf in INJF_B1_B2.
      unfold Mem.flat_inj in INJF_B1_B2.
      destruct (plt b1 (Mem.nextblock ma)); inversion INJF_B1_B2; subst.
      exists 0. omega.
      Qed.

  Lemma mem_structure_eq_ma'_mb':
    mem_structure_eq injf ma' mb'.
    assert (mem_structure_eq injf ma mb) as structure_eq_begin.
    eapply mem_inj_mem_structure_eq. inversion begininj. eassumption.


    eapply mem_structure_eq_trans with (m2 := mb).
    eapply mem_structure_eq_trans with (m2 := ma).
    eapply mem_structure_eq_ma'_ma.
    assumption.
    eapply mem_structure_eq_mb_mb'.
  Qed.

      

    
   
  Lemma meminj_ma'_mb': Mem.mem_inj injf ma' mb'.
  Proof.

    assert (mem_structure_eq injf ma' mb') as structureeq.
    apply mem_structure_eq_ma'_mb'.

    inversion structureeq.

    
    constructor.
    - intros.
    eapply mseq_perm0; eassumption.

    - (* permission *)
      intros.
      eapply mseq_align0; eassumption.

    - (* content matching, the difficult part *)
      intros until delta.
      intros injf_b1.
      intros ma'_readable.
      unfold injf in injf_b1.
      unfold Mem.flat_inj in injf_b1.
      destruct (plt b1 (Mem.nextblock ma)); try contradiction.
      inversion injf_b1.
      subst.

      
      replace (ofs + 0) with ofs.
  Admitted.

  Theorem flip_valid: Mem.inject injf ma' mb'.
  Proof.
    
  Abort.
  

  
End STMTINTERCHANGE.