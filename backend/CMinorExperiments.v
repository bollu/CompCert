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
  Variable exec_s21: exec_stmt ge f sp  e ma s21 E0 e' mb' Out_normal.

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
      unfold injf.
      unfold Mem.flat_inj.
      destruct (plt b1 (Mem.nextblock ma)).
      reflexivity.
      admit.
      eassumption.
      omega.

    - intros until p.
      intros inj_b1.
      intros perm.
      exists 0.
      unfold injf in inj_b1.
      unfold Mem.flat_inj in inj_b1.
      destruct (plt b1 (Mem.nextblock ma)); inversion inj_b1; try omega.
  Admitted.


             







      

  

  Lemma meminj_new: Mem.mem_inj injf ma' mb'.
  Proof.
    constructor.
    intros.

    - (* permission *)
  Abort.

  Theorem flip_valid: Mem.inject injf ma' mb'.
  Proof.
  Abort.
  

  
End STMTINTERCHANGE.