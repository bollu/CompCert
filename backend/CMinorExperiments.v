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

  Variable injf : Val.meminj.
  Variable begininj: Mem.inject injf ma mb.


  Variable ge: genv.
  Variable f: function.
  Variable sp: val.
  Variable e e': env.
  Variable exec_s12: exec_stmt ge f sp  e ma s12 E0 e' ma' Out_normal.
  Variable exec_s21: exec_stmt ge f sp  e ma s21 E0 e' mb' Out_normal.

  Lemma meminj_new: Mem.mem_inj injf ma' mb'.
  Proof.
    constructor.
  Abort.

  Theorem flip_valid: Mem.inject injf ma' mb'.
  Proof.
  Abort.
  

  
End STMTINTERCHANGE.