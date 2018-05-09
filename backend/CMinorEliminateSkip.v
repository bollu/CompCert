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
Require Import Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Switch Cminor Selectionproof.
Require Import Errors.



Fixpoint remove_skip_from_seq_stmt(s: stmt) : stmt :=
  match s with
  | Sseq Sskip y =>
    remove_skip_from_seq_stmt y
  | Sseq x Sskip => remove_skip_from_seq_stmt x
  | _ => s
  end.

Definition replace_fn_body (fn: Cminor.function) (b: stmt): Cminor.function :=
  {|
    fn_sig := fn_sig fn;
    fn_params := fn_params fn;
    fn_vars := fn_vars fn;
    fn_stackspace := fn_stackspace fn;
    fn_body := b;
  |}.

Definition transf_fn(fn : Cminor.function): Cminor.function :=
  replace_fn_body fn (remove_skip_from_seq_stmt (fn_body fn)).
  

Definition transf_fundef (fd: Cminor.fundef) : Cminor.fundef :=
  AST.transf_fundef transf_fn fd.

Definition transf_program (p: Cminor.program): Cminor.program :=
  AST.transform_program transf_fundef p.


(* as seen from tailcallproof *)
(* I chose tailcallproof to imitate since it is referred to from the paper:
 https://people.mpi-sws.org/~viktor/papers/sepcompcert.pdf
as a "trivial pass"
*)
(* 
Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.
*)
Check (AST.transf_partial_fundef).

Definition match_prog (p tp: Cminor.program) :=
  Linking.match_program
    (fun cu f tf =>  tf = transf_fundef f)
    Coq.Init.Logic.eq
    p
    tp.

Theorem transf_program_match:
  forall p tp, transf_program p =  tp -> match_prog p tp.
Proof.
  intros.
  inversion H.
Admitted.
  
Theorem transf_program_correct: forall (p p': Cminor.program),
    match_prog p p' ->
    forward_simulation (Cminor.semantics p) (Cminor.semantics p').
Proof.
  intros.
Admitted.
