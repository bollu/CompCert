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
Require Import CMinorExperiments.
Require Import Errors.



Fixpoint measure_stmt (s: stmt):nat  :=
  match s with
  | Sskip => 1
  | _ => 0
  end.


Fixpoint measure_cont(c: Cminor.cont): nat :=
  match c with
  | Kseq s k => measure_stmt s + measure_cont k 
  | Kblock k =>  measure_cont k + 1
  | _ => 1
  end.

Lemma measure_of_block_decreases:
  forall (k: cont), (measure_cont k  < measure_cont (Kblock k))%nat.
Proof.
  intros.
  induction k; simpl; try omega.
Qed.

  


Fixpoint measure_state(st: Cminor.state) : nat :=
  match st with
  |  State f s k sp e m => measure_stmt s + measure_cont k 
  | _ => 0
  end.

Fixpoint remove_skip_from_seq_stmt(s: stmt) : stmt :=
  match s with
  | Sseq Sskip y =>
    remove_skip_from_seq_stmt y
  | Sseq x Sskip => remove_skip_from_seq_stmt x
  | Sseq x y =>  Sseq (remove_skip_from_seq_stmt x)
                     (remove_skip_from_seq_stmt y)
  (* need these for completeness, just not right now.
  | Sblock s => Sblock (remove_skip_from_seq_stmt s)
  | Sloop s => Sloop (remove_skip_from_seq_stmt s)
  | Sifthenelse cond t e => Sifthenelse cond
                                       (remove_skip_from_seq_stmt t)
                                       (remove_skip_from_seq_stmt e)
   *)
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

(* As seen in Tailcallproof.v *)
Theorem transf_program_match:
  forall p tp, transf_program p = tp -> match_prog p tp.
Proof.
  intros.
  rewrite <- H.
  apply match_transform_program; auto.
Qed.

Section PRESERVATION.
  Variable prog tprog: Cminor.program.
  Hypothesis TRANSL: match_prog prog tprog.

  Let ge := Genv.globalenv prog.
  Let tge := Genv.globalenv tprog.

  (* TODO: understand what the fuck these are doing *)
 Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
 Proof.
   eapply Genv.find_symbol_transf.
   apply TRANSL.
 Qed.

Lemma functions_translated:
  forall (v: val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof.
  apply (Genv.find_funct_transf TRANSL).
Qed.

Lemma funct_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof.
  apply (Genv.find_funct_ptr_transf TRANSL).
Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. apply (Genv.senv_transf TRANSL). Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. 
Qed.

Check(PTree.set).

Inductive match_states: Cminor.state -> Cminor.state -> Prop :=
|  match_deliberate_skip: forall (f: function) (s: stmt)
                          (k: cont)
                          (sp: val)
                          (e: env)
                          (m: mem),
    s <> Sskip -> 
    match_states (State f Sskip (Kseq s k) sp e m)
                 (State f s k sp e m)
| match_non_skip: forall (f: function)
                    (k: cont)
                    (sp: val)
                    (e: env)
                    (m: mem)
                    (s: stmt),
    (s <> Sskip) -> match_states (State f s k sp e m)
                               (State f s k sp e m)
| match_non_deliberate_skip: forall (f: function)
                            (k: cont)
                            (sp: val)
                            (e: env)
                            (m: mem),
     (forall s' k', k <> Kseq s' k') ->
    match_states (State f Sskip k sp e m)
                 (State f Sskip k sp e m)
| match_callstate: forall (f: fundef) (m: mem),
  match_states (Callstate f nil Kstop m)
               (Callstate (transf_fundef f) nil Kstop m).

(* 
               
(* 
| match_skip_setter:
    forall (f: functionte: 
      (k: cont)
      (sp: val)
      (id: ident)
      (v: val)
      (e: env)
      (m: mem)
      (st2: state)
      match_states (State f Sskip k sp (PTree.set id v e) m) st2
*)
      
| match_non_skip_seq_state: forall (f: function)  (s s': stmt)
                 (k: cont)
                 (sp: val)
                 (e: env)
                 (m: mem),
    s <> Sskip -> match_states (State f s (Kseq s' k) sp e m)
                             (State (transf_fn f) s (Kseq s' k) sp e m)

| match_returnstates: forall (v: val)
                        (k: cont)
                        (m: mem),
    match_states (Returnstate v k m) (Returnstate v k m).
*)

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros.
  inversion H.
  subst.
  exists (Callstate (transf_fundef f) nil Kstop m0).
  split; try constructor.
  
  - econstructor; try auto.
    
    + apply (Genv.init_mem_transf TRANSL). auto.

    + replace (prog_main tprog) with (prog_main prog).
      rewrite symbols_preserved. eauto.
      symmetry;
      (* comes from Linking *)
        eapply match_program_main; eauto.

      
    + subst.
      
      assert (Genv.find_funct_ptr tge b = Some (transf_fundef f)).
      apply funct_ptr_translated.
      auto.
      replace (Genv.globalenv tprog) with tge; try auto.

    + rewrite sig_preserved.
      auto.

Qed.

Lemma transf_final_states:
  forall st1 st2 r,
    match_states  st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros.
  inversion H0; inversion H; subst; try discriminate.
Qed.

    


Theorem transf_program_correct:
    forward_simulation (Cminor.semantics prog) (Cminor.semantics tprog).
Proof.
  eapply forward_simulation_opt with (match_states := match_states)
                                     (measure := measure_state).
 
  - apply senv_preserved.
  - apply transf_initial_states.
  - apply transf_final_states.
  - intros until s1'.
    intros STEP_S1_S1'.
    
    induction STEP_S1_S1'.
    
    -- intros s2.
       intros MATCH_S1_S2.
       inversion MATCH_S1_S2; subst.
       + right.
         repeat split; auto; try omega.
         eapply match_non_skip; auto.
       + congruence.

       + specialize (H5 s k).
         congruence.

    -- 
         

    
Admitted.
