Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HTactics.

Set Implicit Arguments.

Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.


(*** `hsim` is an intermediate step towards `isim`, which is defined in iProp like weakest precondition (wp).
Both `hsim` and `isim` take the postcondition (Q) as an argument like the weakest precondition (wp). ***)

Section SIM.
  Context `{Σ: GRA.t}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Variable stb: gname -> fspec.

  Definition option_Ord_lt (o0 o1: option Ord.t): Prop :=
    match o0, o1 with
    | None, Some _ => True
    | Some o0, Some o1 => Ord.lt o0 o1
    | _, _ => False
    end.

  Lemma option_Ord_lt_well_founded: well_founded option_Ord_lt.
  Proof.
    ii. destruct a.
    { induction (Ord.lt_well_founded t). econs.
      i. destruct y; ss.
      { eapply H0; eauto. }
      { econs. ii. destruct y; ss. }
    }
    { econs; ii. destruct y; ss. }
  Qed.

  Definition option_Ord_le (o0 o1: option Ord.t): Prop :=
    match o0, o1 with
    | None, _ => True
    | Some o0, Some o1 => Ord.le o0 o1
    | _, _ => False
    end.

  Global Program Instance option_Ord_le_PreOrder: PreOrder option_Ord_le.
  Next Obligation.
  Proof.
    ii. destruct x; ss. refl.
  Qed.
  Next Obligation.
  Proof.
    ii. destruct x, y, z; ss. etrans; eauto.
  Qed.

  Lemma option_Ord_lt_le o0 o1
        (LT: option_Ord_lt o0 o1)
    :
      option_Ord_le o0 o1.
  Proof.
    destruct o0, o1; ss. apply Ord.lt_le; auto.
  Qed.

  Lemma option_Ord_lt_le_lt o0 o1 o2
        (LT: option_Ord_lt o0 o1)
        (LE: option_Ord_le o1 o2)
    :
      option_Ord_lt o0 o2.
  Proof.
    destruct o0, o1, o2; ss. eapply Ord.lt_le_lt; eauto.
  Qed.

  Lemma option_Ord_le_lt_lt o0 o1 o2
        (LE: option_Ord_le o0 o1)
        (LT: option_Ord_lt o1 o2)
    :
      option_Ord_lt o0 o2.
  Proof.
    destruct o0, o1, o2; ss. eapply Ord.le_lt_lt; eauto.
  Qed.

  Definition inv_with w0 st_src st_tgt: iProp :=
    (∃ w1, I w1 st_src st_tgt ** ⌜le w0 w1⌝)%I.

  Lemma inv_with_current `{PreOrder _ le} w0 st_src st_tgt
    :
      bi_entails (I w0 st_src st_tgt) (inv_with w0 st_src st_tgt).
  Proof.
    unfold inv_with. iIntros "H". iExists w0. iSplit; auto.
  Qed.

  Lemma inv_with_le `{PreOrder _ le} w0 w1 st_src st_tgt
        (LE: le w0 w1)
    :
      bi_entails (inv_with w1 st_src st_tgt) (inv_with w0 st_src st_tgt).
  Proof.
    unfold inv_with. iIntros "H". iDestruct "H" as (w2) "[H0 %]".
    iExists w2. iSplit; auto. iPureIntro. etrans; eauto.
  Qed.

  Inductive _hsim
            (hsim: forall R_src R_tgt
                          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                          (fmr: Σ),
                bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
            {R_src R_tgt}
            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
            (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hsim_ret
      v_src v_tgt
      st_src st_tgt
      f_src f_tgt
      (RET: current_iProp fmr (Q st_src st_tgt v_src v_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  | hsim_call
      fsp (x: fsp.(meta)) w0 FR
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      f_src f_tgt
      (SPEC: stb fn = fsp)
      (PRE: current_iProp fmr (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) x arg_src arg_tgt))
      (POST: forall fmr1 st_src1 st_tgt1 ret_src ret_tgt
                    (ACC: current_iProp fmr1 (FR ** inv_with w0 st_src1 st_tgt1 ** fsp.(postcond) x ret_src ret_tgt)),
          hsim _ _ Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_assert_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (COND ** IPROPS))
      (SIM: forall fmr1 (ACC: current_iProp fmr1 IPROPS),
          _hsim hsim Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_assume_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (IPROPS))
      (SIM: forall fmr1 (ACC: current_iProp fmr1 (COND ** IPROPS)),
          _hsim hsim Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      f_src f_tgt
      (POST: forall ret,
          hsim _ _ Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsim_tau_src
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsim_tau_tgt
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsim_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: exists x, _hsim hsim Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: forall x, _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsim_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: forall x, _hsim hsim Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: exists x, _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsim_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      f_src f_tgt
      (SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsim_pget_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      _hsim hsim Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsim_progress
      st_src st_tgt itr_src itr_tgt
      (SIM: hsim _ _ Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim Q fmr true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Lemma _hsim_ind2
        (hsim: forall R_src R_tgt
                      (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                      (fmr: Σ),
            bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
        R_src R_tgt Q
        (P: Σ -> bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
        (RET: forall
            fmr
            v_src v_tgt
            st_src st_tgt
            f_src f_tgt
            (RET: current_iProp fmr (Q st_src st_tgt v_src v_tgt)),
            P fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            fmr
            fsp (x: fsp.(meta)) w0 FR
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            f_src f_tgt
            (SPEC: stb fn = fsp)
            (PRE: current_iProp fmr (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) x arg_src arg_tgt))
            (POST: forall fmr1 st_src1 st_tgt1 ret_src ret_tgt
                          (ACC: current_iProp fmr1 (FR ** inv_with w0 st_src1 st_tgt1 ** fsp.(postcond) x ret_src ret_tgt)),
                hsim _ _ Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)),
            P fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (ASSERTSRC: forall
            fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (COND ** IPROPS))
            (SIM: forall fmr1 (ACC: current_iProp fmr1 IPROPS),
                P fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt))
        (ASSUMESRC: forall
            fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (IPROPS))
            (SIM: forall fmr1 (ACC: current_iProp fmr1 (COND ** IPROPS)),
                P fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt))
        (SYSCALL: forall
            fmr
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            f_src f_tgt
            (POST: forall ret,
                hsim _ _ Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            fmr
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            fmr
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            f_src f_tgt
            (SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: _hsim hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            fmr
            st_src st_tgt itr_src itr_tgt
            (SIM: hsim _ _ Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P fmr true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall fmr f_src f_tgt st_src st_tgt
             (SIM: @_hsim hsim _ _ Q fmr f_src f_tgt st_src st_tgt),
        P fmr f_src f_tgt st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply ASSERTSRC; eauto. }
    { eapply ASSUMESRC; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { des. eapply CHOOSESRC; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKESRC; eauto. }
    { des. eapply TAKETGT; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Definition hsim := paco8 _hsim bot8.
  Arguments hsim [_ _] _ _ _ _ _ _.

  Lemma _hsim_mon: monotone8 _hsim.
  Proof.
    ii. induction IN using _hsim_ind2.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
  Qed.
  Hint Resolve _hsim_mon: paco.

  Lemma hsim_ind
        R_src R_tgt Q
        (P: Σ -> bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
        (RET: forall
            fmr
            v_src v_tgt
            st_src st_tgt
            f_src f_tgt
            (RET: current_iProp fmr (Q st_src st_tgt v_src v_tgt)),
            P fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            fmr
            fsp (x: fsp.(meta)) w0 FR
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            f_src f_tgt
            (SPEC: stb fn = fsp)
            (PRE: current_iProp fmr (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) x arg_src arg_tgt))
            (POST: forall fmr1 st_src1 st_tgt1 ret_src ret_tgt
                          (ACC: current_iProp fmr1 (FR ** inv_with w0 st_src1 st_tgt1 ** fsp.(postcond) x ret_src ret_tgt)),
                hsim Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)),
            P fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (ASSERTSRC: forall
            fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (COND ** IPROPS))
            (SIM: forall fmr1 (ACC: current_iProp fmr1 IPROPS),
                P fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt))
        (ASSUMESRC: forall
            fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (IPROPS))
            (SIM: forall fmr1 (ACC: current_iProp fmr1 (COND ** IPROPS)),
                P fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt))
        (SYSCALL: forall
            fmr
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            f_src f_tgt
            (POST: forall ret,
                hsim Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: hsim Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: hsim Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: hsim Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: hsim Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            fmr
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: hsim Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            fmr
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            f_src f_tgt
            (SIM: hsim Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: hsim Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: hsim Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            fmr
            st_src st_tgt itr_src itr_tgt
            (SIM: hsim Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P fmr true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall fmr f_src f_tgt st_src st_tgt
             (SIM: hsim Q fmr f_src f_tgt st_src st_tgt),
        P fmr f_src f_tgt st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _hsim_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. hexploit POST; eauto. i. pclearbot. eauto. }
    { eapply ASSERTSRC; eauto. }
    { eapply ASSUMESRC; eauto. }
    { eapply SYSCALL; eauto. i. hexploit POST; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. pfold. eauto. }
    { eapply TAUTGT; eauto. pfold. eauto. }
    { des. eapply CHOOSESRC; eauto. esplits; eauto. pfold. eauto. }
    { eapply CHOOSETGT; eauto. i. hexploit SIM; eauto. i. des. pclearbot. splits; eauto. pfold. eauto. }
    { eapply TAKESRC; eauto. i. hexploit SIM; eauto. i. des. pclearbot. splits; eauto. pfold. eauto. }
    { des. eapply TAKETGT; eauto. esplits; eauto. pfold. eauto. }
    { eapply PPUTSRC; eauto. pfold. eauto. }
    { eapply PPUTTGT; eauto. pfold. eauto. }
    { eapply PGETSRC; eauto. pfold. eauto. }
    { eapply PGETTGT; eauto. pfold. eauto. }
    { eapply PROGRESS; eauto. pclearbot. eauto. }
  Qed.

  Local Transparent HoareFunRet HoareCall.
  Lemma hsim_adequacy_aux `{PreOrder _ le}:
    forall
      f_src f_tgt st_src st_tgt (itr_src: itree Es' Any.t) itr_tgt (mr_src: Σ) fr X (x: X) Q w0
      (SIM: hsim (fun st_src st_tgt ret_src ret_tgt =>
                    (inv_with w0 st_src st_tgt) ** (Q x ret_src ret_tgt: iProp)) (fr ⋅ mr_src) f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt)),
      paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 (@eq Any.t))
            f_src f_tgt w0
            (Any.pair st_src mr_src↑,
              ('(fr1, r) <- interp_condE_tgt (interp_Es'_tgt stb itr_src) fr;;
              '(_, r) <- interp_condE_tgt (HoareFunRet Q x r) fr1;;
              Ret r))
            (st_tgt, itr_tgt).
  Proof.
    ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt). remember (fr ⋅ mr_src).
    revert st_src st_tgt itr_src itr_tgt Heqp Heqp0 CIH Heqc. revert mr_src. revert fr.
    induction SIM using hsim_ind; i; clarify.
    { eapply current_iPropL_convert in RET. mDesAll. steps.
      unfold inv_with in RET. mDesAll.
      unfold HoareFunRet, ASSERT. steps.
      eapply sim_itreeC_spec; econs; i.
      esplits. steps.
      eapply hassert_clo_strong.
      { eapply current_iProp_entail; et.
        { iIntros "[A [B _]]". iFrame. iSplitR; try iAssumption. instantiate (1:=True%I); ss. }
      }
      i. steps. rr. esplits; ss; et. econs; et.
    }
    { eapply current_iPropL_convert in PRE. mDesAll. steps.
      unfold inv_with in PRE. mDesAll.
      unfold HoareCall, ASSERT, ASSUME. steps.
      eapply sim_itreeC_spec; econs; i. esplits.
      steps.
      eapply sim_itreeC_spec; econs; i. esplits.
      steps.
      eapply hassert_clo_strong.
      { eapply current_iProp_entail; et.
        { iIntros "[A [B [C _]]]". iSplitR "A"; [|iAssumption]. iFrame. iAssumption.
        }
      }
      i. steps.
      eapply sim_itreeC_spec; econs; i.
      { econs; eauto. }
      steps. inv WF0.
      eapply hassume_clo; et.
      { instantiate (1:=FR ** I w2 mp_src st_tgt1). i. econs; et.
        - uipropall. esplits; et. eapply RSRC. eapply URA.wf_extends; et. exists fr1; r_solve.
        - refl.
      }
      i. steps. gbase. hexploit CIH.
      { eapply POST. eapply current_iProp_entail; [eauto|].
        iIntros; iDes. iFrame. iExists w2. iSplit; eauto. }
      i. ss; eauto.
    }
    (* { eapply current_iPropL_convert in RET. mDesAll. steps. *)
    (*   { unfold inv_with in RET. mDesAll. hret _; eauto. *)
    (*     iModIntro. iSplitL "H"; auto. } *)
    (* } *)
    (* { eapply current_iPropL_convert in PRE. mDesAll. steps. *)
    (*   { destruct (stb fn) eqn:T. ss. *)
    (*     unfold inv_with in PRE. mDesAll. hcall _ _ with "A A1". *)
    (*     { iModIntro. iSplitL "A1"; eauto. } *)
    (*     { i. steps. gbase. hexploit CIH. *)
    (*       { eapply POST. eapply current_iProp_entail; [eauto|]. *)
    (*         start_ipm_proof. iSplitR "POST". *)
    (*         { iSplitL "H"; eauto. iExists a1. iSplit; eauto. } *)
    (*         { iApply "POST". } *)
    (*       } *)
    (*       i. ss; eauto. *)
    (*     } *)
    (*   } *)
    (* } *)
    { steps. eapply hassert_clo; et. i. steps. eapply SIM; ss; et. }
    { steps. eapply hassume_clo; et. i. steps. eapply SIM; ss; et. }
    { steps.
      { gbase. hexploit CIH; eauto. }
    }
    { steps.
      { exploit IHSIM; eauto. }
    }
    { steps. exploit IHSIM; eauto. }
    { des. exploit IH; eauto. i. steps.
      { force_l. eexists. steps. eauto. }
    }
    { steps. exploit SIM; eauto. i. des. eauto. }
    { steps.
      { exploit SIM; eauto. i. des. eauto. }
    }
    { des. exploit IH; eauto. i. force_r. eexists. eauto. }
    { steps.
      { exploit IHSIM; eauto. }
    }
    { steps. exploit IHSIM; eauto. }
    { steps.
      { exploit IHSIM; eauto. }
    }
    { steps. exploit IHSIM; eauto. }
    { deflag. gbase. eapply CIH; eauto. }
  Qed.

  Lemma hsim_adequacy `{PreOrder _ le}:
    forall
      f_src f_tgt st_src st_tgt (itr_src: itree Es' Any.t) itr_tgt mr_src fr X (x: X) Q w0
      (SIM: hsim (fun st_src st_tgt ret_src ret_tgt =>
                    (inv_with w0 st_src st_tgt) ** (Q x ret_src ret_tgt: iProp)) (fr ⋅ mr_src) f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt)),
      paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 (@eq Any.t))
            f_src f_tgt w0
            (Any.pair st_src mr_src↑,
              ('(fr1, r) <- interp_condE_tgt (interp_Es'_tgt stb itr_src) fr;;
              '(_, r) <- interp_condE_tgt (HoareFunRet Q x r) fr1;;
              Ret r))
            (st_tgt, itr_tgt).
  Proof.
    i. hexploit hsim_adequacy_aux; eauto.
  Qed.

  Lemma hsim_progress_flag R_src R_tgt r g Q fmr st_src st_tgt
        (SIM: gpaco8 _hsim (cpn8 _hsim) g g R_src R_tgt Q fmr false false st_src st_tgt)
    :
      gpaco8 _hsim (cpn8 _hsim) r g _ _ Q fmr true true st_src st_tgt.
  Proof.
    destruct st_src, st_tgt. gstep. eapply hsim_progress; eauto.
  Qed.

  Lemma _hsim_flag_mon
        r
        R_src R_tgt Q fmr
        f_src0 f_tgt0 f_src1 f_tgt1 st_src st_tgt
        (SIM: @_hsim r R_src R_tgt Q fmr f_src0 f_tgt0 st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_hsim r R_src R_tgt Q fmr f_src1 f_tgt1 st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _hsim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6. eapply IHSIM; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits. eapply IH; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. eapply IH; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12. eapply IHSIM; auto. }
    { econs 13. eapply IHSIM; auto. }
    { econs 14. eapply IHSIM; auto. }
    { econs 15. eapply IHSIM; auto. }
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs 16; eauto. }
  Qed.

  Variant hflagC (r: forall R_src R_tgt
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1
      st_src st_tgt
      (SIM: r _ _ Q fmr f_src0 f_tgt0 st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      hflagC r Q fmr f_src1 f_tgt1 st_src st_tgt
  .

  Lemma hflagC_mon:
    monotone8 hflagC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hflagC_mon: paco.

  Structure grespectful clo : Prop :=
    grespect_intro {
        grespect_mon: monotone8 clo;
        grespect_respect :
          forall l r
                 (LE: l <8= r)
                 (GF: l <8= @_hsim r),
            clo l <8= gpaco8 _hsim (cpn8 _hsim) bot8 (rclo8 (clo \9/ gupaco8 _hsim (cpn8 _hsim)) r);
      }.

  Lemma grespect_uclo clo
        (RESPECT: grespectful clo)
    :
      clo <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    eapply grespect8_uclo; eauto with paco.
    econs.
    { eapply RESPECT. }
    i. hexploit grespect_respect.
    { eauto. }
    { eapply LE. }
    { eapply GF. }
    { eauto. }
    i. inv H. eapply rclo8_mon.
    { eauto. }
    i. ss. des; ss. eapply _paco8_unfold in PR0.
    2:{ ii. eapply _hsim_mon; [eapply PR1|]. i. eapply rclo8_mon; eauto. }
    ss. eapply _hsim_mon.
    { eapply PR0; eauto. }
    i. eapply rclo8_clo. right. econs.
    eapply rclo8_mon; eauto. i. inv PR2.
    { left. eapply paco8_mon; eauto. i. ss. des; ss.
      left. auto. }
    { des; ss. right. auto. }
  Qed.

  Lemma hflagC_spec: hflagC <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    eapply grespect_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    gstep.
    eapply _hsim_flag_mon; eauto.
    eapply _hsim_mon; eauto. i. gbase. eapply rclo8_base. auto.
  Qed.

  Variant hsimC
          (r g: forall R_src R_tgt
                       (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                       (fmr: Σ),
              bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hsimC_ret
      v_src v_tgt
      st_src st_tgt
      f_src f_tgt
      (RET: current_iProp fmr (Q st_src st_tgt v_src v_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  | hsimC_call
      fsp (x: fsp.(meta)) w0 FR
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      f_src f_tgt
      (SPEC: stb fn = fsp)
      (PRE: current_iProp fmr (FR ** I w0 st_src0 st_tgt0 ** fsp.(precond) x arg_src arg_tgt))
      (POST: forall fmr1 st_src1 st_tgt1 ret_src ret_tgt
                    (ACC: current_iProp fmr1 (FR ** inv_with w0 st_src1 st_tgt1 ** fsp.(postcond) x ret_src ret_tgt)),
          g _ _ Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsimC_assert_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (COND ** IPROPS))
      (SIM: forall fmr1 (ACC: current_iProp fmr1 IPROPS),
          r _ _ Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_assume_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (IPROPS))
      (SIM: forall fmr1 (ACC: current_iProp fmr1 (COND ** IPROPS)),
          r _ _ Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      f_src f_tgt
      (POST: forall ret,
          g _ _ Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsimC_tau_src
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsimC_tau_tgt
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsimC_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: exists x, r _ _ Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: forall x, r _ _ Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsimC_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: forall x, r _ _ Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: exists x, r _ _ Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsimC_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      f_src f_tgt
      (SIM: r _ _ Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsimC_pget_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: r _ _ Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      hsimC r g Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsimC_progress
      st_src st_tgt itr_src itr_tgt
      (SIM: g _ _ Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g Q fmr true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Lemma hsim_indC_mon_gen r0 r1 g0 g1
        (LE0: r0 <8= r1)
        (LE1: g0 <8= g1)
    :
      @hsimC r0 g0 <8= @hsimC r1 g1.
  Proof.
    ii. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
  Qed.

  Lemma hsim_indC_mon: monotone8 (fun r => @hsimC r r).
  Proof.
    ii. eapply hsim_indC_mon_gen; eauto.
  Qed.

  Lemma hsim_indC_spec:
    (fun r => @hsimC r r) <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    eapply wrespect8_uclo; eauto with paco. econs.
    { eapply hsim_indC_mon. }
    i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 5; eauto. i. eapply rclo8_base. eauto. }
    { econs 6; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 12; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 13; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 14; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 15; eauto. eapply _hsim_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 16; eauto. eapply rclo8_base. eauto. }
  Qed.

  Lemma hsimC_spec:
    hsimC <10= gpaco8 (_hsim) (cpn8 _hsim).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 3; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 4; eauto. gbase. eauto. }
    { gstep. econs 5; eauto. i. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 6; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 7; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 8; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 9; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 10; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 11; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 12; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 13; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 14; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 15; eauto. gbase. eauto. }
    { gstep. econs 16; eauto. i. gbase. eauto. }
  Qed.

  Lemma hsimC_uclo r g:
    @hsimC (gpaco8 (_hsim) (cpn8 _hsim) r g) (gupaco8 (_hsim) (cpn8 _hsim) g) <8= gpaco8 (_hsim) (cpn8 _hsim) r g.
  Proof.
    i. eapply hsimC_spec in PR.  ss.
    eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon; eauto. i. eapply gupaco8_mon; eauto.
  Qed.

  Variant hbindC (r: forall R_src R_tgt
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hbindC_intro
      S_src S_tgt
      (P: Any.t -> Any.t -> S_src -> S_tgt -> iProp)
      f_src f_tgt st_src0 st_tgt0 itr_src itr_tgt ktr_src ktr_tgt
      (SIM: @r S_src S_tgt P fmr f_src f_tgt (st_src0, itr_src) (st_tgt0, itr_tgt))
      (SIMK: forall fmr1 st_src1 st_tgt1 ret_src ret_tgt
                    (POST: current_iProp fmr1 (P st_src1 st_tgt1 ret_src ret_tgt)),
          @r R_src R_tgt Q fmr1 false false (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      hbindC r Q fmr f_src f_tgt (st_src0, itr_src >>= ktr_src) (st_tgt0, itr_tgt >>= ktr_tgt)
  .

  Lemma hbindC_mon:
    monotone8 hbindC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hbindC_mon: paco.

  Lemma hbindC_spec: hbindC <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    eapply grespect_uclo.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    remember (st_src0, itr_src). remember (st_tgt0, itr_tgt).
    revert st_src0 itr_src st_tgt0 itr_tgt Heqp Heqp0.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { hexploit SIMK; eauto. i.
      eapply GF in H. guclo hflagC_spec. econs.
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=false). ss. }
      gstep. eapply _hsim_mon; eauto. i. gbase. eapply rclo8_base. auto.
    }
    { gstep. econs 2; eauto. i. hexploit POST; eauto. i.
      gbase. eapply rclo8_clo_base. left. econs; eauto.
    }
    { eapply hsimC_uclo. econs 3; eauto. }
    { eapply hsimC_uclo. econs 4; eauto. }
    { gstep. econs 5; eauto. i. gbase. eapply rclo8_clo_base. left. econs; eauto. }
    { eapply hsimC_uclo. econs 6; eauto. }
    { eapply hsimC_uclo. econs 7; eauto. }
    { des. eapply hsimC_uclo. econs 8; eauto. }
    { eapply hsimC_uclo. econs 9; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { eapply hsimC_uclo. econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { des. eapply hsimC_uclo. econs 11; eauto. }
    { eapply hsimC_uclo. econs 12; eauto. }
    { eapply hsimC_uclo. econs 13; eauto. }
    { eapply hsimC_uclo. econs 14; eauto. }
    { eapply hsimC_uclo. econs 15; eauto. }
    { gstep. econs 16; eauto. gbase. eapply rclo8_clo_base. left. econs; eauto. }
  Qed.

  Variant hmonoC (r: forall R_src R_tgt
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hmonoC_intro
      f_src f_tgt Q0
      st_src st_tgt
      (SIM: r _ _ Q0 fmr f_src f_tgt st_src st_tgt)
      (MONO: forall st_src st_tgt ret_src ret_tgt,
          (bi_entails (Q0 st_src st_tgt ret_src ret_tgt) (#=> Q st_src st_tgt ret_src ret_tgt)))
    :
      hmonoC r Q fmr f_src f_tgt st_src st_tgt
  .

  Lemma hmonoC_mon:
    monotone8 hmonoC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hmonoC_mon: paco.

  Lemma hmonoC_spec: hmonoC <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_upd.
      eapply current_iProp_entail; eauto.
    }
    { econs 2; eauto. i. eapply rclo8_clo_base. econs; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. i. eapply rclo8_clo_base. econs; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. eapply rclo8_clo_base. econs; eauto. }
  Qed.

  Variant hframeC_aux (r: forall R_src R_tgt
                             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                             (res: Σ),
                      bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (res: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hframeC_aux_intro
      res0 frm
      f_src f_tgt
      st_src st_tgt
      (PRE: URA.wf res)
      (UPD: URA.updatable res (res0 ⋅ frm))
      (SIM: r _ _ (fun st_src st_tgt ret_src ret_tgt => Own frm -* #=> Q st_src st_tgt ret_src ret_tgt)
              res0 f_src f_tgt st_src st_tgt)
    :
      hframeC_aux r Q res f_src f_tgt st_src st_tgt
  .

  Lemma hframeC_aux_mon:
    monotone8 hframeC_aux.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hframeC_aux_mon: paco.

  Lemma current_iProp_updatable (res0 res1: Σ) P
        (WF: URA.wf res1)
        (UPD: URA.updatable res1 res0)
        (CUR: current_iProp res0 P)
    :
      current_iProp res1 P.
  Proof.
    inv CUR. econs; try eassumption. etrans; et.
  Qed.

  Lemma current_iProp_frame_own res0 res1 P
        (WF: URA.wf ((res0 ⋅ res1): Σ))
        (CUR: current_iProp (res0) (Own res1 -* P))
    :
      current_iProp (res0 ⋅ res1) P.
  Proof.
    inv CUR. uipropall. hexploit IPROP.
    2:{ refl. }
    { eapply URA.updatable_wf; try apply WF; et. eapply URA.updatable_add; et. refl. }
    i. econs; eauto. eapply URA.updatable_add; et. refl.
  Qed.

  Lemma current_iProp_frame_own_rev res0 res1 P
        (CUR: current_iProp res0 (Own res1 ** P))
    :
      exists res2, URA.wf res0 /\ URA.updatable res0 (res2 ⋅ res1) ∧ current_iProp res2 P.
  Proof.
    inv CUR. uipropall.
    unfold URA.extends in *. des; clarify.
    exists (ctx ⋅ b). esplits; et.
    { etrans; et. replace (ctx ⋅ b ⋅ res1) with (res1 ⋅ ctx ⋅ b) by r_solve; ss. }
    econs; eauto.
    { eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists res1. r_solve. }
    { eapply URA.extends_updatable. exists ctx. r_solve. }
  Qed.

  (* Lemma current_iProp_own_wf ctx res *)
  (*       (CUR: current_iProp ctx (Own res)) *)
  (*   : *)
  (*     URA.wf (ctx ⋅ res). *)
  (* Proof. *)
  (*   inv CUR. uipropall. unfold URA.extends in *. des. clarify. *)
  (*   eapply URA.wf_mon. *)
  (*   instantiate (1:=ctx0). r_wf GWF. *)
  (* Qed. *)

  Lemma hframeC_aux_spec: hframeC_aux <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    (* eapply grespect_uclo; eauto with paco. *)
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    revert x3 PRE UPD.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_upd. eapply current_iProp_updatable; et.
      eapply current_iProp_frame_own in RET; eauto. eapply URA.updatable_wf; et. }
    { econs 2; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail.
        { eapply PRE. }
        iIntros "[[H0 H1] H2] H3".
        iSplitR "H2"; [|iExact "H2"].
        iSplitR "H1"; [|iExact "H1"].
        instantiate (1:= _ ** _).
        iSplitL "H0"; [iExact "H0"|].
        iExact "H3".
      }
      { i. eapply rclo8_clo_base.
        eapply current_iProp_entail in ACC; cycle 1.
        { iIntros "[[[H0 H1] H2] H3]". iCombine "H1 H0 H2 H3" as "H". iExact "H". }
        eapply current_iProp_frame_own_rev in ACC. des.
        econs; et.
        { eapply POST; eauto.
          eapply current_iProp_entail.
          { eapply ACC1. }
          iIntros "[H0 [H1 H2]]".
          iFrame.
        }
      }
    }
    { econs 3; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail.
        { eapply PRE. }
        iIntros "[H0 H1] H2". iFrame.
        instantiate (1:= _ ** _).
        iSplitL "H2"; iAssumption.
      }
      { i.
        eapply current_iProp_frame_own_rev in ACC. des.
        eapply SIM; et.
      }
    }
    { econs 4; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail.
        { eapply PRE. }
        iIntros "H1 H2".
        instantiate (1:= _ ** _).
        iSplitL "H2"; iAssumption.
      }
      { i.
        eapply current_iProp_entail in ACC; cycle 1.
        { iIntros "[A [B C]]". iCombine "B A C" as "A". iExact "A". }
        eapply current_iProp_frame_own_rev in ACC. des.
        eapply SIM; et.
      }
    }
    { econs 5; eauto. i. eapply rclo8_clo_base. econs; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. eapply rclo8_clo_base. econs; eauto. }
  Qed.

  Variant hframeC (r: forall R_src R_tgt
                             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                             (fmr: Σ),
                      bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hframeC_intro
      P0 P1
      f_src f_tgt
      st_src st_tgt
      (PRE: current_iProp fmr (P0 ** P1))
      (SIM: forall fmr (PRE: current_iProp fmr P1),
          r _ _ (fun st_src st_tgt ret_src ret_tgt => P0 -* #=> Q st_src st_tgt ret_src ret_tgt) fmr f_src f_tgt st_src st_tgt)
    :
      hframeC r Q fmr f_src f_tgt st_src st_tgt
  .

  Lemma hframeC_spec: hframeC <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    ii. inv PR.
    inv PRE. rr in IPROP.
    autounfold with iprop in IPROP.
    autorewrite with iprop in IPROP. des. clarify.
    guclo hframeC_aux_spec. econs.
    { ss. }
    { rewrite URA.add_comm. eauto. }
    { guclo hmonoC_spec. econs.
      { gbase. eapply SIM. econs; eauto.
        - eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists a; r_solve.
        - refl.
      }
      { i. ss. iIntros "H0". iModIntro. iIntros "H1".
        iApply bupd_trans. iApply "H0".
        iStopProof. uipropall.
        i. red in H. des. clarify. esplits; [eassumption|eauto].
        i. eapply URA.wf_extends. { exists ctx. r_solve. } r_wf H.
      }
    }
  Qed.

  Variant hupdC (r: forall R_src R_tgt
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop)
          {R_src R_tgt}
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es R_tgt -> Prop :=
  | hupdC_intro
      f_src f_tgt
      st_src st_tgt
      fmr1
      (WF: URA.wf fmr)
      (UPD: URA.updatable fmr fmr1)
      (SIM: r _ _ Q fmr1 f_src f_tgt st_src st_tgt)
    :
      hupdC r Q fmr f_src f_tgt st_src st_tgt
  .

  Lemma hupdC_mon:
    monotone8 hupdC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hupdC_mon: paco.

  Lemma hupdC_spec: hupdC <9= gupaco8 (_hsim) (cpn8 _hsim).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM. revert x3 WF UPD.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_updatable; et. }
    { econs 2; eauto. { eapply current_iProp_updatable; et. }
      i. eapply rclo8_clo_base. econs; eauto; try refl. apply ACC.
    }
    { econs 3; eauto. { eapply current_iProp_updatable; et. }
      i. eapply SIM; et; try refl. apply ACC.
    }
    { econs 4; eauto. { eapply current_iProp_updatable; et. }
      i. eapply SIM; et; try refl. apply ACC.
    }
    { econs 5; eauto. i. eapply rclo8_clo_base. econs; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. des. esplits; eauto. }
    { econs 9; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. eapply rclo8_clo_base. econs; eauto. }
  Qed.
End SIM.
#[export] Hint Resolve _hsim_mon: paco.
#[export] Hint Resolve cpn9_wcompat: paco.
