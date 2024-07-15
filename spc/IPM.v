Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.
Require Import AList.
Require Import Coq.Init.Decimal.
Require Export IProp.

Set Implicit Arguments.

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Require Export DisableSsreflect.
Arguments Z.of_nat: simpl nomatch.

Section IPM.
  Context {Σ: GRA.t}.

  (* Trivial Ofe Structure *)
  Inductive uPred_equiv' (P Q : iProp') : Prop :=
    { uPred_in_equiv : ∀ x, URA.wf x -> P x <-> Q x }.

  Local Instance uPred_equiv : Equiv iProp' := uPred_equiv'.
  Definition uPred_dist' (n : nat) (P Q : iProp') : Prop := uPred_equiv' P Q.
  Local Instance uPred_dist : Dist iProp' := uPred_dist'.
  Definition uPred_ofe_mixin : OfeMixin iProp'.
  Proof.
    split.
    - intros P Q; split.
      + ii. ss.
      + ii. specialize (H 0). ss.
    - i. split.
      + ii. ss.
      + ii. econs. i. symmetry. apply H. auto.
      + ii. econs. i. transitivity (y x0); [apply H|apply H0]; ss.
    - i. ss.
  Qed.
  Canonical Structure uPredO : ofe := Ofe iProp' uPred_ofe_mixin.

  Program Definition uPred_compl : Compl uPredO := λ c, iProp_intro (fun x => forall n, c n x) _.
  Next Obligation.
    i. ss. i. eapply iProp_mono; eauto.
  Qed.

  Global Program Instance uPred_cofe : Cofe uPredO := {| compl := uPred_compl |}.
  Next Obligation.
    econs. i. split.
    - ii. exploit H0; et.
    - ii. destruct (le_ge_dec n n0).
      + apply c in l. apply l in H0; et.
      + apply c in g. apply g in H0; et.
  Qed.

  Lemma iProp_bi_mixin:
    BiMixin
      Entails Emp Pure And Or Impl
      (@Univ _) (@Ex _) Sepconj Wand
      Persistently.
  Proof.
    econs.
    - exact PreOrder_Entails.
    - econs.
      { uipropall. ii. split; ii; eapply H; et. }
      { uipropall. i. econs. i. des. split; i.
        { eapply H; et. }
        { eapply H1; et. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H. ss. }
      { uipropall. ii. eapply H. ss. }
    - econs. i. split.
      { uipropall. ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
      { uipropall. ii. inv H2. split.
        { eapply H; et. }
        { eapply H0; et. }
      }
    - econs. i. split.
      { uipropall. ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
      { uipropall. ii. inv H2.
        { left. eapply H; et. }
        { right. eapply H0; et. }
      }
    - econs. i. split.
      { uipropall. ii. eapply H0; et. eapply H2; et. eapply H; et. }
      { uipropall. ii. eapply H0; et. eapply H2; et. eapply H; et. }
    - econs. i. split.
      { uipropall. ii. exploit H; et. i. eapply x3; et. }
      { uipropall. ii. exploit H; et. i. eapply x3; et. }
    - econs. i. split.
      { uipropall. ii. inv H1. exploit H; et. i. eexists. eapply x3; et. }
      { uipropall. ii. inv H1. exploit H; et. i. eexists. eapply x3; et. }
    - econs. i. split.
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
      { uipropall. ii. inv H2. des. subst. eexists. esplits; eauto.
        { eapply H; et. eapply URA.wf_mon; et. }
        { eapply H0; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
      }
    - econs. uipropall. i. split.
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
      { ii. exploit H2; et.
        { eapply H; et. eapply URA.wf_mon; et. rewrite URA.add_comm. et. }
        { i. eapply H0; et. }
      }
    - ii. econs. uipropall. i. split.
      { ii. eapply H; ss. eapply URA.wf_core. auto. }
      { ii. eapply H; ss. eapply URA.wf_core. auto. }
    - exact Pure_intro.
    - exact Pure_elim.
    - exact And_elim_l.
    - exact And_elim_r.
    - exact And_intro.
    - exact Or_intro_l.
    - exact Or_intro_r.
    - exact Or_elim.
    - exact Impl_intro_r.
    - exact Impl_elim_l.
    - exact Univ_intro.
    - exact Univ_elim.
    - exact Ex_intro.
    - exact Ex_elim.
    - exact Sepconj_mono.
    - exact Emp_Sepconj_l.
    - exact Emp_Sepconj_r.
    - exact Sepconj_comm.
    - exact Sepconj_assoc.
    - exact Wand_intro_r.
    - exact Wand_elim_l.
    - exact Persistently_mono.
    - exact Persistently_idem.
    - exact Persistently_emp.
    - exact Persistently_and2.
    - exact Persistently_ex.
    - exact Persistently_sep.
    - exact Persistently_and.
  Qed.

  Lemma iProp_bi_later_mixin:
    BiLaterMixin
      Entails Pure Or Impl
      (@Univ _) (@Ex _) Sepconj Persistently Later.
  Proof.
    econs.
    - ii. uipropall. rr. split. ii. ss. apply H. auto.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. specialize (H x). uipropall.
    - ii. uipropall. ii. right. des. exists x. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall.
    - ii. uipropall. ii. right. ss.
  Qed.

  Canonical Structure iProp: bi :=
    {| bi_bi_mixin := iProp_bi_mixin;
       bi_bi_later_mixin := iProp_bi_later_mixin |}.

  Definition OwnM (M: URA.t) `{@GRA.inG M Σ} (r: M): iProp := Own (GRA.embed r).

  (** extra BI instances *)
  Lemma iProp_bupd_mixin_weak: BiBUpdMixin iProp WeakUpd.
  Proof.
    econs.
    - ii. econs. unfold bupd. uipropall. i. split.
      { ii. specialize (H1 ctx). spc H1. des.
        esplits. 2: { eapply H; [|et]. eapply URA.wf_mon; et. } ss. }
      { ii. specialize (H1 ctx). spc H1. des.
        esplits. 2: { eapply H; [|et]. eapply URA.wf_mon; et. } ss. }
    - exact WeakUpd_intro.
    - exact WeakUpd_mono.
    - exact WeakUpd_trans.
    - exact WeakUpd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd_weak: BiBUpd iProp | 10 := {| bi_bupd_mixin := iProp_bupd_mixin_weak |}.

  Lemma iProp_bupd_mixin: BiBUpdMixin iProp Upd.
  Proof.
    econs.
    - ii. econs. unfold bupd. uipropall. i. split.
      { ii. des. esplits; et. eapply H; et. eapply URA.wf_mon; et. eapply H2. rewrite URA.unit_id. et. }
      { ii. des. esplits; et. eapply H; et. eapply URA.wf_mon; et. eapply H2. rewrite URA.unit_id. et. }
    - exact Upd_intro.
    - exact Upd_mono.
    - exact Upd_trans.
    - exact Upd_frame_r.
  Qed.
  Global Instance iProp_bi_bupd: BiBUpd iProp | 0 := {| bi_bupd_mixin := iProp_bupd_mixin |}.

  Global Instance iProp_absorbing (P: iProp): Absorbing P.
  Proof.
    rr. uipropall. i. rr in H. uipropall. des. eapply iProp_mono; eauto.
    exists a. rewrite H. r_solve.
  Qed.

  Global Instance iProp_pure_forall: BiPureForall iProp.
  Proof.
    ii. rr. uipropall. i. rr. rr in H. uipropall.
    i. specialize (H a). rr in H. uipropall.
  Qed.
End IPM.
Arguments OwnM: simpl never.

Section TEST.
  Context {Σ: GRA.t}.

  Goal forall (P Q R: iProp) (PQ: P -∗ Q) (QR: Q -∗ R), P -∗ R.
  Proof.
    i. iStartProof. iIntros "H".
    iApply QR. iApply PQ. iApply "H".
  Qed.

  Goal forall (P Q: iProp), ((bupd P) ∗ Q) -∗ (bupd Q).
  Proof.
    i. iStartProof.
    unfold bupd, bi_bupd_bupd; cbn.
    match goal with
    | [ |- context[Upd] ] => idtac
    | [ |- context[WeakUpd] ] => fail
    end.
    Undo 2.
    iIntros "[Hxs Hys]". iMod "Hxs". iApply "Hys".
  Qed.

  Lemma WeakUpd_fold: WeakUpd = (@bupd (bi_car (@iProp Σ))
                                   (@bi_bupd_bupd (@iProp Σ) (@iProp_bi_bupd_weak Σ))).
  Proof. refl. Qed.

  Goal forall (P Q: iProp), ((WeakUpd P) ∗ Q) -∗ (WeakUpd Q).
  Proof.
    i. iStartProof.
    iIntros "[Hxs Hys]".
    rewrite WeakUpd_fold.
    iMod "Hxs". iApply "Hys".
  Qed.

End TEST.

Infix "⊢" := (@bi_entails iProp).
Infix "**" := bi_sep (at level 99).
Infix "-*" := bi_wand (at level 99, right associativity).
Notation "#=> P" := ((@bupd (bi_car (@iProp _)) (@bi_bupd_bupd (@iProp _) (@iProp_bi_bupd _))) P) (at level 99).

Class IsOp {A : URA.t} (a b1 b2 : A) := is_op : a = b1 ⋅ b2.
Global Arguments is_op {_} _ _ _ {_}.
Global Hint Mode IsOp + - - - : typeclass_instances.

Global Instance is_op_op {A : URA.t} (a b : A) : IsOp (URA.add a b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : URA.t} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Global Hint Mode IsOp' + ! - - : typeclass_instances.
Global Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : URA.t} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Global Hint Mode IsOp'LR + ! - - : typeclass_instances.
Global Instance is_op_lr_op {A : URA.t} (a b : A) : IsOp'LR (URA.add a b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section class_instances.
  Context `{Σ: GRA.t}.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. inv H. red. uipropall. i. des. subst.
    unfold URA.extends in *. des. subst.
    exists (URA.add ctx0 ctx). repeat rewrite URA.add_assoc.
    f_equal. rewrite URA.add_comm. rewrite URA.add_assoc. f_equal.
    eapply URA.add_comm.
  Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof.
    ii. apply bi.intuitionistically_if_mono. inv H.
    uipropall. i. unfold URA.extends in *. des. subst. split.
    { exists (URA.add b2 ctx). eapply URA.add_assoc. }
    { exists (URA.add b1 ctx). rewrite URA.add_assoc.
      f_equal. eapply URA.add_comm. }
  Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. red. inv H. uipropall. i.
    unfold URA.extends in *. des. subst.
    exists b1, (URA.add b2 ctx). split.
    { symmetry. eapply URA.add_assoc. }
    esplits.
    { eapply URA.unit_id. }
    { et. }
  Qed.

  Global Instance from_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. unfold OwnM. inv H0.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    rewrite GRA.embed_add. iApply "H".
  Qed.

  Global Instance into_and_ownM (M: URA.t) `{@GRA.inG M Σ} p (a b1 b2 : M) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. apply bi.intuitionistically_if_mono. inv H0.
    unfold OwnM. rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplit.
    { iApply "H1". }
    { iApply "H2". }
  Qed.

  Global Instance into_sep_ownM (M: URA.t) `{@GRA.inG M Σ} (a b1 b2 : M) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. inv H0. unfold OwnM.
    rewrite <- GRA.embed_add. iIntros "[H1 H2]". iSplitL "H1"; iFrame.
  Qed.
End class_instances.



Section ILEMMAS.
  Context `{Σ: GRA.t}.

  Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      Own a ⊢ #=> P.
  Proof.
    uipropall. ss. i. unfold URA.extends in *. des. subst.
    esplits; et. i. eapply (URA.wf_mon (b:=ctx)). r_wf H.
  Qed.

  Lemma to_semantic (a: Σ) (P: iProp') (SAT: Own a ⊢ P) (WF: URA.wf a)
    :
      P a.
  Proof.
    uipropall. eapply SAT; et. refl.
  Qed.

  Lemma OwnM_valid (M: URA.t) `{@GRA.inG M Σ} (m: M):
    OwnM m -∗ ⌜URA.wf m⌝.
  Proof.
    rr. uipropall. i. red. rr. unfold OwnM, Own in *. uipropall.
    unfold URA.extends in *. des. subst.
    eapply URA.wf_mon in WF. eapply GRA.embed_wf. et.
  Qed.

  Lemma Upd_Pure P
    :
      #=> ⌜P⌝ ⊢ ⌜P⌝.
  Proof.
    rr. uipropall. i. rr. uipropall. des. rr in H. uipropall.
  Qed.

  Lemma Own_WeakUpd_set
        (r1: Σ) B
        (UPD: URA.updatable_set r1 B)
    :
      (Own r1) ⊢ (WeakUpd (∃ b, ⌜B b⌝ ** (Own b))%I)
  .
  Proof.
    cut (Entails (Own r1) (WeakUpd (Ex (fun b => Sepconj (Pure (B b)) (Own b)))%I)); ss.
    uipropall. i. red in H. des. subst.
    exploit (UPD (ctx0 ⋅ ctx)).
    { rewrite URA.add_assoc. et. }
    i. des. exists (b ⋅ ctx0). split.
    { rewrite <- URA.add_assoc. et. }
    { exists b. uipropall. esplits; [|apply IN|refl].
      eapply URA.add_comm. }
  Qed.

  Lemma Own_Upd
        (r1 r2: Σ)
        (UPD: URA.updatable r1 r2)
    :
      (Own r1) ⊢ (#=> (Own r2))
  .
  Proof.
    uipropall. i. exists r2. esplits; et. { refl. } i. eapply UPD. eapply URA.wf_extends; et.
    eapply URA.extends_add; et.
  Qed.

  Lemma Own_extends
        (a b: Σ)
        (EXT: URA.extends a b)
    :
      Own b ⊢ Own a
  .
  Proof.
    red. uipropall. ii. etrans; et.
  Qed.

  Lemma OwnM_WeakUpd_set (M: URA.t) `{@GRA.inG M Σ}
        (r1: M) B
        (UPD: URA.updatable_set r1 B)
    :
      (OwnM r1) ⊢ (WeakUpd (∃ b, ⌜B b⌝ ** (OwnM b))%I)
  .
  Proof.
    assert (UPDM: URA.updatable_set
                    (GRA.embed r1)
                    (fun r => exists m, r = GRA.embed m /\ B m)).
    { red. i. red in UPD.
      unshelve hexploit UPD.
      { eapply (@eq_rect URA.t (Σ (@GRA.inG_id _ _ H)) (@URA.car)).
        { eapply (ctx (@GRA.inG_id _ _ H)). }
        { symmetry. eapply (@GRA.inG_prf _ _ H). }
      }
      Local Transparent GRA.to_URA.
      { ur in WF. ss. specialize (WF GRA.inG_id).
        destruct H. subst. ss.
        unfold GRA.embed in WF. ss.
        replace (PeanoNat.Nat.eq_dec inG_id inG_id)
          with (@left (inG_id = inG_id) (inG_id <> inG_id) eq_refl) in WF; ss.
        { des_ifs. repeat f_equal. eapply proof_irrelevance. }
      }
      i. des. exists (GRA.embed b). esplits; et.
      ur. Local Transparent GRA.to_URA. ss.
      i. unfold GRA.embed. des_ifs.
      { ss. unfold PCM.GRA.cast_ra. destruct  H. subst. ss. }
      { ur in WF. specialize (WF k). rewrite URA.unit_idl.
        eapply URA.wf_mon. rewrite URA.add_comm. et.
      }
    }
    iIntros "H".
    iPoseProof (Own_WeakUpd_set with "H") as "H".
    { eapply UPDM. }
    rewrite WeakUpd_fold. iMod "H".
    iDestruct "H" as (b) "[% H1]". des. subst.
    iModIntro. iExists m. iFrame. ss.
  Qed.

  Lemma OwnM_Upd (M: URA.t) `{@GRA.inG M Σ}
        (r1 r2: M)
        (UPD: URA.updatable r1 r2)
    :
      (OwnM r1) ⊢ (#=> (OwnM r2))
  .
  Proof.
    uipropall. i. exists (GRA.embed r2). esplits; et.
    { unfold OwnM in *. uipropall. refl. }
    i. eapply GRA.embed_updatable in UPD. eapply UPD. eapply URA.wf_extends; et. eapply URA.extends_add; et.
    unfold OwnM in H0. uipropall.
  Qed.

  Lemma OwnM_extends (M: URA.t) `{@GRA.inG M Σ}
        (a b: M)
        (EXT: URA.extends a b)
    :
      OwnM b ⊢ OwnM a
  .
  Proof.
    red. unfold OwnM. uipropall. i. unfold URA.extends in *.
    des. subst. rewrite <- GRA.embed_add.
    rewrite <- URA.add_assoc. et.
  Qed.

End ILEMMAS.

Ltac iOwnWf' H :=
  iPoseProof (OwnM_valid with H) as "%".

Tactic Notation "iOwnWf" constr(H) :=
  iOwnWf' H.

Tactic Notation "iOwnWf" constr(H) "as" ident(WF) :=
  iOwnWf' H;
  match goal with
  | H0: @URA.wf _ _ |- _ => rename H0 into WF
  end
.

(** TODO: move to PCM.v **)
Declare Scope ra_scope.
Delimit Scope ra_scope with ra.
Notation " K ==> V' " := (URA.pointwise K V'): ra_scope.


Section AUX.
  Context {K: Type} `{M: URA.t}.
  Let RA := URA.pointwise K M.

  Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; et. Qed.

  Lemma pw_wf: forall (f: K -> M) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  Lemma pw_add_disj_wf
        (f g: K -> M)
        (WF0: URA.wf (f: @URA.car RA))
        (WF1: URA.wf (g: @URA.car RA))
        (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
    :
      <<WF: URA.wf ((f: RA) ⋅ g)>>
  .
  Proof.
    ii; ss. ur. i. ur in WF0. ur in WF1. spc DISJ. des; rewrite DISJ.
    - rewrite URA.unit_idl; et.
    - rewrite URA.unit_id; et.
  Qed.

  Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
      <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
  Proof.
    i. unfold insert, fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
  Qed.

  Lemma lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.
End AUX.




Section INW.
  Context `{Σ: GRA.t}.
  Definition iNW (name: string) (P: iProp'): iProp' := P.
End INW.
Global Hint Unfold iNW.
Notation "{{ x : t }}" := (@iNW _ x t) (at level 80, x at next level, t at next level, no associativity).


Ltac iSplits :=
  intros; unfold NW, iNW;
  repeat match goal with
         | [ |- @ex _ _ ] => eexists
         | [ |- _ /\ _ ] => split
         | [ |- @sig _ _ ] => eexists
         | [ |- @sigT _ _ ] => eexists
         | [ |- @prod _  _ ] => split
         | |- environments.envs_entails _ (@bi_exist _ _ _) => iExists _
         | _ => iSplit
         end
.


From iris.proofmode Require Import proofmode environments base coq_tactics.
(* (*** copied & modified from DiaFrame ***) *)
Ltac fresh_name name Δ :=
  let rec first_fresh name num :=
    (let base := eval cbv in (match num with | 0 => name | _ => append name (pretty.pretty_nat num) end) in
       let name_in_env := eval cbv in (existsb (fun i => ident_beq i base) (envs_dom Δ)) in
         match constr:(name_in_env) with
         | true =>
             let new_num := eval cbv in (Nat.succ num) in
               first_fresh name new_num
         | false => base
         end)
  in
  let ident := first_fresh name constr:(0%nat) in constr:(ident)
  (* let l := constr:(or_else (last (list_ascii_of_string name)) zero) in *)
  (* match constr:(is_nat l) with *)
  (* | Some ?n => let ident := first_fresh name n in constr:(ident) *)
  (* | _ => let ident := first_fresh name constr:(0%nat) in constr:(ident) *)
  (* end *)
.

Ltac get_fresh_string :=
  match goal with
  | |- context["A"] =>
      match goal with
      | |- context["A0"] =>
          match goal with
          | |- context["A1"] =>
              match goal with
              | |- context["A2"] =>
                  match goal with
                  | |- context["A3"] =>
                      match goal with
                      | |- context["A4"] =>
                          match goal with
                          | |- context["A5"] =>
                              match goal with
                              | |- context["A6"] =>
                                  match goal with
                                  | |- context["A7"] =>
                                      match goal with
                                      | |- context["A8"] =>
                                          match goal with
                                          | |- context["A9"] =>
                                              match goal with
                                              | |- context["A10"] =>
                                                  match goal with
                                                  | |- context["A11"] =>
                                                      match goal with
                                                      | |- context["A12"] => fail 12
                                                      | _ => constr:("A12")
                                                      end
                                                  | _ => constr:("A11")
                                                  end
                                              | _ => constr:("A10")
                                              end
                                          | _ => constr:("A9")
                                          end
                                      | _ => constr:("A8")
                                      end
                                  | _ => constr:("A7")
                                  end
                              | _ => constr:("A6")
                              end
                          | _ => constr:("A5")
                          end
                      | _ => constr:("A4")
                      end
                  | _ => constr:("A3")
                  end
              | _ => constr:("A2")
              end
          | _ => constr:("A1")
          end
      | _ => constr:("A0")
      end
  | _ => constr:("A")
  end
.
(* Ltac iDes := *)
(*   repeat multimatch goal with *)
(*          | |- context[@environments.Esnoc _ _ (INamed ?namm) ?ip] => *)
(*            match ip with *)
(*            | @bi_or _ _ _ => *)
(*              let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ "|" +:+ namm +:+ "]")) in *)
(*              iDestruct namm as pat *)
(*            | @bi_pure _ _ => iDestruct namm as "%" *)
(*            | @iNW _ ?newnamm _ => iEval (unfold iNW) in namm; iRename namm into newnamm *)
(*            | @bi_sep _ _ _ => *)
(*              let f := get_fresh_string in *)
(*              let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ f +:+ "]")) in *)
(*              iDestruct namm as pat *)
(*            | @bi_exist _ _ (fun x => _) => *)
(*              let x := fresh x in *)
(*              iDestruct namm as (x) namm *)
(*            end *)
(*          end *)
(* . *)

Ltac iCombineAll :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ (@environments.Esnoc _ _ (INamed ?nam1) _) (INamed ?nam2) _] =>
           iCombine nam1 nam2 as nam1
         end
.
Ltac xtra := iCombineAll; iAssumption.

Ltac iDes' l :=
  match l with
  | Enil => idtac
  | Esnoc ?tl (IAnon ?x) ?P =>
      match goal with
      | |- envs_entails ?Δ _ => let name := fresh_name "H" Δ in iRename (IAnon x) into name
      end
  | Esnoc ?tl (INamed ?ident) ?P =>
      match P with
      | (∃ x, _)%I =>
          let name := fresh x in
          eapply tac_exist_destruct with (i:=ident) (j:=ident); [reduction.pm_reflexivity|iSolveTC|cbn];
          intro name
      (*** TODO FIXME: below does not work ***)
      (* let name := fresh x in *)
      (* let str := constr:(("[" ++ ident ++ "]")%string) in *)
      (* iDestruct ident as (name) str *)
      | (⌜_⌝ ∗ _)%I =>
          let str := constr:(("[% " ++ ident ++ "]")%string) in
          iDestruct ident as str
      | (⌜_⌝ ∧ _)%I =>
          let str := constr:(("[% " ++ ident ++ "]")%string) in
          iDestruct ident as str
      | (_ ∗ ⌜_⌝)%I =>
          let str := constr:(("[" ++ ident ++ " %]")%string) in
          iDestruct ident as str
      | (_ ∧ ⌜_⌝)%I =>
          let str := constr:(("[" ++ ident ++ " %]")%string) in
          iDestruct ident as str
      | (_ ∗ _)%I =>
          match goal with
          | |- envs_entails ?Δ _ =>
              let ident' := fresh_name ident Δ in
              let str := constr:(("[" ++ ident ++ " " ++ ident' ++ "]")%string) in
              iDestruct ident as str
          end
      | (⌜_⌝)%I => iDestruct ident as "[%]"
      | ({{?H: _}})%I => iEval ltac:(unfold iNW) in ident; iRename ident into H
      | _ => idtac
      end;
      iDes' tl
  end
.

Ltac iDes :=
  repeat match goal with
         | |- envs_entails (Envs _ ?l _) _ => iDes' l
         end
.

Ltac iName :=
  repeat match goal with
         | |- context[Esnoc _ (IAnon ?x) _] =>
             match goal with
             | |- envs_entails ?Δ _ => let name := fresh_name "H" Δ in iRename (IAnon x) into name
             end
         end
.

(* Ltac iIntroall := *)
(*   repeat match goal with *)
(*          | |- envs_entails ?Δ (∀ x, _) => let name := fresh x in idtac name; iIntros (name) *)
(*          | |- envs_entails ?Δ _ => let name := fresh_name "H" Δ in iIntros name *)
(*          | |- _ => iIntros "H" *)
(*          end *)
(* . *)

Goal forall {PROP : bi} (P Q: PROP) R, bi_entails True ((P ∗ Q ∗ ⌜R⌝) -* ⌜True⌝).
  i. iIntros. iDes.
Abort.

