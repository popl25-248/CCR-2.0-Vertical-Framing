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
From Ordinal Require Export Ordinal Arithmetic.
Require Import Red IRed.
Require Import ProofMode.
Require Export HTactics.

Set Implicit Arguments.






(***
Note: in below lemmas, argp and retp are both ∀ quantified.
Q: They should be dual and one should be ∃?
A: No:
parg <- choose(); pret := f(parg); vret_src <- take();
parg <- choose(); pret := f(parg); vret_tgt <- take();
In both cases, ∀ appears in either source or target, and we need to deal with it;
thus the reasoning principle should also be ∀ quantified.
Specifically, "parg <- choose()" in the target will give you ∀ quantified parg, and
"pret <- take()" in the source will give you ∀ quantified pret.

***)

Section MODE.

  Context `{Σ: GRA.t}.

  Let OwnT := Own.

  Local Transparent HoareFun HoareFunArg HoareFunRet HoareCall.

  Variant mk_wf (A: Type)
          (R: A -> Any.t -> Any.t -> iProp)
    : A -> Any.t * Any.t -> Prop :=
  | mk_wf_intro
      a
      mr_src' mr_tgt mp_src mp_tgt
      (RSRC: URA.wf mr_src' -> (R a mp_src mp_tgt) mr_src')
    :
      mk_wf R a ((Any.pair mp_src (mr_src' ⋅ mr_tgt)↑), (Any.pair mp_tgt mr_tgt↑))
  .

  Local Ltac steps := repeat (ired_both; repeat (apply sim_itreeC_spec; econs; i)).
  Local Transparent handle_condE_tgt.

  Lemma hassert_src_clo_strong
          A a (le: A -> A -> Prop)
          (R: A -> Any.t -> Any.t -> iProp)
          (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
          r rg m n mp_src0 mp_tgt mr_tgt itr_tgt ktr_src (mr_srctgt0: Σ)
          (COND: iProp) fr0 FRES MRES
          (ACC: current_iProp (fr0 ⋅ (mr_srctgt0)) (COND ** FRES ** MRES ** OwnT mr_tgt))
          (POST: forall (mr_src1 fr1: Σ)
                        (WF: URA.wf (fr1 ⋅ (mr_src1 ⋅ mr_tgt)))
                        (ACCMR: (MRES) (mr_src1))
                        (ACCFR: (FRES) (fr1)),
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true n a
             (Any.pair mp_src0 (mr_src1 ⋅ mr_tgt)↑, ktr_src (fr1, tt))
             (Any.pair mp_tgt mr_tgt↑, itr_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 (mr_srctgt0)↑,
               handle_condE_tgt (Cassert COND) fr0 >>= ktr_src)
             (Any.pair mp_tgt mr_tgt↑, itr_tgt)
  .
  Proof.
    { steps.
      eapply current_iPropL_convert in ACC. mDesAll. rr in ACC. inv ACC.
      assert(T: ∃ fr mr cr x, r0 = fr ⋅ mr ⋅ cr ⋅ x ⋅ mr_tgt ∧ FRES fr ∧ MRES mr ∧ COND cr).
      { rr in IPROP. uipropall. des; ss. clarify. rr in IPROP6. uipropall.
        rr in IPROP6. des; clarify. esplits; et. instantiate (1:=b2 ⋅ ctx). r_solve. }
      des; ss. clarify. clear IPROP.
      eexists (cr, fr, (mr ⋅ mr_tgt)). unfold mput, mget. steps. unfold guarantee. steps.
      unshelve esplits; et.
      { etrans; et. eapply URA.extends_updatable. exists x. r_solve. }
      steps. esplits; et. steps.
      eapply POST; ss; et.
      { eapply URA.updatable_wf; et.
        etrans; et. eapply URA.extends_updatable. exists (x ⋅ cr). r_solve. }
    }
  Qed.

  Lemma hassert_src_clo
          A a (le: A -> A -> Prop)
          (R: A -> Any.t -> Any.t -> iProp)
          (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
          r rg m n mp_src0 mp_tgt mr_srctgt0 mr_tgt itr_tgt ktr_src
          (COND: iProp) fr0 FR
          (ACC: current_iProp (fr0 ⋅ (mr_srctgt0)) (COND ** FR ** OwnT mr_tgt))
          (POST: forall (mr_src1 fr1: Σ)
                        (ACC: current_iProp (fr1 ⋅ (mr_src1 ⋅ mr_tgt)) (FR ** OwnT mr_tgt)),
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true n a
             (Any.pair mp_src0 (mr_src1 ⋅ mr_tgt)↑, ktr_src (fr1, tt))
             (Any.pair mp_tgt mr_tgt↑, itr_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 (mr_srctgt0)↑,
               handle_condE_tgt (Cassert COND) fr0 >>= ktr_src)
             (Any.pair mp_tgt mr_tgt↑, itr_tgt)
  .
  Proof.
    { eapply hassert_src_clo_strong; et.
      { eapply current_iProp_entail; et. iIntros. iDes. iFrame. iSplitL; try iAssumption.
        instantiate (1:=True%I). ss. }
      i. eapply POST; et.
      econs; et.
      { rr. uipropall. esplits; et. rr. uipropall. refl. }
      { eapply URA.extends_updatable. exists mr_src1; r_solve. }
    }
  Qed.

  Lemma hassume_src_clo_strong
          A a (le: A -> A -> Prop)
          (R: A -> Any.t -> Any.t -> iProp)
          (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
          r rg m n mp_src0 mp_tgt itr_tgt ktr_src (mr_src0: Σ)
          (COND: iProp) fr0 FR (mr_tgt: Σ)
          (ACC: URA.wf (fr0 ⋅ mr_src0) -> current_iProp (fr0 ⋅ mr_src0) FR)
          (POST: forall cr
                        (WF: URA.wf (cr ⋅ fr0 ⋅ mr_src0))
                        (CND: COND cr)
                        (ACC: current_iProp (fr0 ⋅ mr_src0) (FR))
                        (ACCDERIVED: current_iProp (cr ⋅ fr0 ⋅ mr_src0) (COND ** FR))
            ,
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true n a
             (Any.pair mp_src0 (mr_src0)↑, ktr_src (cr ⋅ fr0, tt))
             (Any.pair mp_tgt mr_tgt↑, itr_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 (mr_src0)↑,
               handle_condE_tgt (Cassume COND) fr0 >>= ktr_src)
             (Any.pair mp_tgt mr_tgt↑, itr_tgt)
  .
  Proof.
    { steps. unfold mput, mget. steps. unfold assume. steps.
      assert(T: current_iProp (fr0 ⋅ mr_src0) FR).
      { hexploit1 ACC.
        { eapply URA.wf_extends; et. exists x. r_solve. }
        inv ACC. econs; et.
      }
      eapply POST; ss; et.
      clear ACC.
      eapply current_iPropL_convert in T.
      eapply current_iPropL_push with (hd:= ("A", COND)) in T; et.
      { replace (x ⋅ fr0 ⋅ mr_src0) with (fr0 ⋅ mr_src0 ⋅ x) by r_solve.
        eapply current_iProp_entail; eauto.
        iIntros "[A [B C]]". iFrame.
      }
      { r_wf x0. }
    }
  Qed.

  Lemma hassume_src_clo
          A a (le: A -> A -> Prop)
          (R: A -> Any.t -> Any.t -> iProp)
          (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
          r rg m n mp_src0 mp_tgt itr_tgt ktr_src (mr_src0: Σ)
          (COND: iProp) fr0 FR (mr_tgt: Σ)
          (ACC: URA.wf (fr0 ⋅ mr_src0) -> current_iProp (fr0 ⋅ mr_src0) FR)
          (POST: forall (fr1: Σ)
                        (ACC: current_iProp (fr1 ⋅ mr_src0) (COND ** FR)),
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true n a
             (Any.pair mp_src0 mr_src0↑, ktr_src (fr1, tt))
             (Any.pair mp_tgt mr_tgt↑, itr_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0↑,
               handle_condE_tgt (Cassume COND) fr0 >>= ktr_src)
             (Any.pair mp_tgt mr_tgt↑, itr_tgt)
  .
  Proof.
    eapply hassume_src_clo_strong; et.
  Qed.

  Lemma hassume_tgt_clo_strong
          A a (le: A -> A -> Prop)
          (R: A -> Any.t -> Any.t -> iProp)
          (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
          r rg m n mp_src0 mp_tgt mr_tgt0 itr_src ktr_tgt (mr_src0: Σ)
          (COND: iProp) fr_src fr_tgt0 FR
          (ACC: current_iProp (fr_src ⋅ mr_src0)
                  (COND ** FR ** OwnT (fr_tgt0) ** OwnT mr_tgt0))
          (POST: forall (cr: Σ)
                        (CND: COND cr)
                        (ACC: current_iProp (fr_src ⋅ mr_src0)
                                (FR ** OwnT (fr_tgt0) ** OwnT cr ** OwnT mr_tgt0)),
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m true a
             (Any.pair mp_src0 mr_src0↑, itr_src)
             (Any.pair mp_tgt mr_tgt0↑, ktr_tgt (cr ⋅ fr_tgt0, tt)))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0↑, itr_src)
             (Any.pair mp_tgt mr_tgt0↑, handle_condE_tgt (Cassume COND) fr_tgt0 >>= ktr_tgt)
  .
  Proof.
    { steps.
      eapply current_iPropL_convert in ACC. mDesAll. rr in ACC. inv ACC.
      assert(T: ∃ fr cr x, r0 = fr ⋅ cr ⋅ x ⋅ mr_tgt0 ⋅ fr_tgt0 ∧ FR fr ∧ COND cr).
      { rr in IPROP. uipropall. des; ss. clarify. rr in IPROP4. uipropall.
        rr in IPROP4. des; clarify. rr in IPROP6. uipropall. rr in IPROP6. des; clarify.
        esplits; et. instantiate (1:=ctx ⋅ ctx0 ⋅ b2). r_solve. }
      des; ss. clarify. clear IPROP.
      exists cr. steps.
      unfold mget, assume. steps. esplits.
      { eapply URA.updatable_wf; et. etrans; et.
        eapply URA.extends_updatable. exists (x ⋅ fr). r_solve. }
      steps.
      esplits; et. steps.
      eapply POST; et.
      { econs; et. rr. uipropall. esplits; revgoals; try (by rr; uipropall; refl); revgoals.
        { instantiate (1:=fr ⋅ x). r_solve. }
        eapply iProp_mono; et.
        - eapply URA.updatable_wf; et. etrans; et.
          eapply URA.extends_updatable; et. exists (cr ⋅ mr_tgt0 ⋅ fr_tgt0). r_solve.
        - exists x. r_solve.
      }
    }
  Qed.

  Lemma hassume_tgt_clo
          A a (le: A -> A -> Prop)
          (R: A -> Any.t -> Any.t -> iProp)
          (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
          r rg m n mp_src0 mp_tgt mr_tgt0 itr_src ktr_tgt (mr_src0: Σ)
          (COND: iProp) fr_src fr_tgt0 FR
          (ACC: current_iProp (fr_src ⋅ mr_src0)
                  (COND ** FR ** OwnT (fr_tgt0) ** OwnT mr_tgt0))
          (POST: forall (fr_tgt1: Σ)
                        (ACC: current_iProp (fr_src ⋅ mr_src0)
                                (FR ** OwnT (fr_tgt1) ** OwnT mr_tgt0)),
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m true a
             (Any.pair mp_src0 mr_src0↑, itr_src)
             (Any.pair mp_tgt mr_tgt0↑, ktr_tgt (fr_tgt1, tt)))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0↑, itr_src)
             (Any.pair mp_tgt mr_tgt0↑, handle_condE_tgt (Cassume COND) fr_tgt0 >>= ktr_tgt)
  .
  Proof.
    eapply hassume_tgt_clo_strong; et.
    i. eapply POST; et. eapply current_iProp_entail; et. iIntros; iDes; iFrame.
    iSplitL "H2"; et.
  Qed.

  Lemma hassert_tgt_clo
          A a (le: A -> A -> Prop)
          (R: A -> Any.t -> Any.t -> iProp)
          (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
          r rg m n mp_src0 mp_tgt mr_tgt0 itr_src ktr_tgt (mr_srctgt: Σ)
          (COND: iProp) fr_src fr_tgt0 FR
          (ACC: current_iProp (fr_src ⋅ mr_srctgt)
                  (FR ** OwnT fr_tgt0 ** OwnT mr_tgt0))
          (POST: forall (mr_tgt1 fr_tgt1: Σ)
                        (ACC: current_iProp (fr_src ⋅ mr_srctgt)
                                (COND ** FR ** OwnT fr_tgt1 ** OwnT mr_tgt1)),
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m true a
             (Any.pair mp_src0 mr_srctgt↑, itr_src)
             (Any.pair mp_tgt mr_tgt1↑, ktr_tgt (fr_tgt1, tt)))
    :
      gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_srctgt↑, itr_src)
             (Any.pair mp_tgt mr_tgt0↑, handle_condE_tgt (Cassert COND) fr_tgt0 >>= ktr_tgt)
  .
  Proof.
    { steps. unfold mput, mget. des_ifs. steps. unfold guarantee. steps.
      eapply POST; ss; et.
      { eapply current_iProp_upd. eapply current_iProp_entail; et.
        iIntros. iDes. iFrame.
        unfold OwnT.
        iCombineAll. rewrite Own_Upd; et. iMod "H2". iDestruct "H2" as "[[A B] C]".
        iModIntro. iFrame.
        - iStopProof. clear - x0. uipropall. ii. rr in H. des; subst.
          eapply iProp_mono; et. exists ctx; refl.
      }
    }
  Qed.

  (* Lemma harg_clo2 *)
  (*       A *)
  (*       mn r rg *)
  (*       X_src (P_src: option mname -> X_src -> Any.t -> Any.t -> iProp) *)
  (*       X_tgt (P_tgt: option mname -> X_tgt -> Any.t -> Any.t -> iProp) *)
  (*       argp *)
  (*       mp_src mp_tgt (mr_src mr_tgt: Σ) k_src k_tgt *)
  (*       a (le: A -> A -> Prop) *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)
  (*       (WF: mk_wf R a ((Any.pair mp_src mr_src↑), (Any.pair mp_tgt mr_tgt↑))) *)
  (*       m n *)
  (*       (ARG: forall x_src varg_src, exists x_tgt, *)
  (*           <<SEP: (R a mp_src mp_tgt ** P_src mn x_src varg_src argp) ⊢ *)
  (*                    (#=> ∃ varg_tgt FR, (P_tgt mn x_tgt varg_tgt argp ** FR ** ⌜(<<SIM: forall mr_src' fr_src fr_tgt *)
  (*                 (TGT: P_tgt mn x_tgt varg_tgt argp fr_tgt) *)
  (*                 (ACC: current_iPropL (fr_src ⋅ (mr_tgt ⋅ mr_src')) *)
  (*                                      [("FR", FR); ("TF", OwnT fr_tgt); ("TM", OwnT mr_tgt)]), *)
  (*               gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr true true a *)
  (*                      (Any.pair mp_src (mr_tgt ⋅ mr_src')↑, k_src (fr_src, ((mn, x_src), varg_src))) *)
  (*                      (Any.pair mp_tgt mr_tgt↑, k_tgt (fr_tgt, ((mn, x_tgt), varg_tgt)))>>)⌝))>> *)
  (*       ) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a *)
  (*            ((Any.pair mp_src mr_src↑), (HoareFunArg P_src (mn, argp) >>= k_src)) *)
  (*            ((Any.pair mp_tgt mr_tgt↑), (HoareFunArg P_tgt (mn, argp) >>= k_tgt)) *)
  (* . *)
  (* Proof. *)
  (*   inv WF. apply_all_once Any.pair_inj. des. subst. apply_all_once Any.upcast_inj. des; subst. clear_fast. *)
  (*   unfold HoareFunArg, ASSUME, ASSERT, mput, mget, assume, guarantee. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). intro x_src. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). intro fr_src. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). intro VALID. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). intro arg_src. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). intro PRE. *)
  (*   specialize (ARG x_src arg_src). des. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists x_tgt. *)
  (*   exploit RSRC; et. *)
  (*   { eapply URA.wf_mon. instantiate (1:=fr_src ⋅ mr_tgt). r_wf VALID. } *)
  (*   i; des. *)
  (*   assert(T: current_iPropL (fr_src ⋅ mr_src') [("A", (Own (fr_src ⋅ mr_src')))]). *)
  (*   { eapply current_iPropL_init. *)
  (*     { eapply URA.wf_mon. instantiate (1:=mr_tgt). r_wf VALID. } *)
  (*   } *)
  (*   assert(U: Own fr_src ∗ Own mr_src' ⊢ R a mp_src mp_tgt ** P_src mn x_src arg_src argp). *)
  (*   { clear - PRE x0. uipropall. i. des; subst. esplits. *)
  (*     { rewrite URA.add_comm. refl. } *)
  (*     { eapply iProp_mono; eauto. eapply URA.wf_mon. instantiate (1:=a0). r_wf WF. } *)
  (*     { eapply iProp_mono; eauto. eapply URA.wf_mon. instantiate (1:=b). r_wf WF. } *)
  (*   } *)
  (*   mAssert _%I with "A". *)
  (*   { iDestruct "A" as "[A B]". instantiate (1:=(Own fr_src ∗ Own mr_src')%I). iFrame. } *)
  (*   mAssert _%I with "A1". *)
  (*   { iStopProof. etrans; eauto. } *)
  (*   clear SEP U. mUpd "A". mDesAll. *)
  (*   inv T. rr in IPROP. uipropall. des; subst. *)
  (*   rename a0 into varg_tgt. rename a3 into fr_tgt. rename a1 into FR. rename a2 into fr_src'. clear GWF. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists fr_tgt. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto. *)
  (*   { eapply URA.updatable_wf; et. rewrite ! URA.unit_id. *)
  (*     replace (fr_src ⋅ (mr_tgt ⋅ mr_src')) with ((fr_src ⋅ mr_src') ⋅ mr_tgt) by r_solve. *)
  (*     eapply URA.updatable_add; et; try refl. *)
  (*     etrans; et. eapply URA.extends_updatable. *)
  (*     exists (fr_src' ⋅ b0). r_solve. } *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists varg_tgt. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *)
  (*   ired_both. *)
  (*   eapply PURE. *)
  (*   { rewrite URA.unit_id. ss. } *)
  (*   unshelve eassert(T:=@current_iPropL_init (fr_src ⋅ mr_src' ⋅ mr_tgt) "N" _). *)
  (*   { r_wf VALID. } *)
  (*   mAssert (#=> (FR ** OwnT fr_tgt ** OwnT mr_tgt)) with "N". *)
  (*   { iDestruct "N" as "[A B]". iFrame. *)
  (*     iDestruct (Own_Upd with "A") as "T". *)
  (*     { r; et. } *)
  (*     iMod "T". iDestruct "T" as "[A [B _]]". iFrame. *)
  (*     iStopProof. eapply from_semantic; et. *)
  (*   } *)
  (*   mUpd "A". mDesAll. mRename "A1" into "TM". mRename "A2" into "TF". mRename "A" into "FR". ss. *)
  (*   rewrite ! URA.unit_id. *)
  (*   replace (fr_src ⋅ (mr_tgt ⋅ mr_src')) with (fr_src ⋅ mr_src' ⋅ mr_tgt) by r_solve. ss. *)
  (* Qed. *)

  (* (*** TODO: update the one in IPM.v ***) *)
  (* Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a) *)
  (*   : *)
  (*     bi_entails (Own a) (P). *)
  (* Proof. *)
  (*   uipropall. ss. i. eapply iProp_mono; et. *)
  (* Qed. *)

  (* (*** TODO: move to IPM.v ***) *)
  (* Lemma to_semantic_pure: forall (P: Prop), (bi_emp_valid ((⌜P⌝)%I: iProp)) -> P. *)
  (* Proof. *)
  (*   i. rr in H. uipropall. exploit (H ε); eauto. *)
  (*   { eapply URA.wf_unit. } *)
  (*   { rr. uipropall. } *)
  (*   { i. rr in x0. uipropall. } *)
  (* Qed. *)

  (* (*** Just for proof reuse. ***) *)
  (* Definition HoareCall_ *)
  (*            (mn: mname) *)
  (*            (tbr: bool) *)
  (*            (ord_cur: ord) *)
  (*            (fsp: fspec) (x: fsp.(meta)): *)
  (*   gname -> Any.t -> stateT (Σ) (itree Es) Any.t := *)
  (*   fun fn varg_src fr0 => *)

  (*     '(fr1, varg_tgt) <- (ASSERT (fsp.(precond) (Some mn) x) varg_src fr0);; *)

  (*     let ord_next := fsp.(measure) x in *)
  (*     _ <- guarantee(ord_lt ord_next ord_cur /\ (tbr = true -> is_pure ord_next) /\ (tbr = false -> ord_next = ord_top));; *)

  (*     vret_tgt <- trigger (Call fn varg_tgt);; *)

  (*     ASSUME (fsp.(postcond) (Some mn) x) vret_tgt fr1 *)
  (* . *)

  (* Lemma HoareCall_spec: forall mn tbr ord_cur fsp fn varg fr0, *)
  (*     HoareCall mn tbr ord_cur fsp fn varg fr0 = *)
  (*       x <- trigger (Choose (fsp.(meta)));; HoareCall_ mn tbr ord_cur fsp x fn varg fr0 *)
  (* . *)
  (* Proof. *)
  (*   unfold HoareCall, HoareCall_. grind. *)
  (* Qed. *)

  (* Lemma hcall_clo2_ *)
  (*       (fsp_src: fspec) *)

  (*       A (a0: shelve__ A) *)

  (*       (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0 *)
  (*       `{PreOrder _ le} *)
  (*       (fsp_tgt: fspec) *)
  (*       mr_tgt0 mp_tgt0 k_tgt k_src *)
  (*       fn tbr_src tbr_tgt o_src o_tgt arg_src arg_tgt *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)

  (*       fr_src0 fr_tgt0 *)

  (*       x_src x_tgt *)
  (*       (ORD: (<<PURE: ord_lt (fsp_src.(measure) x_src) o_src /\ *)
  (*              (tbr_src = true -> is_pure (fsp_src.(measure) x_src)) /\ *)
  (*                (tbr_src = false -> (fsp_src.(measure) x_src) = ord_top)>>)) *)
  (*       (POST: *)
  (*         exists I FR, *)
  (*           (<<ACC: current_iPropL (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) [("I", I)] >>) /\ *)
  (*           (<<UPDATABLE: bi_entails I (OwnT (fr_tgt0) ** OwnT (mr_tgt0) ** *)
  (*                             (∀ argp, fsp_tgt.(precond) (Some mn) x_tgt arg_tgt argp *)
  (*                                ==∗ (FR ** (∃ a1, R a1 mp_src0 mp_tgt0 ** ⌜le a0 a1⌝) ** *)
  (*                                        (fsp_src.(precond) (Some mn) x_src arg_src argp: iProp))))>>) /\ *)
  (*           (<<POST: forall (ret_src: Any.t) (mp_src1 mp_tgt1 : Any.t), *)
  (*             (<<UPDATABLE: ∀ retp, (FR ** (∃ a1, R a1 mp_src1 mp_tgt1 ** ⌜le a0 a1⌝) ** *)
  (*                                         fsp_src.(postcond) (Some mn) x_src ret_src retp) ==∗ *)
  (*                           ∃ ret_tgt J, (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt retp ** J ** *)
  (*                  ⌜(<<SIM: forall fr_src1 fr_tgt1 (TGT: fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt retp fr_tgt1) mr_src1 mr_tgt1 *)
  (*                             (ACC: current_iPropL (fr_src1 ⋅ (mr_tgt1 ⋅ mr_src1)) *)
  (*                                                  [("J", J); ("TF", OwnT fr_tgt1); ("TM", OwnT mr_tgt1)]), *)
  (*               gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a *)
  (*                      (Any.pair mp_src1 (mr_tgt1 ⋅ mr_src1)↑, k_src (fr_src1, ret_src)) *)
  (*                      (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (fr_tgt1, ret_tgt))>>)⌝)>>) *)
  (*               >>)) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a *)
  (*            (Any.pair mp_src0 (mr_tgt0 ⋅ mr_src0)↑, *)
  (*                      (HoareCall_ mn tbr_src o_src fsp_src x_src fn arg_src) fr_src0 >>= k_src) *)
  (*            (Any.pair mp_tgt0 mr_tgt0↑, *)
  (*                      (HoareCall_ mn tbr_tgt o_tgt fsp_tgt x_tgt fn arg_tgt) fr_tgt0 >>= k_tgt) *)
  (* . *)
  (* Proof. *)
  (*   subst. unfold HoareCall_ at 2, ASSUME, ASSERT, mput, mget, assume, guarantee. *)
  (*   steps. *)
  (*   rename c into mr_tgt1. rename c0 into ro_tgt. rename c1 into fr_tgt. *)
  (*   des. *)
  (*   eapply (current_iPropL_entail "I") in ACC; et. unfold alist_add in ACC; ss. *)
  (*   mDesAll. *)
  (*   mAssert (Own (fr_tgt0 ⋅ mr_tgt0))%I with "I A1" as "H". *)
  (*   { iSplitL "I"; iFrame. } *)
  (*   mAssert _ with "H" as "H". *)
  (*   { iApply (Own_Upd with "H"); eauto. } *)
  (*   mUpd "H". *)
  (*   mAssert _ with "H" as "H". *)
  (*   { iDestruct "H" as "[[A B] C]". instantiate (1:=_ ** _ ** _). *)
  (*     iSplitR "A"; try iAssumption. iSplitR "B"; try iAssumption. } *)
  (*   mDesAll. *)
  (*   mAssert (_) with "A1". *)
  (*   { iStopProof. eapply from_semantic; eauto. } *)
  (*   mAssert (#=> _) with "A A3". *)
  (*   { iSpecialize ("A" with "A3"). iMod "A". iModIntro. iAssumption. *)
  (*   } *)
  (*   mUpd "A1". mDesAll. *)

  (*   inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss). *)
  (*   des. subst. rename a2 into mr_src1. rename a3 into fr_src. *)
  (*   rename a4 into ro_src. rename a5 into fr_tgt_. rename a6 into mr_tgt_. *)
  (*   unfold HoareCall_ at 1, ASSUME, ASSERT, mput, mget, assume, guarantee. *)
  (*   steps. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists (ro_src, (fr_src ⋅ fr_tgt), (mr_tgt1 ⋅ mr_src1)). *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits. *)
  (*   { replace (fr_src0 ⋅ (mr_tgt0 ⋅ mr_src0)) with (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) by r_solve. etrans; et. *)
  (*     rr in IPROP6. rr in IPROP8. des. subst. *)
  (*     eapply URA.extends_updatable. exists (b3 ⋅ ctx0 ⋅ ctx); r_solve. } *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). esplits; et. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). econs; et. *)
  (*   bar. *)
  (*   i. steps. rename x5 into ri_src. rename t into mp_src2. rename c into mr_src2. *)
  (*   rename x7 into ret_src. rename vret into retp. *)
  (*   inv WF. rewrite Any.pair_split in *. clarify. rewrite Any.upcast_downcast in *. clarify. *)
  (*   move POST at bottom. *)
  (*   specialize (POST ret_src mp_src2 mp_tgt). des. *)
  (*   assert(T: URA.wf (ri_src ⋅ fr_src ⋅ mr_src')). *)
  (*   { eapply URA.wf_mon; et. instantiate (1:= fr_tgt ⋅ mr_tgt). r_wf x6. } *)
  (*   assert(ACC:=current_iPropL_init "A" T). *)
  (*   mAssert (_ ∗ _ ∗ _)%I with "A". *)
  (*   { iDestruct "A" as "[[A B] C]". iSplitL "A"; try iAssumption. iSplitL "B"; try iAssumption. } *)
  (*   mDesAll. *)
  (*   mAssert (_) with "A". *)
  (*   { iStopProof. eapply from_semantic; et. } *)
  (*   mAssert (_) with "A1". *)
  (*   { iStopProof. eapply from_semantic; et. } *)
  (*   mAssert (_) with "A2". *)
  (*   { iStopProof. eapply from_semantic; et. eapply RSRC; et. eapply URA.wf_mon. *)
  (*     instantiate (1:=ri_src ⋅ fr_src ⋅ fr_tgt ⋅ mr_tgt). r_wf x6. *)
  (*   } *)
  (*   specialize (POST retp). *)
  (*   eapply current_iProp_entail in ACC; cycle 1. *)
  (*   { etrans; try eassumption. iIntros "H". iDestruct "H" as "[A [B [C _]]]". iFrame. iSplits; et. *)
  (*     iPureIntro. etrans; eauto. } *)
  (*   apply current_iProp_upd in ACC. apply current_iProp_ex in ACC. des. apply current_iProp_ex in ACC. des. *)
  (*   rename x5 into ret_tgt. rename x7 into J. *)
  (*   inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss). *)
  (*   des. subst. *)
  (*   rename a3 into ri_tgt. rename b0 into jr. rename b into unused. *)
  (*   assert(WF: URA.wf (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt))). *)
  (*   { eapply URA.updatable_wf; try apply x6. *)
  (*     replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src')) with *)
  (*       ((fr_tgt ⋅ mr_tgt) ⋅ (ri_src ⋅ fr_src ⋅ mr_src')) by r_solve. *)
  (*     replace (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt)) with ((fr_tgt ⋅ mr_tgt) ⋅ (ri_tgt ⋅ jr)) by r_solve. *)
  (*     eapply URA.updatable_add; et; try refl. etrans; et. eapply URA.extends_updatable. *)
  (*     exists unused; r_solve. } *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists ri_tgt. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *)
  (*   { eapply URA.wf_mon. instantiate (1:=jr). r_wf WF. } *)
  (*   steps. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists ret_tgt. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *)
  (*   steps. *)
  (*   rename IPROP3 into SIM. *)
  (*   rr in SIM; repeat (autorewrite with iprop in SIM; autounfold with iprop in SIM; ss). des. *)
  (*   eapply SIM. *)
  (*   { eapply iProp_mono; et. *)
  (*     - eapply URA.wf_extends; et. exists (jr ⋅ mr_tgt). r_solve. *)
  (*     - exists fr_tgt. r_solve. } *)
  (*   econs; et; cycle 1. *)
  (*   { replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src')) *)
  (*       with ((ri_src ⋅ fr_src ⋅ mr_src') ⋅ (fr_tgt ⋅ mr_tgt)) by r_solve. *)
  (*     eapply URA.updatable_add. *)
  (*     { etrans; try apply UPD0. eapply URA.extends_updatable. *)
  (*       instantiate (1:=ri_tgt ⋅ jr). exists unused; r_solve. } refl. } *)
  (*   { eapply to_semantic; cycle 1. *)
  (*     { r_wf WF. } *)
  (*     iIntros "[[A B] [C D]]". iSplitL "B". *)
  (*     { iStopProof. eapply from_semantic; et. } *)
  (*     iFrame. iSplitL "A"; iFrame. *)
  (*   } *)
  (* Qed. *)

  (* Lemma hcall_clo2 *)
  (*       (fsp_src: fspec) *)

  (*       A (a0: shelve__ A) *)

  (*       (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0 *)
  (*       `{PreOrder _ le} *)
  (*       (fsp_tgt: fspec) *)
  (*       mr_tgt0 mp_tgt0 k_tgt k_src *)
  (*       fn tbr_src tbr_tgt o_src o_tgt arg_src arg_tgt *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)

  (*       fr_src0 fr_tgt0 *)

  (*       (POST: forall x_tgt (PURE: ord_lt (fsp_tgt.(measure) x_tgt) o_tgt *)
  (*                                  /\ (tbr_tgt = true -> is_pure (fsp_tgt.(measure) x_tgt)) *)
  (*                                  /\ (tbr_tgt = false -> (fsp_tgt.(measure) x_tgt) = ord_top)), *)
  (*         exists x_src, *)
  (*           (<<PURE: ord_lt (fsp_src.(measure) x_src) o_src /\ *)
  (*              (tbr_src = true -> is_pure (fsp_src.(measure) x_src)) /\ *)
  (*                (tbr_src = false -> (fsp_src.(measure) x_src) = ord_top)>>) /\ *)
  (*         exists I FR, *)
  (*           (<<ACC: current_iPropL (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) [("I", I)] >>) /\ *)
  (*           (<<UPDATABLE: bi_entails I (OwnT (fr_tgt0) ** OwnT (mr_tgt0) ** *)
  (*                             (∀ argp, fsp_tgt.(precond) (Some mn) x_tgt arg_tgt argp *)
  (*                                ==∗ (FR ** (∃ a1, R a1 mp_src0 mp_tgt0 ** ⌜le a0 a1⌝) ** *)
  (*                                        (fsp_src.(precond) (Some mn) x_src arg_src argp: iProp))))>>) /\ *)
  (*           (<<POST: forall (ret_src: Any.t) (mp_src1 mp_tgt1 : Any.t), *)
  (*             (<<UPDATABLE: ∀ retp, (FR ** (∃ a1, R a1 mp_src1 mp_tgt1 ** ⌜le a0 a1⌝) ** *)
  (*                                         fsp_src.(postcond) (Some mn) x_src ret_src retp) ==∗ *)
  (*                           ∃ ret_tgt J, (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt retp ** J ** *)
  (*                  ⌜(<<SIM: forall fr_src1 fr_tgt1 (TGT: fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt retp fr_tgt1) mr_src1 mr_tgt1 *)
  (*                             (ACC: current_iPropL (fr_src1 ⋅ (mr_tgt1 ⋅ mr_src1)) *)
  (*                                                  [("J", J); ("TF", OwnT fr_tgt1); ("TM", OwnT mr_tgt1)]), *)
  (*               gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a *)
  (*                      (Any.pair mp_src1 (mr_tgt1 ⋅ mr_src1)↑, k_src (fr_src1, ret_src)) *)
  (*                      (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (fr_tgt1, ret_tgt))>>)⌝)>>) *)
  (*               >>)) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a *)
  (*            (Any.pair mp_src0 (mr_tgt0 ⋅ mr_src0)↑, *)
  (*                      (HoareCall mn tbr_src o_src fsp_src fn arg_src) fr_src0 >>= k_src) *)
  (*            (Any.pair mp_tgt0 mr_tgt0↑, *)
  (*                      (HoareCall mn tbr_tgt o_tgt fsp_tgt fn arg_tgt) fr_tgt0 >>= k_tgt) *)
  (* . *)
  (* Proof. *)
  (*   rewrite ! HoareCall_spec. *)
  (*   steps. rename x into x_tgt. *)
  (*   destruct (classic (ord_lt (measure fsp_tgt x_tgt) o_tgt *)
  (*                      ∧ (tbr_tgt = true → is_pure (measure fsp_tgt x_tgt)) *)
  (*                      ∧ (tbr_tgt = false → measure fsp_tgt x_tgt = ord_top))); cycle 1. *)
  (*   { unfold HoareCall_ at 2. steps. unfold ASSERT, mput, mget. steps. } *)
  (*   spc POST. spc POST. des. *)
  (*   force_l. exists x_src. *)
  (*   eapply hcall_clo2_; eauto. *)
  (* Qed. *)

  (* (* Lemma hcall_clo2 *) *)
  (* (*       (fsp_src: fspec) *) *)

  (* (*       A (a0: shelve__ A) *) *)

  (* (*       (le: A -> A -> Prop) mn r rg a n m mr_src0 mp_src0 *) *)
  (* (*       `{PreOrder _ le} *) *)
  (* (*       (fsp_tgt: fspec) *) *)
  (* (*       mr_tgt0 mp_tgt0 k_tgt k_src *) *)
  (* (*       fn tbr_src tbr_tgt o_src o_tgt arg_src arg_tgt *) *)
  (* (*       (R: A -> Any.t -> Any.t -> iProp) *) *)
  (* (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *) *)

  (* (*       fr_src0 fr_tgt0 *) *)

  (* (*       (POST: forall x_tgt (PURE: ord_lt (fsp_tgt.(measure) x_tgt) o_tgt *) *)
  (* (*                                  /\ (tbr_tgt = true -> is_pure (fsp_tgt.(measure) x_tgt)) *) *)
  (* (*                                  /\ (tbr_tgt = false -> (fsp_tgt.(measure) x_tgt) = ord_top)), *) *)
  (* (*         exists x_src, *) *)
  (* (*           (<<PURE: ord_lt (fsp_src.(measure) x_src) o_src /\ *) *)
  (* (*              (tbr_src = true -> is_pure (fsp_src.(measure) x_src)) /\ *) *)
  (* (*                (tbr_src = false -> (fsp_src.(measure) x_src) = ord_top)>>) /\ *) *)
  (* (*         exists I FR, *) *)
  (* (*           (<<ACC: current_iPropL (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) [("I", I)] >>) /\ *) *)
  (* (*           (<<UPDATABLE: bi_entails I (OwnT (fr_tgt0) ** OwnT (mr_tgt0) ** *) *)
  (* (*                             (∀ argp, fsp_tgt.(precond) (Some mn) x_tgt arg_tgt argp *) *)
  (* (*                                ==∗ (FR ** (∃ a1, R a1 mp_src0 mp_tgt0 ** ⌜le a0 a1⌝) ** *) *)
  (* (*                                        (fsp_src.(precond) (Some mn) x_src arg_src argp: iProp))))>>) /\ *) *)
  (* (*           (<<POST: forall (ret_src: Any.t) (mp_src1 mp_tgt1 : Any.t), *) *)
  (* (*             (<<UPDATABLE: ∀ retp, (FR ** (∃ a1, R a1 mp_src1 mp_tgt1 ** ⌜le a0 a1⌝) ** *) *)
  (* (*                                         fsp_src.(postcond) (Some mn) x_src ret_src retp) ==∗ *) *)
  (* (*                           ∃ ret_tgt J, (fsp_tgt.(postcond) (Some mn) x_tgt ret_tgt retp ** J ** *) *)
  (* (*                  ⌜(<<SIM: forall fr_src1 fr_tgt1 mr_src1 mr_tgt1 *) *)
  (* (*                             (ACC: current_iPropL (fr_src1 ⋅ (mr_tgt1 ⋅ mr_src1)) *) *)
  (* (*                                                  [("J", J); ("TF", OwnT fr_tgt1); ("TM", OwnT mr_tgt1)]), *) *)
  (* (*               gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true a *) *)
  (* (*                      (Any.pair mp_src1 (mr_tgt1 ⋅ mr_src1)↑, k_src (fr_src1, ret_src)) *) *)
  (* (*                      (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (fr_tgt1, ret_tgt))>>)⌝)>>) *) *)
  (* (*               >>)) *) *)
  (* (*   : *) *)
  (* (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a *) *)
  (* (*            (Any.pair mp_src0 (mr_tgt0 ⋅ mr_src0)↑, *) *)
  (* (*                      (HoareCall mn tbr_src o_src fsp_src fn arg_src) fr_src0 >>= k_src) *) *)
  (* (*            (Any.pair mp_tgt0 mr_tgt0↑, *) *)
  (* (*                      (HoareCall mn tbr_tgt o_tgt fsp_tgt fn arg_tgt) fr_tgt0 >>= k_tgt) *) *)
  (* (* . *) *)
  (* (* Proof. *) *)
  (* (*   subst. unfold HoareCall at 2, ASSUME, ASSERT, mput, mget, assume, guarantee. *) *)
  (* (*   steps. *) *)
  (* (*   rename c into mr_tgt1. rename c0 into ro_tgt. rename c1 into fr_tgt. *) *)
  (* (*   rename x into x_tgt. des. specialize (POST x_tgt (conj x3 (conj x4 x5))). des. *) *)
  (* (*   eapply (current_iPropL_entail "I") in ACC; et. unfold alist_add in ACC; ss. *) *)
  (* (*   mDesAll. *) *)
  (* (*   mAssert (Own (fr_tgt0 ⋅ mr_tgt0))%I with "I A1" as "H". *) *)
  (* (*   { iSplitL "I"; iFrame. } *) *)
  (* (*   mAssert _ with "H" as "H". *) *)
  (* (*   { iApply (Own_Upd with "H"); eauto. } *) *)
  (* (*   mUpd "H". *) *)
  (* (*   mAssert _ with "H" as "H". *) *)
  (* (*   { iDestruct "H" as "[[A B] C]". instantiate (1:=_ ** _ ** _). *) *)
  (* (*     iSplitR "A"; try iAssumption. iSplitR "B"; try iAssumption. } *) *)
  (* (*   mDesAll. *) *)
  (* (*   mAssert (_) with "A1". *) *)
  (* (*   { iStopProof. eapply from_semantic; eauto. } *) *)
  (* (*   mAssert (#=> _) with "A A3". *) *)
  (* (*   { iSpecialize ("A" with "A3"). iMod "A". iModIntro. iAssumption. *) *)
  (* (*   } *) *)
  (* (*   mUpd "A1". mDesAll. *) *)

  (* (*   inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss). *) *)
  (* (*   des. subst. rename a2 into mr_src1. rename a3 into fr_src. *) *)
  (* (*   rename a4 into ro_src. rename a5 into fr_tgt_. rename a6 into mr_tgt_. *) *)
  (* (*   unfold HoareCall at 1, ASSUME, ASSERT, mput, mget, assume, guarantee. *) *)
  (* (*   steps. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). esplits; et. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists (ro_src, (fr_src ⋅ fr_tgt), (mr_tgt1 ⋅ mr_src1)). *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits. *) *)
  (* (*   { replace (fr_src0 ⋅ (mr_tgt0 ⋅ mr_src0)) with (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) by r_solve. etrans; et. *) *)
  (* (*     rr in IPROP6. rr in IPROP8. des. subst. *) *)
  (* (*     eapply URA.extends_updatable. exists (b3 ⋅ ctx0 ⋅ ctx); r_solve. } *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). esplits; et. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). econs; et. *) *)
  (* (*   bar. *) *)
  (* (*   i. steps. rename x into ri_src. rename t into mp_src2. rename c into mr_src2. *) *)
  (* (*   rename x7 into ret_src. rename vret into retp. *) *)
  (* (*   inv WF. rewrite Any.pair_split in *. clarify. rewrite Any.upcast_downcast in *. clarify. *) *)
  (* (*   move POST at bottom. *) *)
  (* (*   specialize (POST ret_src mp_src2 mp_tgt). des. *) *)
  (* (*   assert(T: URA.wf (ri_src ⋅ fr_src ⋅ mr_src')). *) *)
  (* (*   { eapply URA.wf_mon; et. instantiate (1:= fr_tgt ⋅ mr_tgt). r_wf x6. } *) *)
  (* (*   assert(ACC:=current_iPropL_init "A" T). *) *)
  (* (*   mAssert (_ ∗ _ ∗ _)%I with "A". *) *)
  (* (*   { iDestruct "A" as "[[A B] C]". iSplitL "A"; try iAssumption. iSplitL "B"; try iAssumption. } *) *)
  (* (*   mDesAll. *) *)
  (* (*   mAssert (_) with "A". *) *)
  (* (*   { iStopProof. eapply from_semantic; et. } *) *)
  (* (*   mAssert (_) with "A1". *) *)
  (* (*   { iStopProof. eapply from_semantic; et. } *) *)
  (* (*   mAssert (_) with "A2". *) *)
  (* (*   { iStopProof. eapply from_semantic; et. eapply RSRC; et. eapply URA.wf_mon. *) *)
  (* (*     instantiate (1:=ri_src ⋅ fr_src ⋅ fr_tgt ⋅ mr_tgt). r_wf x6. *) *)
  (* (*   } *) *)
  (* (*   specialize (POST retp). *) *)
  (* (*   eapply current_iProp_entail in ACC; cycle 1. *) *)
  (* (*   { etrans; try eassumption. iIntros "H". iDestruct "H" as "[A [B [C _]]]". iFrame. iSplits; et. *) *)
  (* (*     iPureIntro. etrans; eauto. } *) *)
  (* (*   apply current_iProp_upd in ACC. apply current_iProp_ex in ACC. des. apply current_iProp_ex in ACC. des. *) *)
  (* (*   rename x into ret_tgt. rename x7 into J. *) *)
  (* (*   inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss). *) *)
  (* (*   des. subst. *) *)
  (* (*   rename a3 into ri_tgt. rename b0 into jr. rename b into unused. *) *)
  (* (*   assert(WF: URA.wf (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt))). *) *)
  (* (*   { eapply URA.updatable_wf; try apply x6. *) *)
  (* (*     replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src')) with *) *)
  (* (*       ((fr_tgt ⋅ mr_tgt) ⋅ (ri_src ⋅ fr_src ⋅ mr_src')) by r_solve. *) *)
  (* (*     replace (ri_tgt ⋅ jr ⋅ (fr_tgt ⋅ mr_tgt)) with ((fr_tgt ⋅ mr_tgt) ⋅ (ri_tgt ⋅ jr)) by r_solve. *) *)
  (* (*     eapply URA.updatable_add; et; try refl. etrans; et. eapply URA.extends_updatable. *) *)
  (* (*     exists unused; r_solve. } *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists ri_tgt. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *) *)
  (* (*   { eapply URA.wf_mon. instantiate (1:=jr). r_wf WF. } *) *)
  (* (*   steps. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). exists ret_tgt. *) *)
  (* (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et. *) *)
  (* (*   steps. *) *)
  (* (*   rename IPROP3 into SIM. *) *)
  (* (*   rr in SIM; repeat (autorewrite with iprop in SIM; autounfold with iprop in SIM; ss). des. *) *)
  (* (*   eapply SIM. *) *)
  (* (*   econs; et; cycle 1. *) *)
  (* (*   { replace (ri_src ⋅ (fr_src ⋅ fr_tgt) ⋅ (mr_tgt ⋅ mr_src')) *) *)
  (* (*       with ((ri_src ⋅ fr_src ⋅ mr_src') ⋅ (fr_tgt ⋅ mr_tgt)) by r_solve. *) *)
  (* (*     eapply URA.updatable_add. *) *)
  (* (*     { etrans; try apply UPD0. eapply URA.extends_updatable. *) *)
  (* (*       instantiate (1:=ri_tgt ⋅ jr). exists unused; r_solve. } refl. } *) *)
  (* (*   { eapply to_semantic; cycle 1. *) *)
  (* (*     { r_wf WF. } *) *)
  (* (*     iIntros "[[A B] [C D]]". iSplitL "B". *) *)
  (* (*     { iStopProof. eapply from_semantic; et. } *) *)
  (* (*     iFrame. iSplitL "A"; iFrame. *) *)
  (* (*   } *) *)
  (* (* Qed. *) *)

  (* Lemma hret_clo2 *)
  (*       A *)
  (*       mn r rg n m mp_src mp_tgt (mr_src mr_tgt: Σ) a0 *)
  (*       Xs (Qs: option mname -> Xs -> Any.t -> Any.t -> iProp) *)
  (*       Xt (Qt: option mname -> Xt -> Any.t -> Any.t -> iProp) *)
  (*       xs xt vret_src vret_tgt *)
  (*       (le: A -> A -> Prop) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)

  (*       fr_src fr_tgt *)

  (*       I *)
  (*       (ACC: current_iPropL (fr_src ⋅ (mr_tgt ⋅ mr_src)) [("I", I)]) *)
  (*       (UPDATABLE: *)
  (*         bi_entails I (OwnT (fr_tgt) ** OwnT (mr_tgt) ** *)
  (*                            (∀ retp, Qt mn xt vret_tgt retp *)
  (*                                ==∗ ((∃ a, R a mp_src mp_tgt ** ⌜le a0 a⌝) *)
  (*                                       ** (Qs mn xs vret_src retp: iProp))))) *)
  (*       (EQ: forall mr_src mr_tgt a retp (WLE: le a0 a) *)
  (*                   (WF: mk_wf R a ((Any.pair mp_src mr_src), (Any.pair mp_tgt mr_tgt))), *)
  (*           eqr (Any.pair mp_src mr_src) (Any.pair mp_tgt mr_tgt) retp retp) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n a0 *)
  (*            (Any.pair mp_src (mr_tgt ⋅ mr_src)↑, (HoareFunRet Qs mn xs (fr_src, vret_src))) *)
  (*            (Any.pair mp_tgt mr_tgt↑, (HoareFunRet Qt mn xt (fr_tgt, vret_tgt))) *)
  (* . *)
  (* Proof. *)
  (*   subst. unfold HoareFunRet, ASSUME, ASSERT, mput, mget, guarantee. *)
  (*   steps. *)
  (*   rename c0 into ro_tgt. rename c into mr_tgt0. rename c1 into residue. *)
  (*   eapply current_iPropL_entail with (Hn:="I") in ACC; et. ss. unfold alist_add in *. ss. *)
  (*   mDesAll. *)
  (*   mAssert (#=> (_ ∗ _ ∗ _)) with "I A1". *)
  (*   { iCombine "I A1" as "A". iDestruct (Own_Upd with "A") as "A"; eauto. iMod "A". *)
  (*     iDestruct "A" as "[[A B] C]". iSplitL "A"; eauto. iSplitL "B"; eauto. } *)
  (*   mUpd "A2". mDesAll. *)
  (*   mAssert _ with "A2". *)
  (*   { iStopProof. eapply from_semantic; eauto. } *)
  (*   mAssert (#=> _) with "A A4". *)
  (*   { iSpecialize ("A" with "A4"). iAssumption. } *)
  (*   mUpd "A2". mDesAll. *)
  (*   inv ACC. rr in IPROP. repeat (autorewrite with iprop in IPROP; autounfold with iprop in IPROP; ss). *)
  (*   des. subst. *)
  (*   rename a1 into mr_src0. rename a2 into ro_src. rename a3 into mr_tgt0_. rename a4 into residue_. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). eexists (ro_src, ε, mr_tgt0 ⋅ mr_src0). *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits. *)
  (*   { etrans; et. eapply URA.extends_updatable. *)
  (*     rr in IPROP4. des; subst. exists (ctx ⋅ b2 ⋅ residue_). rewrite URA.unit_id. r_solve. } *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). esplits. *)
  (*   repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; eauto. *)
  (*   steps. eapply EQ; et. econs; et. *)
  (* Qed. *)

  (* Lemma current_iPropL_entail_all Hn fmr (l: iPropL) (P: iProp) *)
  (*       (ACC: current_iPropL fmr l) *)
  (*       (ENTAIL: from_iPropL l -∗ (bupd P)) *)
  (*   : *)
  (*     current_iPropL fmr [(Hn, P)]. *)
  (* Proof. *)
  (*   eapply current_iProp_upd. *)
  (*   eapply current_iProp_entail; et. *)
  (*   unfold from_iPropL at 2. etrans; et. (*** !!! ***) *)
  (*   iIntros "H". iMod "H". iModIntro. iFrame. *)
  (* Qed. *)

  (* (* Lemma current_iPropL_merge_all Hn ctx (l: iPropL) *) *)
  (* (*   : *) *)
  (* (*     current_iPropL ctx l <-> current_iPropL ctx [(Hn, from_iPropL l)]. *) *)
  (* (* Proof. *) *)
  (* (*   unfold current_iPropL. unfold from_iPropL at 2. *) *)
  (* (*   set (from_iPropL l) as x. *) *)
  (* (*   set (x ** emp) as y. *) *)
  (* (*   assert(x = y). *) *)
  (* (*   { subst y. uipropall. extensionality r. apply Axioms.prop_ext. split; i; et. *) *)
  (* (*     - esplits; et. { rewrite URA.unit_id; ss. } r. uipropall. *) *)
  (* (*     - des. clarify. ss. *) *)
  (* (*   Check (from_iPropL l). *) *)
  (* (*   Check (from_iPropL l ** emp). *) *)
  (* (*   assert((from_iPropL l): iProp = (from_iPropL l ** emp): iProp). *) *)
  (* (*   assert(from_iPropL l = from_iPropL l ** emp). *) *)
  (* (*   { } *) *)
  (* (*   f_equal. *) *)
  (* (*   eapply prop_ext. *) *)
  (* (*   eapply current_iProp_upd. *) *)
  (* (*   eapply current_iProp_entail; et. *) *)
  (* (*   unfold from_iPropL at 2. etrans; et. (*** !!! ***) *) *)
  (* (* Qed. *) *)

  (* Local Transparent APC. *)

  (* (*** TODO: also allow weakening? maybe not needed (could be derived)? ***) *)
  (* Definition stb_pure_incl (stb_tgt stb_src: string -> option fspec): Prop := *)
  (*   forall fn fsp (FIND: stb_tgt fn = Some fsp) x (PURE: is_pure (fsp.(measure) x)), *)
  (*     stb_src fn = Some fsp /\ IsIrr fsp *)
  (* . *)

  (* Local Transparent HoareCall. *)

  (* Definition ord_le (o0 o1: ord): Prop := *)
  (*   match o0, o1 with *)
  (*   | ord_pure o0, ord_pure o1 => (o0 <= o1)%ord *)
  (*   | _, ord_top => True *)
  (*   | ord_top, _ => False *)
  (*   end *)
  (* . *)

  (* Lemma ord_lt_le_lt: forall o0 o1 o2, ord_lt o0 o1 -> ord_le o1 o2 -> ord_lt o0 o2. *)
  (* Proof. *)
  (*   i. destruct o0, o1, o2; ss. eapply Ord.lt_le_lt; eauto. *)
  (* Qed. *)

  (* Lemma hAPC2 *)
  (*       A (a0: shelve__ A) mp_src0 mp_tgt0 (mr_src0 mr_tgt0: Σ) *)
  (*       mn r rg *)
  (*       k_src k_tgt *)
  (*       _a (le: A -> A -> Prop) *)
  (*       (R: A -> Any.t -> Any.t -> iProp) *)
  (*       (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop) *)
  (*       m n *)
  (*       `{PreOrder _ le} *)

  (*       fr_src0 fr_tgt0 *)

  (*       FR *)
  (*       (ACC: current_iPropL (fr_src0 ⋅ (mr_tgt0 ⋅ mr_src0)) *)
  (*                            [("TM", Own mr_tgt0); ("TF", Own fr_tgt0); *)
  (*                             ("I", (∃ a1, R a1 mp_src0 mp_tgt0 ** ⌜le a0 a1⌝)%I); ("FR", FR)]) *)
  (*       stb_src stb_tgt o_src o_tgt *)
  (*       (LE: ord_le o_tgt o_src) *)
  (*       (STBINCL: stb_pure_incl stb_tgt stb_src) *)
  (*       (*** TODO: we should be able to remove the above condition. ***) *)
  (*       (ARG: forall *)
  (*           (mr_src1 mr_tgt1: Σ) (mp_src1 mp_tgt1 : Any.t) *)
  (*           fr_src1 fr_tgt1 *)
  (*           (ACC: current_iPropL (fr_src1 ⋅ (mr_tgt1 ⋅ mr_src1)) *)
  (*                                [("TM", Own mr_tgt1); ("TF", Own fr_tgt1); *)
  (*                                 ("I", (∃ a1, R a1 mp_src1 mp_tgt1 ∗ ⌜le a0 a1⌝)%I); ("FR", FR)]), *)
  (*           gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) rg rg _ _ eqr true true _a *)
  (*                  (Any.pair mp_src1 (mr_tgt1 ⋅ mr_src1)↑, k_src (fr_src1, tt)) *)
  (*                  (Any.pair mp_tgt1 mr_tgt1↑, k_tgt (fr_tgt1, tt))) *)
  (*   : *)
  (*     gpaco8 (_sim_itree (mk_wf R) le) (cpn8 (_sim_itree (mk_wf R) le)) r rg _ _ eqr m n _a *)
  (*            (Any.pair mp_src0 (mr_tgt0 ⋅ mr_src0)↑, (interp_hCallE_tgt mn stb_src o_src APC fr_src0) >>= k_src) *)
  (*            (Any.pair mp_tgt0 mr_tgt0↑, (interp_hCallE_tgt mn stb_tgt o_tgt APC fr_tgt0) >>= k_tgt) *)
  (* . *)
  (* Proof. *)
  (*   subst. *)
  (*   unfold APC. steps. force_l. exists x. steps. *)
  (*   deflag. *)
  (*   (* Unset Printing Notations. *) *)
  (*   clear_until x. gen x o_src o_tgt fr_src0 fr_tgt0. gen mp_src0 mp_tgt0 mr_src0 mr_tgt0. gen a0. gcofix CIH. i. *)
  (*   { *)
  (*     rewrite unfold_APC. ired_both. *)
  (*     force_r. i. force_l. exists x0. *)
  (*     destruct x0. *)
  (*     - steps. eapply gpaco8_mon; et. *)
  (*     - steps. force_l. exists x0. steps. force_l; ss. steps. *)
  (*       rewrite ! HoareCall_spec. steps. rename x1 into x_tgt. *)
  (*       destruct (classic (is_pure (f.(measure) x_tgt))); cycle 1. *)
  (*       { unfold HoareCall_ at 1. unfold ASSUME, ASSERT, mput, mget. steps. des. contradict H0. eauto. } *)

  (*       assert(STB: stb_src s = Some f /\ IsIrr f). *)
  (*       { eapply STBINCL; et. } *)
  (*       des. *)
  (*       force_l. eexists (_, _). steps. rewrite STB. steps. instantiate (1:=t). *)

  (*       mDesAll. *)
  (*       rewrite HoareCall_spec. steps. force_l. exists x_tgt. *)
  (*       destruct (classic (ord_lt (measure f x_tgt) o_src *)
  (*                          ∧ (true = true → is_pure (measure f x_tgt)) ∧ *)
  (*                            (true = false → measure f x_tgt = ord_top))); cycle 1. *)
  (*       { unfold HoareCall_ at 2. unfold ASSUME, ASSERT, mput, mget. steps. des. contradict H1. *)
  (*         esplits; eauto.  eapply ord_lt_le_lt; eauto. } *)
  (*       eapply hcall_clo2_; eauto. *)
  (*       esplits; eauto. *)
  (*       { replace (fr_src0 ⋅ mr_src0 ⋅ mr_tgt0) with (fr_src0 ⋅ (mr_tgt0 ⋅ mr_src0)) by r_solve. *)
  (*         eapply current_iProp_entail; eauto. *)
  (*         iIntros "[A [B [C [D _]]]]". iFrame. iIntros. iFrame. iModIntro. *)
  (*         iSplitL "D"; try iAssumption. iSplits; eauto. } *)
  (*       i. iIntros "[[A B] C]". *)
  (*       iModIntro. iSplits; eauto. *)
  (*       { iFrame. iCombine "A B" as "A". iAssumption. } *)
  (*       iPureIntro. *)
  (*       i. steps. *)
  (*       move CIH at bottom. *)
  (*       deflag. gbase. mDesAll. eapply (CIH); et. *)
  (*       { eapply current_iProp_entail; eauto. iIntros "[A [B [C [D _]]]]". iFrame. iSplits; eauto. } *)
  (*   } *)
  (* Unshelve. all: try exact 0; ss. *)
  (* Qed. *)

End MODE.

