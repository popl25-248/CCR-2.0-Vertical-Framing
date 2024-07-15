Require Import HoareDef MapHeader MapM MapA SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import HoareFacts.
Require Import HTactics2 HSim2 ISim2 ProofMode IProofMode2 STB Invariant.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.
  Context `{Σ: GRA.t}.

  Context `{@GRA.inG MapRA0 Σ}.
  Context `{@GRA.inG MapRA1 Σ}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := Any.t * Any.t.

  Definition initial_map_r: @URA.car MapRA1 :=
    (Excl.unit, Auth.excl ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra) ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition black_map_r (f: Z -> Z): @URA.car MapRA1 :=
    (Excl.unit, Auth.black ((fun k => Excl.just (f k)): @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition unallocated_r (sz: Z): @URA.car MapRA1 :=
    (Excl.unit, Auth.white ((fun k =>
                               if (Z_gt_le_dec 0 k) then Excl.just 0%Z
                               else if (Z_gt_le_dec sz k) then Excl.unit else Excl.just 0%Z)
                             : @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition initial_map: iProp :=
    OwnM initial_map_r.

  Definition black_map (f: Z -> Z): iProp :=
    OwnM (black_map_r f).

  Definition unallocated (sz: Z): iProp :=
    OwnM (unallocated_r sz).

  Lemma unallocated_alloc (sz: nat)
    :
    unallocated sz -∗ (map_points_to sz 0 ** unallocated (Z.pos (Pos.of_succ_nat sz))).
  Proof.
    unfold map_points_to, unallocated. iIntros "H".
    replace (unallocated_r sz) with ((map_points_to_r sz 0) ⋅ (unallocated_r (S sz))).
    { ss. iDestruct "H" as "[H0 H1]". iFrame. }
    unfold unallocated_r, map_points_to_r. ur. f_equal.
    { ur. auto. }
    { ur. unfold Auth.white. f_equal. ur. extensionality k.
      ur. des_ifs; try by (exfalso; lia).
    }
  Qed.

  Lemma initial_map_initialize sz
    :
    initial_map -∗ (black_map (fun _ => 0%Z) ** initial_points_tos sz ** unallocated sz).
  Proof.
    induction sz.
    { ss. iIntros "H". unfold initial_map.
      replace initial_map_r with ((black_map_r (fun _ => 0%Z)) ⋅ (unallocated_r 0)).
      { iDestruct "H" as "[H0 H1]". iFrame. }
      { unfold initial_map_r, black_map_r, unallocated_r. ur. f_equal.
        { ur. auto. }
        { ur. f_equal. ur. extensionality k. ur. des_ifs. }
      }
    }
    { iIntros "H". iPoseProof (IHsz with "H") as "H". ss.
      iDes. iPoseProof (unallocated_alloc with "H1") as "A". iFrame. auto.
    }
  Qed.

  Lemma initial_map_no_points_to k v
    :
    initial_map -∗ map_points_to k v -∗ ⌜False⌝.
  Proof.
    unfold initial_map, map_points_to.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". exfalso. rr in H2. ur in H2. unseal "ra". des.
    rr in H3. ur in H3. unseal "ra". des.
    rr in H3. des. ur in H3. eapply equal_f with (x:=k) in H3.
    ur in H3. des_ifs.
  Qed.

  Lemma unallocated_range sz k v
    :
    unallocated sz -∗ map_points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
  Proof.
    unfold unallocated, map_points_to.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". iPureIntro. rr in H2. ur in H2. unseal "ra". des.
    rr in H3. ur in H3. unseal "ra".
    rr in H3. ur in H3. unseal "ra". specialize (H3 k).
    rr in H3. ur in H3. unseal "ra". des_ifs. lia.
  Qed.

  Lemma black_map_get f k v
    :
    black_map f -∗ map_points_to k v -∗ (⌜f k = v⌝).
  Proof.
    unfold black_map, map_points_to.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". iPureIntro. rr in H2. ur in H2. unseal "ra". des.
    rr in H3. ur in H3. unseal "ra". des.
    rr in H3. des. ur in H3. eapply equal_f with (x:=k) in H3.
    ur in H3. des_ifs.
  Qed.

  Lemma black_map_set f k w v
    :
    black_map f -∗ map_points_to k w -∗ #=> (black_map (fun n => if Z.eq_dec n k then v else f n) ** map_points_to k v).
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iPoseProof (OwnM_Upd with "H") as "H".
    { instantiate (1:=black_map_r (fun n => if Z.eq_dec n k then v else f n) ⋅ map_points_to_r k v).
      rr. i. ur in H2. ur. unseal "ra". des_ifs. des. split; auto.
      ur in H3. ur. des_ifs. des. rr in H3. des. split.
      { rr. exists ctx. ur in H3. ur. extensionality n.
        eapply equal_f with (x:=n) in H3. ur in H3. ur. des_ifs.
      }
      { ur. i. rr. ur. unseal "ra". ss. }
    }
    iMod "H". iDestruct "H" as "[H0 H1]". iFrame. auto.
  Qed.

  Require Import HTactics2 HSim2 ISim2 IProofMode2.

  Let wf :=
        (fun (_: unit) st_src st_tgt =>
           ((∃ f sz, ⌜st_src = f↑ /\ st_tgt = (Some (f, sz))↑⌝ ** black_map f ** unallocated sz) ∨ (initial_map ** ⌜st_src = (fun (_: Z) => 0%Z)↑ /\ st_tgt = (None: option ((Z -> Z) * Z))↑⌝))%I).

  (* Variable GlobalStbM: Sk.t -> gname -> option fspec. *)
  (* Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM. *)

  (* Variable GlobalStb: Sk.t -> gname -> option fspec. *)
  (* Hypothesis STB_set: forall sk, (GlobalStb sk) "set" = Some set_spec. *)

  (* Hypothesis PUREINCL: forall sk, stb_pure_incl (GlobalStbM sk) (GlobalStb sk). *)

  Notation "a ↑" := (Any.upcast a) (at level 9).
  Notation "a ↓" := (Any.downcast a) (at level 9).

  Local Existing Instance HasFreezeN.
  Theorem correct: gccr CondsB MapM.SMap MapA.SMap.
  Proof.
    eapply adequacy_isim2 with (I:=wf) (le:=top2); ss.
    i. esplits; ss.
    { econs. eapply to_semantic. iIntros; iDes. iRight. iFrame. auto. }
    econs; ss.
    { econs; [reflexivity|].
      iIntros. iDes. ss. iModIntro. iIntros. iDes. des; subst. iModIntro. iSplits; ss.
      iFrame. iSplits; ss.
      unfold MapM.initF, MapA.initF, cfunU, ccallU. steps. subst. steps.
      iIntros. subst. unfold inv_with. iDes.

      iDestruct "INV" as "[A|B]".
      { iDes. des; subst. clarify. rewrite Any.upcast_downcast in *. clarify. }
      des; subst. iModIntro. iSplits; ss. steps.
      iDes. des; subst.
      iDestruct (initial_map_initialize with "B") as "A". iDes.
      iFrame. iSplits; ss.
      iLeft. iSplits; ss. iFrame.
      iSplits; ss.
    }
    econs; ss.
    { econs; [reflexivity|].
      iIntros. iDes. ss. iModIntro. iIntros. iDes. iModIntro. iSplits; ss.
      des_ifs.
      unfold MapM.getF, MapA.getF, cfunU, ccallU. steps. iDes. des; subst.
      des_ifs. unfold inv_with. iDes. unfold unint in *. des_ifs; subst.
      rewrite Any.upcast_downcast in *. clarify. steps.

      iDestruct "INV" as "[A|B]".
      2:{ iExFalso; ss. iDes. iApply (initial_map_no_points_to with "B PRE"). }
      iDes. des; subst. clarify. rewrite Any.upcast_downcast in *. clarify. steps.
      iApply isim_assume_tgt. iSplit.
      { iApply (unallocated_range with "[A1]"); eauto. }
      steps.
      iAssert (⌜_⌝)%I as "%".
      { iApply (black_map_get with "A PRE"). }
      iIntros. iModIntro. iSplits; ss. iFrame. iSplits; ss.
      { iLeft. iSplits; ss. iFrame. iSplits; ss. }
      { subst. ss. }
    }
    econs; ss.
    { econs; [reflexivity|].
      iIntros. iDes. ss. iModIntro. iIntros. iDes. iModIntro. iSplits; ss.
      des_ifs.
      unfold MapM.setF, MapA.setF, cfunU, ccallU. steps. iDes. des; subst.
      des_ifs. unfold inv_with. iDes. unfold unint in *. des_ifs; subst.
      rewrite Any.upcast_downcast in *. clarify. steps.

      iDestruct "INV" as "[A|B]".
      2:{ iExFalso; ss. iDes. iApply (initial_map_no_points_to with "B PRE"). }
      iDes. des; subst. clarify. rewrite Any.upcast_downcast in *. clarify. steps.
      iApply isim_assume_tgt. iSplit.
      { iApply (unallocated_range with "[A1]"); eauto. }
      steps.
      iIntros. des; subst.
      iAssert (_)%I with "[A PRE]" as "U".
      { iApply (black_map_set with "A PRE"). }
      iMod "U". iDes.
      iModIntro. iSplits; ss. iFrame. iSplits; ss.
      { iLeft. iSplits; ss. iFrame. iSplits; ss. }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.
