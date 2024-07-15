Require Import MapHeader MapJ MapM HoareDef SimModSem.
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
Require Import HTactics ProofMode IPM.
Require Import Mem1 STB Invariant.
Require Import HoareFacts.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG MapRA1 Σ}.

  Let W: Type := Any.t * Any.t.

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb MemStb) (GlobalStbM sk).
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Lemma pending0_unique:
    pending0 -∗ pending0 -∗ False%I.
  Proof.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H". exfalso. clear - H1.
    rr in H1. ur in H1. unseal "ra". des; ss. rr in H1. unseal "ra". ss.
    unfold URA.add in *. ss. unseal "ra". ss.
  Qed.

  Lemma points_to_get_split blk ofs l k v
        (GET: nth_error l k = Some v)
    :
    OwnM((blk, ofs) |-> l) -∗ (OwnM((blk, (ofs + k)%Z) |-> [v])) ** ((OwnM((blk, (ofs + k)%Z) |-> [v]) -* OwnM((blk, ofs) |-> l))).
  Proof.
    revert blk ofs k v GET. induction l; ss; i.
    { destruct k; ss. }
    destruct k; ss.
    { clarify. iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]". iSplitL "H0".
      { rewrite Z.add_0_r. ss. }
      iIntros "H". iSplitL "H".
      { rewrite Z.add_0_r. ss. }
      { ss. }
    }
    { iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]".
      iPoseProof (IHl with "H1") as "H1"; eauto.
      iDestruct "H1" as "[H1 H2]".
      replace (ofs + Z.pos (Pos.of_succ_nat k))%Z with (ofs + 1 + k)%Z by lia.
      iSplitL "H1"; auto. iIntros "H1". iSplitL "H0"; auto.
      iApply "H2". auto.
    }
  Qed.

  Lemma set_nth_success A (l: list A) (k: nat) v
        (SZ: k < length l)
    :
    exists l', set_nth k l v = Some l'.
  Proof.
    revert k v SZ. induction l; ss; i.
    { exfalso. lia. }
    { destruct k; ss; eauto.
      hexploit IHl; eauto.
      { instantiate (1:=k). lia. }
      i. des. rewrite H1. eauto.
    }
  Qed.

  Lemma points_to_set_split blk ofs l k v l'
        (GET: set_nth k l v = Some l')
    :
    OwnM((blk, ofs) |-> l) -∗ (∃ v', OwnM((blk, (ofs + k)%Z) |-> [v'])) ** ((OwnM((blk, (ofs + k)%Z) |-> [v]) -* OwnM((blk, ofs) |-> l'))).
  Proof.
    revert blk ofs k v l' GET. induction l; ss; i.
    { destruct k; ss. }
    destruct k; ss.
    { clarify. iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]". iSplitL "H0".
      { rewrite Z.add_0_r. iExists _. ss. }
      iIntros "H". iEval (rewrite points_to_split). iSplitL "H".
      { rewrite Z.add_0_r. ss. }
      { ss. }
    }
    { iIntros "H". rewrite points_to_split.
      iDestruct "H" as "[H0 H1]".
      unfold option_map in GET. des_ifs.
      iPoseProof (IHl with "H1") as "H1"; eauto.
      iDestruct "H1" as "[H1 H2]". iDestruct "H1" as (v') "H1".
      replace (ofs + Z.pos (Pos.of_succ_nat k))%Z with (ofs + 1 + k)%Z by lia.
      iSplitL "H1"; auto. iIntros "H1".
      iEval (rewrite points_to_split). iSplitL "H0"; auto.
      iApply "H2". auto.
    }
  Qed.

  Lemma set_nth_map A B (f: A -> B) k l v
    :
    set_nth k (List.map f l) (f v) = option_map (List.map f) (set_nth k l v).
  Proof.
    revert k v. induction l; ss; i.
    { destruct k; ss. }
    { destruct k; ss. rewrite IHl. unfold option_map. des_ifs. }
  Qed.

  Lemma nth_error_map A B (f: A -> B) k l
    :
    nth_error (List.map f l) k = option_map f (nth_error l k).
  Proof.
    revert k. induction l; ss; i.
    { destruct k; ss. }
    { destruct k; ss. }
  Qed.

  Lemma repeat_nth A (a: A) n k
        (RANGE: k < n)
    :
    nth_error (List.repeat a n) k = Some a.
  Proof.
    revert k RANGE. induction n; ss; i.
    { lia. }
    { destruct k; ss. rewrite IHn; eauto. lia. }
  Qed.

  Lemma set_nth_length A k (a: A) l l'
        (SET: set_nth k l a = Some l')
    :
    length l' = length l.
  Proof.
    revert l l' SET. induction k; ss; i.
    { destruct l; ss. clarify. }
    { destruct l; ss. unfold option_map in *. des_ifs.
      ss. f_equal. eauto.
    }
  Qed.

  Lemma set_nth_error A k (a: A) l l' k'
        (SET: set_nth k l a = Some l')
    :
    nth_error l' k' = if Nat.eq_dec k' k then Some a else nth_error l k'.
  Proof.
    revert a l l' k' SET. induction k; ss; i.
    { destruct l; ss. clarify. des_ifs. destruct k'; ss. }
    { destruct l; ss. unfold option_map in *. des_ifs; ss.
      { erewrite IHk; eauto. des_ifs. }
      { destruct k'; ss. erewrite IHk; eauto. des_ifs. }
    }
  Qed.

  Lemma repeat_map A B (f: A -> B) (a: A) n
    :
    map f (repeat a n) = repeat (f a) n.
  Proof.
    induction n; ss. f_equal; auto.
  Qed.

  Lemma unfold_iter (E : Type -> Type) (A B : Type) (f : A -> itree E (A + B)) (x : A)
    :
    ITree.iter f x = lr <- f x;;
                     match lr with
                     | inl l => tau;; ITree.iter f l
                     | inr r => Ret r
                     end.
  Proof.
    eapply bisim_is_eq. eapply unfold_iter.
  Qed.

  Lemma points_to_nil blk ofs
    :
    ((blk, ofs) |-> []) = ε.
  Proof.
    Local Transparent URA.unit.
    ss. unfold points_to, Auth.white. f_equal.
    rewrite unfold_points_to.
    extensionality _blk. extensionality _ofs. unfold andb. des_ifs.
    exfalso. ss. lia.
  Qed.

  Lemma points_to_app blk ofs l0 l1
    :
    (blk, ofs) |-> (l0 ++ l1) = ((blk, ofs) |-> l0) ⋅ ((blk, (ofs + strings.length l0)%Z) |-> l1).
  Proof.
    revert ofs l1. induction l0; i; ss.
    { rewrite points_to_nil. rewrite URA.unit_idl. ss.
      replace (ofs + 0)%Z with ofs; ss. lia.
    }
    { rewrite points_to_split. rewrite (points_to_split blk ofs a l0).
      erewrite IHl0. rewrite URA.add_assoc. f_equal; ss.
      replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l0)))%Z with
        (ofs + 1 + strings.length l0)%Z; ss. lia.
    }
  Qed.

  Lemma OwnM_combine M `{@GRA.inG M Σ} a0 a1
    :
    (OwnM a0 ** OwnM a1) -∗ OwnM (a0 ⋅ a1).
  Proof.
    iIntros "[H0 H1]". iCombine "H0 H1" as "H". auto.
  Qed.

  Require Import HTactics2 HSim2 ISim2 IProofMode2.

  Let wf :=
        (fun (_: unit) st_src st_tgt =>
           ((∃ blk ofs l (f: Z -> Z) (sz: Z), ⌜st_src = (Some (f, sz))↑ /\ (length l = Z.to_nat sz) /\ (forall k (SZ: (0 <= k < sz)%Z), nth_error l (Z.to_nat k) = Some (f k)) /\ st_tgt = (Vptr blk ofs)↑⌝ ** OwnM ((blk, ofs) |-> (List.map Vint l)) ** pending0) ∨
              (⌜st_src = (None: option ((Z -> Z) * Z))↑⌝))%I).

  (* Theorem correct: refines2 [(SMod.to_tgt (fun _ => MemConds) MapI.Map)] *)
  (*                    [(SMod.to_tgt (fun _ => Conds) MapM.SMap)]. *)
  Local Existing Instance HasFreezeN.
  Theorem correct: gccr Conds MapJ.Map MapM.SMap.
  Proof.
    eapply adequacy_isim2 with (I:=wf) (le:=top2); ss.
    i. esplits; ss.
    { econs. eapply to_semantic. iIntros "_". iRight. auto. }
    econs; ss.
    { econs; [reflexivity|].
      iIntros. iDes. ss. iModIntro. iIntros. iDes. iModIntro. iSplits; ss.
      unfold MapJ.initF, MapM.initF, cfunU, ccallU. steps. subst. steps.
      des_ifs. unfold inv_with. iDes. unfold unint in *. des_ifs; subst.
      rewrite Any.upcast_downcast in *. clarify.

      iDestruct "INV" as "[A|%B]".
      { iDes; des; subst.
        iAssert False%I with "[A1 PRE1]" as "H"; ss.
        iApply (pending0_unique with "A1 PRE1").
      }
      subst. steps. unfold specbody. steps.

      iApply isim_take_tgt. iSplits; et. steps.
      iApply isim_ASSUME_tgt. iSplits; ss.
      steps.
      iApply isim_ASSERT_tgt. iIntros. iDes. subst. steps.
      iApply isim_guarantee_src. iSplits; ss. steps.
      iIntros. iModIntro. iSplits; ss. iLeft. iSplits; ss; et.
      iFrame. iSplitR "H"; et.
      2: { rewrite repeat_map. et. }
      iDestruct "PRE" as "%T". iPureIntro. esplits; et.
      - rewrite repeat_length. rewrite Nat2Z.id; ss.
      - i; ss. rewrite nth_error_repeat; ss. lia.
    }
    econs; ss.
    { econs; [reflexivity|].
      iIntros. iDes. ss. iModIntro. iIntros. iDes. iModIntro. iSplits; ss.
      unfold MapJ.getF, MapM.getF, cfunU, ccallU. steps. subst. steps.
      des_ifs. unfold inv_with. iDes. unfold unint in *. des_ifs; subst.

      iDestruct "INV" as "[A|%B]".
      2: { subst. steps. iApply isim_triggerUB_src. ss. }
      iDes. des. subst. steps. unfold specbody. steps.

      unfold scale_int. des_ifs.
      2:{ exfalso. eapply n. eapply Z.divide_factor_r. }
      steps.

      iApply isim_take_tgt. iSplits; et. steps.
      iApply isim_ASSUME_tgt. iSplits; ss.
      instantiate (1:=(_, _, _)). ss.
      iDestruct (points_to_get_split with "A") as "B".
      { eapply map_nth_error; et. }
      iDes. iFrame. iSplits; ss; et.
      { rewrite Z_div_mult; ss. iPureIntro. repeat f_equal. lia. }
      steps.
      iApply isim_ASSERT_tgt. iIntros. iDes. subst. steps.

      iIntros. iModIntro. iSplits; ss. iLeft. iSplits; ss; et.
      iFrame. iSplitR.
      { iSplits; ss. }
      iApply "B1"; et.
    }
    econs; ss.
    { econs; [reflexivity|].
      iIntros. iDes. ss. iModIntro. iIntros. iDes. iModIntro. iSplits; ss.
      unfold MapJ.setF, MapM.setF, cfunU, ccallU. steps. subst. steps.
      des_ifs. unfold inv_with. iDes. unfold unint in *. des_ifs; subst.

      iDestruct "INV" as "[A|%B]".
      2: { subst. steps. iApply isim_triggerUB_src. ss. }
      iDes. des. subst. steps. unfold specbody. steps.

      unfold scale_int. des_ifs.
      2:{ exfalso. eapply n. eapply Z.divide_factor_r. }
      steps.

      hexploit set_nth_success.
      { rewrite H3. instantiate (1:=Z.to_nat y1). lia. }
      i. des.


      iApply isim_take_tgt. iSplits; et. steps.
      iApply isim_ASSUME_tgt. iSplits; ss.
      instantiate (1:=(_, _, _)). ss.
      iDestruct (points_to_set_split with "A") as "B".
      { rewrite set_nth_map. rewrite H2. ss. }
      iDes. iFrame. iSplits; ss; et. iSplitL "B".
      { iSplits; et. rewrite Z_div_mult; ss. rewrite Z2Nat.id; ss. }
      steps.
      iApply isim_ASSERT_tgt. iIntros. iDes. subst. steps.

      iIntros. iModIntro. iSplits; ss. iLeft. subst. iSplits; ss.
      iFrame. iSplitR.
      { instantiate(4:=l'). iSplits; ss.
        { erewrite set_nth_length; eauto. }
        iPureIntro. esplits; eauto.
        { i. ss. erewrite set_nth_error; eauto. des_ifs; eauto. exfalso. lia. }
      }
      iApply "B1"; et. rewrite Z_div_mult; ss. rewrite Z2Nat.id; ss.
    }
  Unshelve.
    all: ss.
  Qed.
End SIMMODSEM.
