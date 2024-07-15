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
Require Import HTactics2 HSim2.
Require Import Sealed.

Arguments hsim [_ _] _ _ _ _ _ _.

Set Implicit Arguments.


Require Import Red.
Require Import IRed.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).



Section SIM.
  Context `{Σ: GRA.t}.
  Context `{HF: HasFreeze}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Variable stb_src: gname -> fspec.
  Variable stb_tgt: gname -> fspec.

  Let _hsim := _hsim le I.

  Program Definition isim'
          r g f_src f_tgt
          {R_src R_tgt}
          (Frz: iProp)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (st_src: Any.t * itree Es' R_src)
          (st_tgt: Any.t * itree Es' R_tgt): iProp :=
    iProp_intro (fun fmr_src => forall OwnT (FROZEN: if has_freeze then Frz OwnT else True)
                                       (WF: URA.wf (fmr_src ⋅ OwnT)),
                     gpaco11 (_hsim) (cpn11 _hsim) r g _ _ stb_src stb_tgt OwnT Q (fmr_src ⋅ OwnT) f_src f_tgt st_src st_tgt) _.
  Next Obligation.
    cbn. i. des. esplits. guclo hupdC_spec.
    assert(URA.updatable (r1 ⋅ OwnT) (r0 ⋅ OwnT)).
    { eapply URA.updatable_add; try refl. eapply URA.extends_updatable; et. }
    econs; et. eapply H; eauto. eapply URA.updatable_wf; et.
  Qed.

  Definition isim
             '(r, g, f_src, f_tgt)
             {R_src R_tgt}
             (Frz: iProp)
             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
             (st_src: Any.t * itree Es' R_src)
             (st_tgt: Any.t * itree Es' R_tgt): iProp :=
    isim' r g f_src f_tgt Frz Q st_src st_tgt.

  Lemma isim_init
        R_src R_tgt (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        P r g fmr f_src f_tgt st_src st_tgt itr_src itr_tgt (Frz: iProp) OwnT
        (FROZEN: if has_freeze then Frz OwnT else True)
        (ENTAIL: bi_entails
                   P
                   (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, itr_tgt)))
        (CUR: current_iProp fmr (Own OwnT ** P))
    :
      gpaco11 _hsim (cpn11 _hsim) r g _ _  stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt).
  Proof.
    eapply current_iProp_frame_own_rev in CUR. des.
    eapply current_iProp_entail in ENTAIL; eauto.
    inv ENTAIL. unfold isim in IPROP. guclo hupdC_spec. econs.
    { eauto. }
    { etrans; eauto. eapply URA.updatable_add; eauto. refl. }
    exploit IPROP; eauto.
    eapply URA.updatable_wf; try apply CUR; eauto. etrans; eauto. eapply URA.updatable_add; eauto. refl.
  Qed.

  Lemma isim_final
        R_src R_tgt (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        P r g f_src f_tgt st_src st_tgt itr_src itr_tgt (Frz: iProp)
        (SIM: forall fmr OwnT
                     (FROZEN: if has_freeze then Frz OwnT else True)
                     (CUR: current_iProp fmr (Own OwnT ** P)),
            gpaco11 _hsim (cpn11 _hsim) r g _ _ stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      bi_entails
        P
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    rr. autorewrite with iprop. ii. eapply SIM; et. eapply current_iProp_frame_own; eauto.
    eapply current_iProp_entail; cycle 1.
    { iIntros "A". iIntros "B". iFrame. iAssumption. }
    econs; eauto. refl.
  Qed.

  Lemma isim_current
        R_src R_tgt (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fmr f_src f_tgt st_src st_tgt itr_src itr_tgt Frz OwnT
        (CUR: current_iProp fmr (Own OwnT ** isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, itr_tgt)))
        (FROZEN: if has_freeze then Frz OwnT else True)
    :
      gpaco11 _hsim (cpn11 _hsim) r g _ _ stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt).
  Proof.
    eapply current_iProp_frame_own_rev in CUR. des.
    inv CUR1.
    assert(URA.updatable fmr (r0 ⋅ OwnT)).
    { etrans; eauto. eapply URA.updatable_add; eauto. refl. }
    guclo hupdC_spec. econs; try apply IPROP; eauto.
    { eapply URA.updatable_wf; [|apply H]; eauto. }
  Qed.

  Lemma isim_upd R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
    :
      bi_entails
        (#=> (isim (r, g, f_src, f_tgt) Frz (fun st_src st_tgt ret_src ret_tgt => #=> Q st_src st_tgt ret_src ret_tgt) st_src st_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q st_src st_tgt).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    rr in H. unfold bi_bupd_bupd in H. ss. unfold Upd in H. autorewrite with iprop in H.
    des. i. guclo hmonoC_spec. econs; auto.
    guclo hupdC_spec. econs; eauto. eapply URA.updatable_add; eauto. refl.
  Qed.

  Lemma isim_upd_strong R_src R_tgt Frz
        (FREEZE: has_freeze = true)
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
    :
      bi_entails
        (sealed_upd Frz (isim (r, g, f_src, f_tgt) Frz Q st_src st_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q st_src st_tgt).
  Proof.
    {
      red. rr. uipropall. i. unfold sealed_upd in *. des_ifs.
      rr in H. uipropall. specialize (H (Own OwnT)). rr in H. uipropall.
      exploit H; et.
      { esplits; ss. refl. }
      clear H. intro T; des. subst.
      exploit T2; et.
      { des_ifs; et. }
      { specialize (T0 ε). rewrite ! URA.unit_id in T0. specialize (T0 WF0). r_wf T0. }
      i.
      guclo hupdC_spec. econs; eauto.
      guclo hupdC2_spec. econs; eauto.
      { eapply URA.extends_updatable. et. }
      rewrite URA.add_comm. ss.
    }
  Qed.

  Lemma isim_upd_frozen_antitone R_src R_tgt Frz0 Frz1
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt
        (VS: Frz1 ⊢ Frz0)
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Frz0 Q st_src st_tgt)
        (isim (r, g, f_src, f_tgt) Frz1 Q st_src st_tgt)
  .
  Proof.
    {
      red. rr. uipropall. i.
      des_ifs.
      - exploit VS; try apply FROZEN.
        { eapply URA.wf_extends; et. exists r0; r_solve. }
        clear VS. intro VS; des.
        exploit H; eauto.
      - eapply H; eauto.
    }
  Qed.

  Lemma isim_mono R_src R_tgt Frz
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src itr_src st_tgt itr_tgt
        (MONO: forall st_src st_tgt ret_src ret_tgt,
            (bi_entails (Q0 st_src st_tgt ret_src ret_tgt) (Q1 st_src st_tgt ret_src ret_tgt)))
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Frz Q0 (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q1 (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    ss.
    guclo hmonoC_spec. econs; eauto. i. iIntros "H".
    iModIntro. iApply MONO. auto.
  Qed.

  Lemma isim_wand R_src R_tgt Frz
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src itr_src st_tgt itr_tgt
    :
      bi_entails
        ((∀ st_src st_tgt ret_src ret_tgt,
             ((Q0 st_src st_tgt ret_src ret_tgt) -∗ (Q1 st_src st_tgt ret_src ret_tgt))) ** (isim (r, g, f_src, f_tgt) Frz Q0 (st_src, itr_src) (st_tgt, itr_tgt)))
        (isim (r, g, f_src, f_tgt) Frz Q1 (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' in *. rr. i.
    rr in H. unfold Sepconj in H. autorewrite with iprop in H. ss.
    des. clarify.
    guclo hframeC_aux_spec. econs; eauto.
    { instantiate (1:=a). instantiate (1:=b ⋅ OwnT).
      replace (a ⋅ b ⋅ OwnT) with (b ⋅ OwnT ⋅ a) by r_solve; refl. }
    eapply from_semantic in H0.
    guclo hmonoC_spec. econs.
    { eapply H1; et. eapply URA.wf_extends; et. exists a. r_solve. }
    i. iIntros "H0". iModIntro. iIntros "H1".
    iPoseProof (H0 with "H1") as "H1".
    iSpecialize ("H1" with "H0"). ss.
  Qed.

  Lemma isim_bind R_src R_tgt S_src S_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src (itr_src: itree Es' S_src)
        ktr_src st_tgt (itr_tgt: itree Es' S_tgt) ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Frz
           (fun st_src st_tgt ret_src ret_tgt =>
              (isim (r, g, false, false) True Q
                (st_src, ktr_src ret_src) (st_tgt, ktr_tgt ret_tgt))%I)
           (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src >>= ktr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hbindC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. guclo hupdC_spec. econs; et.
    uipropall. des. subst. guclo hupdC_spec.
    assert(URA.updatable (a ⋅ b) (b ⋅ OwnT0)).
    { rewrite URA.add_comm. eapply URA.updatable_add; try refl.
      eapply URA.extends_updatable; eauto. }
    econs.
    { eapply URA.updatable_wf; et. }
    2: { rr in IPROP1. uipropall. eapply IPROP1; ss; et.
         { des_ifs. rr. uipropall. }
         eapply URA.updatable_wf; et. etrans; eauto. }
    { ss. }
  Qed.

  Lemma isim_bind_two R_src R_tgt S_src S_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src (itr_src: itree Es' S_src)
        ktr_src st_tgt (itr_tgt: itree Es' S_tgt) ktr_tgt
    :
        (∃ R, (isim (r, g, f_src, f_tgt) Frz R (st_src, itr_src) (st_tgt, itr_tgt)) ∗
               (∀ st_src st_tgt ret_src ret_tgt, R st_src st_tgt ret_src ret_tgt -∗
              (isim (r, g, false, false) True Q
                (st_src, ktr_src ret_src) (st_tgt, ktr_tgt ret_tgt))))%I
          ⊢
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src >>= ktr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    iIntros. iDes.
    iApply isim_bind.
    iApply isim_wand. iFrame.
  Qed.

  Remark isim_bind_using_two
        R_src R_tgt S_src S_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src (itr_src: itree Es' S_src)
        ktr_src st_tgt (itr_tgt: itree Es' S_tgt) ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Frz
           (fun st_src st_tgt ret_src ret_tgt =>
              (isim (r, g, false, false) True Q
                (st_src, ktr_src ret_src) (st_tgt, ktr_tgt ret_tgt))%I)
           (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src >>= ktr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    iIntros. iDes. iApply isim_bind_two.
    iSplits. iFrame. iIntros. ss.
  Qed.

  Lemma isim_bind_left R_src R_tgt S_src Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src (itr_src: itree Es' S_src)
        ktr_src st_tgt itr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Frz (fun st_src st_tgt ret_src ret_tgt => (isim (r, g, false, false) True Q (st_src, ktr_src ret_src) (st_tgt, itr_tgt))%I) (st_src, itr_src) (st_tgt, Ret tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H".
    assert (EQ: itr_tgt = Ret tt >>= fun _ => itr_tgt).
    { grind. }
    rewrite EQ. iApply isim_bind. rewrite <- EQ. iApply "H".
  Qed.

  Lemma isim_bind_right R_src R_tgt S_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src itr_src
        st_tgt (itr_tgt: itree Es' S_tgt) ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, f_tgt) Frz (fun st_src st_tgt ret_src ret_tgt => (isim (r, g, false, false) True Q (st_src, itr_src) (st_tgt, ktr_tgt ret_tgt))%I) (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, itr_tgt >>= ktr_tgt)).
  Proof.
    iIntros "H".
    assert (EQ: itr_src = Ret tt >>= fun _ => itr_src).
    { grind. }
    rewrite EQ. iApply isim_bind. rewrite <- EQ. iApply "H".
  Qed.

  Lemma isim_call_impure
        w0 R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt fn arg_src arg_tgt ktr_src ktr_tgt
        fsp_src fsp_tgt
        (SPECS: stb_src fn = fsp_src)
        (SPECT: stb_tgt fn = fsp_tgt)
    :
      bi_entails
        (∀ (x_tgt: fsp_tgt.(meta)) argp,
            (fsp_tgt.(precond) x_tgt arg_tgt argp)
              -* ∃ (x_src: fsp_src.(meta)),
                ((inv_with le I w0 st_src st_tgt ∗ fsp_src.(precond) x_src arg_src argp)
                    ∗ (∀ st_src st_tgt retp ret_src,
                          {{"INV": inv_with le I w0 st_src st_tgt}}
                            -* {{"POST": (fsp_src.(postcond) x_src ret_src retp)}}
                            -* (∃ ret_tgt, ((fsp_tgt.(postcond) x_tgt ret_tgt retp))
                                  ∗ (isim (g, g, true, true) (fsp_tgt.(postcond) x_tgt ret_tgt retp) Q (st_src, ktr_src ret_src)
                                  (st_tgt, ktr_tgt ret_tgt)))
                      )))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Call fn arg_src) >>= ktr_src)
              (st_tgt, trigger (Call fn arg_tgt) >>= ktr_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp r0 P)
    end.
    { econs; eauto. refl. }
    clear H.
    apply current_iPropL_convert in CUR. mDesAll.
    ired_both. gstep. econs; eauto.
    { eapply current_iProp_frame_own; eauto. eapply current_iProp_entail; eauto.
      start_ipm_proof. iIntros. iFrame.
      iIntros. iDes. iSpecialize ("H" with "H1"). iDes. iModIntro. iSplits.
      iSplitL "H H2".
      { iFrame. instantiate (1:=emp%I). ss. }
      iIntros. iDes. iSpecialize ("H1" with "H3 H2"). iDes. iModIntro. iSplits; ss.
      { iFrame. iClear "H". iAccu. }
      iPureIntro.
      i. eapply current_iProp_frame_own_rev in ACC. des.
      inv ACC1. ss.
      assert(T: URA.updatable fmr1 (r1 ⋅ OwnT0)).
      { etrans; et. eapply URA.updatable_add; eauto. refl. }
      guclo hupdC_spec. econs; try apply IPROP; et.
      { eapply URA.updatable_wf; try apply ACC; eauto. }
    }
  Qed.

  Lemma isim_progress R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src itr_src st_tgt itr_tgt
    :
      bi_entails
        (isim (g, g, false, false) Frz Q (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, true, true) Frz Q (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR; et.
    eapply hsim_progress_flag. auto.
  Qed.

  Lemma isim_knowledge_mon
        r0 g0
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r1 g1 st_src itr_src st_tgt itr_tgt
        f_src f_tgt
        (LE0: r0 <11= r1)
        (LE1: g0 <11= g1)
    :
      bi_entails
        (isim (r0, g0, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r1, g1, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR; et.
    eapply gpaco11_mon; eauto.
  Qed.

  Lemma isim_flag_mon
        f_src0 f_tgt0
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src itr_src st_tgt itr_tgt
        f_src1 f_tgt1
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      bi_entails
        (isim (r, g, f_src0, f_tgt0) Frz Q (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src1, f_tgt1) Frz Q (st_src, itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR; et.
    guclo hflagC_spec. econs; eauto.
  Qed.

  Lemma isim_ret
        R_src R_tgt Frz (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g
        v_src v_tgt
        st_src st_tgt
        f_src f_tgt
    :
      bi_entails
        (Q st_src st_tgt v_src v_tgt)
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, Ret v_src) (st_tgt, (Ret v_tgt))).
  Proof.
    eapply isim_final. i.
    eapply hsimC_uclo. econs; eauto.
  Qed.

  Global Instance iProp_isim_absorbing
         R_src R_tgt r g (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp) Frz
         f_src f_tgt st_src st_tgt:
    Absorbing (isim (r, g, f_src, f_tgt) Frz Q st_src st_tgt).
  Proof.
    unfold Absorbing. unfold bi_absorbingly.
    iIntros "[H0 H1]". iApply isim_upd.
    iDestruct "H0" as "%". iModIntro.
    destruct st_src, st_tgt. iApply isim_mono; [|iApply "H1"].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.

  Global Instance iProp_isim_elim_upd
         R_src R_tgt Frz r g (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
         f_src f_tgt st_src st_tgt
         P:
    ElimModal True false false (#=> P) P (isim (r, g, f_src, f_tgt) Frz Q st_src st_tgt) (isim (r, g, f_src, f_tgt) Frz Q st_src st_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    destruct st_src, st_tgt. iApply isim_mono; [|iApply "H1"; auto].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.

  Global Instance iProp_pure_elim_affine
         P (Q: iProp):
    ElimModal True false false (<affine> ⌜P⌝) (⌜P⌝) Q Q.
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply "H1". iApply "H0".
  Qed.

  Lemma isim_syscall
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        fn arg rvs
        r g f_src f_tgt st_src st_tgt ktr_src ktr_tgt
    :
      bi_entails
        (∀ ret, isim (g, g, true, true) Frz Q (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    i. inv CUR. rr in IPROP. uipropall. des; subst. rr in IPROP1. uipropall.
    assert(URA.updatable (a ⋅ b) (b ⋅ OwnT)).
    { rewrite URA.add_comm. eapply URA.updatable_add; try refl.
      eapply URA.extends_updatable; eauto. }
    guclo hupdC_spec. econs; try apply IPROP1; eauto.
    { etrans; eauto. }
    { eapply URA.updatable_wf; et. etrans; eauto. }
  Qed.

  Lemma isim_tau_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_src itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Frz Q (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, tau;; itr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_tau_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_src itr_tgt
    :
      bi_entails
        (isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, tau;; itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_choose_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X ktr_src itr_tgt
    :
      bi_entails
        (∃ x, isim (r, g, true, f_tgt) Frz Q (st_src, ktr_src x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. subst. rr in IPROP1. uipropall. des. esplits.
    assert(URA.updatable fmr (b ⋅ OwnT)).
    { etrans; et. rewrite URA.add_comm. eapply URA.updatable_add; try refl.
      eapply URA.extends_updatable; eauto. }
    guclo hupdC_spec. econs; try apply IPROP1; et.
    { eapply URA.updatable_wf; et. }
  Qed.

  Lemma isim_choose_src_trigger
        X R_tgt Frz
        (Q: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (∃ x, isim (r, g, true, f_tgt) Frz Q (st_src, Ret x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Choose X)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Choose X))).
    iIntros "H". iApply isim_choose_src.
    iDestruct "H" as (x) "H". iExists x. auto.
  Qed.

  Lemma isim_choose_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X itr_src ktr_tgt
    :
      bi_entails
        (∀ x, isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, ktr_tgt x))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. subst. rr in IPROP1. uipropall. des. esplits.
    assert(URA.updatable fmr (b ⋅ OwnT)).
    { etrans; et. rewrite URA.add_comm. eapply URA.updatable_add; try refl.
      eapply URA.extends_updatable; eauto. }
    guclo hupdC_spec. econs; try apply IPROP1; et.
    { eapply URA.updatable_wf; et. }
  Qed.

  Lemma isim_choose_tgt_trigger
        R_src X Frz
        (Q: Any.t -> Any.t -> R_src -> X -> iProp)
        r g f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (∀ x, isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, Ret x))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, trigger (Choose X))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Choose X))).
    iIntros "H". iApply isim_choose_tgt.
    iIntros (x). iApply "H".
  Qed.

  Lemma isim_take_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X ktr_src itr_tgt
    :
      bi_entails
        (∀ x, isim (r, g, true, f_tgt) Frz Q (st_src, ktr_src x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. subst. rr in IPROP1. uipropall. des. esplits.
    assert(URA.updatable fmr (b ⋅ OwnT)).
    { etrans; et. rewrite URA.add_comm. eapply URA.updatable_add; try refl.
      eapply URA.extends_updatable; eauto. }
    guclo hupdC_spec. econs; try apply IPROP1; et.
    { eapply URA.updatable_wf; et. }
  Qed.

  Lemma isim_take_src_trigger
        X R_tgt Frz
        (Q: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (∀ x, isim (r, g, true, f_tgt) Frz Q (st_src, Ret x) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Take X)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Take X))).
    iIntros "H". iApply isim_take_src.
    iIntros (x). iApply "H".
  Qed.

  Lemma isim_take_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X itr_src ktr_tgt
    :
      bi_entails
        (∃ x, isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, ktr_tgt x))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. subst. rr in IPROP1. uipropall. des. esplits.
    assert(URA.updatable fmr (b ⋅ OwnT)).
    { etrans; et. rewrite URA.add_comm. eapply URA.updatable_add; try refl.
      eapply URA.extends_updatable; eauto. }
    guclo hupdC_spec. econs; try apply IPROP1; et.
    { eapply URA.updatable_wf; et. }
  Qed.

  Lemma isim_take_tgt_trigger
        R_src X Frz
        (Q: Any.t -> Any.t -> R_src -> X -> iProp)
        r g f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (∃ x, isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, Ret x))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, trigger (Take X))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Take X))).
    iIntros "H". iApply isim_take_tgt.
    iDestruct "H" as (x) "H". iExists x. iApply "H".
  Qed.

  Lemma isim_pput_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src0 st_src1 st_tgt ktr_src itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Frz Q (st_src1, ktr_src tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pput_src_trigger
        R_tgt Frz
        (Q: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g f_src f_tgt st_src0 st_src1 st_tgt itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Frz Q (st_src1, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src0, trigger (PPut st_src1)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PPut st_src1))).
    iIntros "H". iApply isim_pput_src. iApply "H".
  Qed.

  Lemma isim_pget_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt ktr_src itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Frz Q (st_src, ktr_src st_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_get_src_trigger
        R_tgt Frz
        (Q: Any.t -> Any.t -> Any.t -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (isim (r, g, true, f_tgt) Frz Q (st_src, Ret st_src) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (PGet)) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PGet))).
    iIntros "H". iApply isim_pget_src. iApply "H".
  Qed.

  Lemma isim_pput_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt0 st_tgt1 itr_src ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt1, ktr_tgt tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pput_tgt_trigger
        R_src Frz
        (Q: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g f_src f_tgt st_src st_tgt0 st_tgt1 itr_src
    :
      bi_entails
        (isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt1, Ret tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PPut st_tgt1))).
    iIntros "H". iApply isim_pput_tgt. iApply "H".
  Qed.

  Lemma isim_pget_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_src ktr_tgt
    :
      bi_entails
        (isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pget_tgt_trigger
        R_src Frz
        (Q: Any.t -> Any.t -> R_src -> Any.t -> iProp)
        r g f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, Ret st_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, trigger (PGet))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PGet))).
    iIntros "H". iApply isim_pget_tgt. iApply "H".
  Qed.

  Lemma isim_assume_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P k_src i_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, true, f_tgt) Frz Q (st_src, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, assume P >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold assume. hred_l.
    iApply isim_take_src. iIntros (H). hred_l. iApply "H". iPureIntro. auto.
  Qed.

  Lemma isim_assume_src_trigger
        R_tgt Frz
        (Q: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P itr_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, true, f_tgt) Frz Q (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, assume P) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (assume P)).
    iIntros "H". iApply isim_assume_src.
    iIntros "H0". iApply "H". auto.
  Qed.

  Lemma isim_assume_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P itr_src ktr_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, ktr_tgt tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, assume P >>= ktr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as "[% H]".
    unfold assume. hred_r. iApply isim_take_tgt.
    iExists H. hred_r. iApply "H".
  Qed.

  Lemma isim_assume_tgt_trigger
        R_src Frz
        (Q: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g f_src f_tgt st_src st_tgt P itr_src
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, Ret tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, assume P)).
  Proof.
    erewrite (@idK_spec _ _ (assume P)).
    iIntros "H". iApply isim_assume_tgt. iSplit; auto.
    { iDestruct "H" as "[H _]". iApply "H". }
    { iDestruct "H" as "[_ H]". iApply "H". }
  Qed.

  Lemma isim_guarantee_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P ktr_src itr_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, true, f_tgt) Frz Q (st_src, ktr_src tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, guarantee P >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as "[% H]".
    unfold guarantee. hred_l. iApply isim_choose_src.
    iExists H. hred_l. iApply "H".
  Qed.

  Lemma isim_guarantee_src_trigger
        R_tgt Frz
        (Q: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P itr_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, true, f_tgt) Frz Q (st_src, Ret tt) (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, guarantee P) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (guarantee P)).
    iIntros "H". iApply isim_guarantee_src. iSplit; auto.
    { iDestruct "H" as "[H _]". iApply "H". }
    { iDestruct "H" as "[_ H]". iApply "H". }
  Qed.

  Lemma isim_guarantee_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P itr_src ktr_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, ktr_tgt tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, guarantee P >>= ktr_tgt)).
  Proof.
    iIntros "H". unfold guarantee. hred_r.
    iApply isim_choose_tgt.
    iIntros (H). hred_r. iApply "H". iPureIntro. auto.
  Qed.

  Lemma isim_guarantee_tgt_trigger
        R_src Frz
        (Q: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g f_src f_tgt st_src st_tgt P itr_src
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, f_src, true) Frz Q (st_src, itr_src) (st_tgt, Ret tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, guarantee P)).
  Proof.
    erewrite (@idK_spec _ _ (guarantee P)).
    iIntros "H". iApply isim_guarantee_tgt.
    iIntros "H0". iApply "H". auto.
  Qed.

  Lemma isim_ASSUME_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P k_src i_tgt
    :
      bi_entails
        (P -* isim (r, g, true, f_tgt) True Q (st_src, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Cassume P) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp r0 P)
    end.
    { econs; eauto. refl. }
    clear H.
    apply current_iPropL_convert in CUR. mDesAll.
    ired_both. eapply hsimC_uclo. econs; eauto.
    { eapply current_iProp_frame_own; eauto. eapply current_iProp_entail; eauto.
      start_ipm_proof. iIntros. iFrame. iAccu.
    }
    i.
    eapply current_iProp_entail in ACC; cycle 1.
    { iIntros. iDes. iSpecialize ("H1" with "H2"). iAccu. }
    eapply current_iProp_frame_own_rev in ACC; eauto. des; subst. inv ACC1. ss.
    guclo hupdC_spec.
    econs; ss.
    2: { eapply IPROP; et; ss.
         { des_ifs; ss. rr. uipropall. }
         eapply URA.updatable_wf; try apply ACC; et. etrans; et. eapply URA.updatable_add; et.
         refl.
    }
    { etrans; et. eapply URA.updatable_add; et. refl. }
  Qed.

  Lemma isim_ASSERT_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P k_src i_tgt
    :
      bi_entails
        (P ∗ isim (r, g, true, f_tgt) True Q (st_src, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, trigger (Cassert P) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp r0 P)
    end.
    { econs; eauto. refl. }
    clear H.
    apply current_iPropL_convert in CUR. mDesAll.
    ired_both. eapply hsimC_uclo. econs; eauto.
    { eapply current_iProp_frame_own; eauto. eapply current_iProp_entail; eauto.
      start_ipm_proof. iIntros. iFrame. iAccu.
    }
    i.
    eapply current_iProp_entail in ACC; cycle 1.
    { iIntros. iDes. iAccu. }
    eapply current_iProp_frame_own_rev in ACC; eauto. des; subst. inv ACC1. ss.
    guclo hupdC_spec.
    econs; ss.
    2: { eapply IPROP; et; ss.
         { des_ifs; ss. rr. uipropall. }
         eapply URA.updatable_wf; try apply ACC; et. etrans; et. eapply URA.updatable_add; et.
         refl.
    }
    { etrans; et. eapply URA.updatable_add; et. refl. }
  Qed.

  Lemma isim_ASSUME_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P i_src k_tgt
    :
      bi_entails
        (P ∗ isim (r, g, f_src, true) True Q (st_src, i_src) (st_tgt, k_tgt tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, i_src) (st_tgt, trigger (Cassume P) >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp r0 P)
    end.
    { econs; eauto. refl. }
    clear H.
    apply current_iPropL_convert in CUR. mDesAll.
    ired_both. eapply hsimC_uclo. econs; eauto.
    { eapply current_iProp_frame_own; eauto. eapply current_iProp_entail; eauto.
      start_ipm_proof. iIntros. iFrame. iAccu.
    }
    i.
    eapply current_iProp_entail in ACC; cycle 1.
    { iIntros. iDes. iAccu. }
    eapply current_iProp_frame_own_rev in ACC; eauto. des; subst. inv ACC1. ss.
    guclo hupdC_spec.
    econs; ss.
    2: { eapply IPROP; et; ss.
         { des_ifs; ss. rr. uipropall. }
         eapply URA.updatable_wf; try apply ACC; et. etrans; et. eapply URA.updatable_add; et.
         refl.
    }
    { etrans; et. eapply URA.updatable_add; et. refl. }
  Qed.

  Lemma isim_ASSERT_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt P i_src k_tgt
    :
      bi_entails
        (P -∗ isim (r, g, f_src, true) True Q (st_src, i_src) (st_tgt, k_tgt tt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, i_src) (st_tgt, trigger (Cassert P) >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp r0 P)
    end.
    { econs; eauto. refl. }
    clear H.
    apply current_iPropL_convert in CUR. mDesAll.
    ired_both. eapply hsimC_uclo. econs; eauto.
    { eapply current_iProp_frame_own; eauto. eapply current_iProp_entail; eauto.
      start_ipm_proof. iIntros. iFrame. iAccu.
    }
    i.
    eapply current_iProp_entail in ACC; cycle 1.
    { iIntros. iDes. iSpecialize ("H1" with "H2"). iAccu. }
    eapply current_iProp_frame_own_rev in ACC; eauto. des; subst. inv ACC1. ss.
    guclo hupdC_spec.
    econs; ss.
    2: { eapply IPROP; et; ss.
         { des_ifs; ss. rr. uipropall. }
         eapply URA.updatable_wf; try apply ACC; et. etrans; et. eapply URA.updatable_add; et.
         refl.
    }
    { etrans; et. eapply URA.updatable_add; et. refl. }
  Qed.

  Lemma isim_triggerUB_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X (ktr_src: X -> _) itr_tgt
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, triggerUB >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". unfold triggerUB. hred_l. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_tgt
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, triggerUB) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply isim_triggerUB_src. auto.
  Qed.

  Lemma isim_triggerNB_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X itr_src (ktr_tgt: X -> _)
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, triggerNB >>= ktr_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply isim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt itr_src
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply isim_triggerNB_tgt. auto.
  Qed.

  Lemma isim_unwrapU_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X (x: option X) ktr_src itr_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Frz Q (st_src, ktr_src x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, unwrapU x >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. auto. }
  Qed.

  Lemma isim_unwrapU_src_trigger
        X R_tgt Frz
        (Q: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt x itr_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Frz Q (st_src, Ret x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, unwrapU x) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iApply isim_unwrapU_src.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed.

  Lemma isim_unwrapN_src
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X (x: option X) ktr_src itr_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Frz Q (st_src, ktr_src x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, unwrapN x >>= ktr_src) (st_tgt, itr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  Lemma isim_unwrapN_src_trigger
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt x itr_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Frz Q (st_src, Ret x') (st_tgt, itr_tgt))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, unwrapN x) (st_tgt, itr_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapN_src. iExists x'. iSplit; auto.
  Qed.

  Lemma isim_unwrapU_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X (x: option X) itr_src ktr_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, ktr_tgt x'))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, unwrapU x >>= ktr_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  Lemma isim_unwrapU_tgt_trigger
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt x itr_src
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, Ret x'))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, unwrapU x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapU_tgt. iExists x'. iSplit; auto.
  Qed.

  Lemma isim_unwrapN_tgt
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt X (x: option X) itr_src ktr_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, ktr_tgt x'))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, unwrapN x >>= ktr_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. auto. }
  Qed.

  Lemma isim_unwrapN_tgt_trigger
        R_src R_tgt Frz
        (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g f_src f_tgt st_src st_tgt x itr_src
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, Ret x'))
        (isim (r, g, f_src, f_tgt) Frz Q (st_src, itr_src) (st_tgt, unwrapN x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iApply isim_unwrapN_tgt.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed.

End SIM.

Global Opaque isim.



Section ADEQUACY.
  Context `{Σ: GRA.t}.
  Variable world: Type.
  Variable wf: world -> Any.t -> Any.t -> iProp.
  Variable le: relation world.
  Context `{PreOrder _ le}.
  Context `{HF: HasFreeze}.

  Lemma isim_fun_to_tgt_aux
        stb_src stb_tgt
        f_src f_tgt w fn
        (body_src body_tgt: _) x y st_src st_tgt
        (EQ: x = y)
        (WF: mk_wf wf w (st_src, st_tgt))
        (ISIM: forall x_src w arg_src argp st_src st_tgt,
              (inv_with le wf w st_src st_tgt ** (stb_src fn).(precond) x_src arg_src argp) ==∗ ∃ x_tgt arg_tgt,
              ((stb_tgt fn).(precond) x_tgt arg_tgt argp ** (
               isim
                 le wf stb_src stb_tgt
                 (bot11, bot11, true, true)
                 ((stb_tgt fn).(precond) x_tgt arg_tgt argp)
                 (λ st_src st_tgt ret_src ret_tgt, ∀ retp,
                   ((stb_tgt fn).(postcond) x_tgt ret_tgt retp) ==∗
                   (inv_with le wf w st_src st_tgt) ** ((stb_src fn).(postcond) x_src ret_src retp))%I
                 (st_src, body_src arg_src)
                 (st_tgt, body_tgt arg_tgt))%I))
    :
      sim_itree
        (mk_wf wf) le
        f_src f_tgt
        w
        (st_src, fun_to_tgt stb_src fn body_src x) (st_tgt, fun_to_tgt stb_tgt fn body_tgt y).
  Proof.
    {
      subst.
      ginit. unfold fun_to_tgt. rewrite ! HoareFun_parse.
      Local Transparent HoareFunArg.
      unfold HoareFunArg. steps. unfold ASSUME. steps.
      inv WF.
      eapply hassume_src_clo; et.
      { i. eapply current_iProp_frame_own; et.
        eapply current_iProp_entail.
        { instantiate (1:=True%I). econs; try refl; ss.
          - rr. uipropall; ss.
          - eapply URA.wf_unit.
        }
        { iIntros; iDes. iAccu. }
      }
      i. steps.
      exploit ISIM; et. clear ISIM. intro T; des.
      eapply from_semantic in RSRC; et.
      2: { inv ACC. eapply URA.wf_extends; et. exists (fr1 ⋅ mr_tgt); r_solve. }
      eapply current_iProp_entail in ACC.
      2: { iIntros. iDes. iDestruct "H1" as "[A B]".
           iDestruct (T with "[H A]") as "T".
           { unfold inv_with. iFrame. iSplits; et. iStopProof. et. }
           iAccu.
      }
      apply current_iPropL_convert in ACC. mDesAll. mUpd "A". mDesAll.
      force_r. esplits; et. steps. force_r. esplits; et. steps.
      eapply hassume_tgt_clo_strong; et.
      { eapply current_iProp_entail; et. start_ipm_proof. iFrame. iSplitL.
        { iAccu. }
        rewrite unit_own_true. ss.
      }
      i.
      steps.
      gfinal. right. rp; try eapply hsim_adequacy; try refl; et.
      2:{ f_equal. grind. des_ifs. }
      2:{ f_equal. grind. des_ifs. }
      clear - ACC0 CND.
      remember (λ st_src st_tgt ret_src ret_tgt : Any.t,
       (∀ retp : Any.t,
          postcond (stb_tgt fn) a ret_tgt retp ==∗
          inv_with le wf w st_src st_tgt ** postcond (stb_src fn) x ret_src retp)%I) as Q.
      clear HeqQ.
      rewrite ! URA.unit_id in *.
      ginit. eapply isim_init; et.
      2: { eapply current_iProp_entail; et. iIntros; iDes. iFrame. iSplitL "H2"; iFrame. }
      des_ifs. eapply iProp_mono; et.
      { apply current_iPropL_convert in ACC0. mDesAll. mClear "H". mClear "A2".
        rr in ACC0. inv ACC0; ss. rr in IPROP. uipropall. des; subst.
        eapply URA.updatable_wf; et. etrans; et.
        rr in IPROP0. rr in IPROP2. des; subst.
        eapply URA.extends_updatable. exists (ctx0 ⋅ ctx ⋅ b0). r_solve.
      }
      exists mr_tgt; r_solve.
    }
  Qed.

  Definition isim_fsem
    (stb_src stb_tgt: gname -> fspec)
    (fn: gname) (body_src body_tgt: (Any.t → itree Es' Any.t)) :=
    ∀ w (x_src: (stb_src fn).(meta)) arg_src argp st_src st_tgt,
      {{"INV": (inv_with le wf w st_src st_tgt)}} ==∗
      {{"PRE": ((stb_src fn).(precond) x_src arg_src argp)}} ==∗
      ∃ x_tgt arg_tgt,
      (((stb_tgt fn).(precond) x_tgt arg_tgt argp) **
         isim le wf stb_src stb_tgt (bot11, bot11, true, true)
         ((stb_tgt fn).(precond) x_tgt arg_tgt argp)
         (λ st_src st_tgt ret_src ret_tgt, ∀ retp,
          ((stb_tgt fn).(postcond) x_tgt ret_tgt retp) ==∗
          (inv_with le wf w st_src st_tgt) ** ((stb_src fn).(postcond) x_src ret_src retp))%I
         (st_src, body_src arg_src) (st_tgt, body_tgt arg_tgt))
  .

  Theorem adequacy_isim
    (stb_src stb_tgt: gname -> fspec)
    (fn: gname) (body_src body_tgt: (Any.t → itree Es' Any.t))
    (ISIM: isim_fsem stb_src stb_tgt fn body_src body_tgt)
    :
    <<SIM: sim_fsem (mk_wf wf) le (fun_to_tgt stb_src fn body_src) (fun_to_tgt stb_tgt fn body_tgt)>>.
  Proof.
    ii. subst. eapply isim_fun_to_tgt_aux; eauto.
    iIntros. iDes.
    iDestruct (ISIM with "[H]") as "H"; et. iMod "H". iSpecialize ("H" with "H1").
    iMod "H". iDes. iModIntro. iSplits; ss. iFrame.
  Qed.

  Definition add_frame (FRAME: iProp) (fsp: fspec): fspec :=
    mk_fspec (λ x a b, fsp.(precond) x a b ** FRAME)
      (λ x a b, fsp.(postcond) x a b ** FRAME).

  Theorem isim_hframe
    (stb_src stb_tgt: gname -> fspec)
    (FRAME: gname -> iProp)
    (fn: gname) (body_src body_tgt: (Any.t → itree Es' Any.t))
    :
    isim_fsem stb_src stb_tgt fn body_src body_tgt <->
    (∀ FRAME, isim_fsem (λ fn, add_frame (FRAME) (stb_src fn)) stb_tgt fn body_src body_tgt)
  .
  Proof.
    split; i.
    - ii. r in H0. etrans; et. clear H0.
      iIntros; iDes. iMod "H". iModIntro. iIntros. iDes. ss. iDes. iSpecialize ("H" with "[$]").
      iMod "H". iDes. iModIntro. iSplits; ss. iFrame.
      iStopProof.
      eapply isim_final. i.
      { inv CUR. rr in IPROP. autorewrite with iprop in IPROP. des; subst. ss.
        rr in IPROP0. autorewrite with iprop in IPROP0. rr in IPROP0; des. subst.
        rr in IPROP1. autorewrite with iprop in IPROP1. rr in IPROP1; des. subst.
        rename a into X.
        exploit IPROP2; et.
        { eapply URA.updatable_wf; et. etrans; et.
          eapply URA.extends_updatable. exists (ctx ⋅ X). r_solve. }
        intro T. clear IPROP2.
        guclo hupdC_spec.
        econs.
        { et. }
        { etrans; et. eapply URA.extends_updatable. exists ctx. instantiate (1:=(b0 ⋅ OwnT) ⋅ X). r_solve. }
        guclo hmonoC_spec. econs.
        { gfinal. right.
          eapply gpaco11_init in T; eauto with paco.
          eapply hframing_right; et.
          - clear - IPROP0. uipropall. i. eapply iProp_mono; et.
          - eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists ctx; r_solve.
        }
        { iIntros; iDes. iFrame. ss. }
      }
    - specialize (H0 True%I).
      ii. r in H0. etrans; et. clear H0.
      iIntros; iDes. iMod "H". iModIntro. iIntros. iDes. ss. iDes. iSpecialize ("H" with "[$]").
      iMod "H". iDes. iModIntro. iSplits; ss. iFrame.
      iStopProof.
      eapply isim_final. i.
      { inv CUR. rr in IPROP. autorewrite with iprop in IPROP. des; subst. ss.
        rr in IPROP0. autorewrite with iprop in IPROP0. rr in IPROP0; des. subst.
        exploit IPROP1; et.
        { eapply URA.updatable_wf; et. etrans; et.
          eapply URA.extends_updatable. exists (ctx). r_solve. }
        intro T. clear IPROP1.
        guclo hupdC_spec.
        econs.
        { et. }
        { etrans; et. eapply URA.extends_updatable. exists ctx. instantiate (1:=(b ⋅ OwnT)). r_solve. }
        guclo hmonoC_spec. econs.
        { gfinal. right.
          eapply gpaco11_init in T; eauto with paco.
          eapply hframing_left_strong; et.
          - eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists ctx; r_solve.
        }
        { iIntros; iDes. iModIntro. iIntros. iDes. iSpecialize ("H" with "H1").
          iMod "H". iDes. iFrame. ss. }
      }
  Qed.

  Require Import HoareFacts.

  Theorem isim_vframe
    (NOFREEZE: has_freeze = false)
    (stb_src stb_tgt: gname -> fspec)
    (fn: gname) (body_src body_tgt: (Any.t → itree Es' Any.t))
    :
    isim_fsem stb_src stb_tgt fn body_src body_tgt <->
    (∀ stb_fr, isim_fsem (stb_fr |> stb_src)%stb (stb_fr |> stb_tgt)%stb fn body_src body_tgt)
  .
  Proof.
    split; i.
    - ii. r in H0. destruct x_src as [x_fr x_src].
      iIntros. iModIntro. iIntros. iDes. ss. iDes.
      iDestruct (H0 with "INV") as "A". iMod "A". iSpecialize ("A" with "[$]").
      iMod "A". iDes. iModIntro. iExists (_, _). iSplits; ss.
      iSplitL "PRE A".
      { iSplits; ss. iFrame. }

      iStopProof.
      eapply isim_final. i.
      { inv CUR. rr in IPROP. autorewrite with iprop in IPROP. des; subst. ss.
        rr in IPROP0. autorewrite with iprop in IPROP0. rr in IPROP0; des. subst.
        exploit IPROP1; et.
        { des_ifs. }
        { eapply URA.updatable_wf; et. etrans; et.
          eapply URA.extends_updatable. instantiate (1:=OwnT). exists ctx. r_solve. }
        intro T. clear IPROP1.
        guclo hupdC_spec.
        econs.
        { et. }
        { etrans; et. eapply URA.extends_updatable. exists ctx. instantiate (1:=(b ⋅ OwnT)). r_solve. }
        guclo hmonoC_spec. econs.
        { gfinal. right.
          eapply gpaco11_init in T; eauto with paco.
          hexploit vframing_right; eauto.
          { eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists ctx; r_solve. }
        }
        { iIntros; iDes. iModIntro. iIntros. iDes. iSpecialize ("H" with "H11").
          iMod "H". iDes. iFrame. ss. iModIntro. iSplits; iFrame. }
      }
    - specialize (H0 ε%stb).
      ii. r in H0. specialize (H0 w (tt, x_src)). etrans; et. clear H0.
      iIntros; iDes. iMod "H". iModIntro. iIntros. iDes. ss. iSpecialize ("H" with "[PRE]").
      { iSplits; ss. }
      iMod "H". iDes. destruct x_tgt as [_ x_tgt]. iDes. subst.
      iModIntro. iSplits; ss. iFrame.
      iStopProof.
      eapply isim_final. i. des_ifs.
      { inv CUR. rr in IPROP. autorewrite with iprop in IPROP. des; subst. ss.
        rr in IPROP0. autorewrite with iprop in IPROP0. rr in IPROP0; des. subst.
        exploit IPROP1; et.
        { des_ifs. }
        { eapply URA.updatable_wf; et. etrans; et.
          eapply URA.extends_updatable. instantiate (1:=OwnT). exists (ctx). r_solve. }
        intro T. clear IPROP1.
        guclo hupdC_spec.
        econs.
        { et. }
        { etrans; et. eapply URA.extends_updatable. exists ctx. instantiate (1:=(b ⋅ OwnT)). r_solve. }
        guclo hmonoC_spec. econs.
        { gfinal. right.
          eapply gpaco11_init in T; eauto with paco.
          eapply vframing_left_strong; et.
          - eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists ctx; r_solve.
        }
        { iIntros; iDes. iModIntro. iIntros. iDes. iSpecialize ("H" with "[H1]").
          { iSplits; ss. }
          iMod "H". iDes. subst. iFrame. iModIntro. ss. }
      }
  Qed.

End ADEQUACY.

Section MOREFACTS.
  Context `{Σ: GRA.t}.
  Local Existing Instance HasFreezeN.
  Context `{EMSConfig}.
  Let wf2: _ -> _ -> Prop :=
        @mk_wf
          _ unit
          (fun (_:unit) st_src st_tgt => ⌜st_src = st_tgt⌝%I)
  .
  Global Program Instance stb_equiv_Proper: Proper ((eq ==> (≡)%stb) ==> eq ==> refines) SMod.to_tgt.
  Next Obligation.
    red; i.
    red; i. subst.
    eapply adequacy_local. econs; ss.
    i; ss.
    econstructor 1 with (wf:=wf2) (le:=top2); ss.
    2: { esplits; ss. rr.
         rp; [econs|..].
         4:{ repeat f_equal. rewrite URA.unit_idl. refl. }
         3:{ refl. }
         2:{ ss. }
         i. ss. rr. uipropall. }
    eapply Forall2_fmap_r. eapply Forall2_fmap_l.
    eapply Reflexive_instance_0.
    ii. ss. des_ifs. clear_tac. econs; ss.
    remember (x sk) as xsk.
    remember (y sk) as ysk.
    assert((xsk ≡ ysk)%stb).
    { subst. eapply H0; ss. }
    clears x. clears y. clears sk. clear_tac.
    {
      eapply adequacy_isim; ss.
      iStartProof.
      iIntros. des; subst; ss. clear_tac. iModIntro. iIntros. iDes.
      assert(T := H s). r in T. des.
      iModIntro. iSplits; ss.
      iSplitL "PRE".
      { iApply PRE; et. instantiate (2:=from x0).
        replace (to (from x0)) with (x0); et.
        eapply equal_f in PATH; et.
      }
      iStopProof.
      abstr (i x1) itr. clear_tac.
      eapply isim_final. ss. des_u; ss.
      i. gstep. econsr; et.
      revert_until H.
      gcofix CIH. i.
      eapply isim_init; ss; et.
      { eapply current_iProp_entail; et.
        iIntros; iDes; iFrame.
        ides itr; ss.
        - iApply isim_ret. iIntros. iDes. iModIntro. iSplits; ss.
          iDestruct (POST with "H") as "H".
          replace (to (from x11)) with (x11); et.
          eapply equal_f in PATH; et.
        - iApply isim_tau_src. iApply isim_tau_tgt.
          iStopProof.
          eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
        - destruct e; ss.
          { rewrite <- ! bind_trigger. resub.
            destruct c; ss.
            + iApply isim_ASSERT_tgt. iIntros. iApply isim_ASSERT_src. iFrame.
              iStopProof.
              eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
            + iApply isim_ASSUME_src. iIntros. iApply isim_ASSUME_tgt. iFrame.
              iStopProof.
              eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
          }
          destruct e; ss.
          { rewrite <- ! bind_trigger. resub.
            destruct c; ss.
            assert(U := H fn). r in U. des.
            iApply isim_call_impure; ss. iIntros. iDes.
            iSplits; ss. iFrame. iSplitL "H"; ss.
            { iSplits; ss. iApply PRE0; ss. }
            iIntros. des; subst. iDes. iSplits; ss.
            iSplitL "H"; ss.
            { iSplits; ss. iApply POST0; ss. }
            iStopProof.
            eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
          }
          destruct s0; ss.
          { rewrite <- ! bind_trigger. resub.
            destruct p; ss.
            + iApply isim_pput_src. iApply isim_pput_tgt.
              iStopProof.
              eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
            + iApply isim_pget_src. iApply isim_pget_tgt.
              iStopProof.
              eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
          }
          { rewrite <- ! bind_trigger. resub.
            destruct e; ss.
            + iApply isim_choose_tgt. iIntros. iApply isim_choose_src. iExists x.
              iStopProof.
              eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
            + iApply isim_take_src. iIntros. iApply isim_take_tgt. iExists x.
              iStopProof.
              eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
            + iApply isim_syscall. iIntros.
              iStopProof.
              eapply isim_final. ss. i. gstep. econsr; et. gbase. eapply CIH; et.
          }
      }
    }
    Unshelve.
    all: ss.
    all: try (exact emp%I).
  Qed.

  Theorem adequacy_isim2
    C T S
    A (le: A -> A -> Prop)
    `{PreOrder _ le}
    (I: A -> Any.t -> Any.t -> iProp)
    (SIMSK: SMod.sk T = SMod.sk S)
    (SIMMOD: ∀ sk,
        let T: SModSem.t := (SMod.get_modsem T sk) in
        let S: SModSem.t := (SMod.get_modsem S sk) in
        <<MN: SModSem.mn T = SModSem.mn S>> ∧
        <<INV: ∃ a0, mk_wf I a0 ((Any.pair (SModSem.initial_st S) (SModSem.initial_mr S)↑), (Any.pair (SModSem.initial_st T) (SModSem.initial_mr T)↑))>> ∧
        <<FNSEM: Forall2 (fun '(fn0, x) '(fn1, y) =>
                            fn0 = fn1 ∧ (isim_fsem I le C (ε%stb) fn0 x y))
                   (SModSem.fnsems S) (SModSem.fnsems T)>>
    )
    :
    gccr C T S
  .
  Proof.
    r; i.
    etrans.
    { eapply stb_equiv_Proper; et. instantiate (1:=(fun _ => fr |> ε)%stb).
      r; i. erewrite <- stb_append_unit_r. refl. }
    eapply adequacy_local.
    econs; ss.
    i. exploit SIMMOD; et. intro U; des. econs; ss; et.
    eapply Forall2_fmap.
    eapply Forall2_impl; try apply FNSEM.
    { ii. ss. des_ifs. des; subst. rr. split; ss.
      eapply adequacy_isim; et. eapply isim_vframe in H2; et.
    }
  Qed.

End MOREFACTS.
