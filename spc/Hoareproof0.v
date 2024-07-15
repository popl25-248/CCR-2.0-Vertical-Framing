Require Import ProofMode.
Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimSTS.
Require Import SimGlobal.
From Ordinal Require Import Ordinal Arithmetic.
Require Import List.
Require Import Red IRed.


Set Implicit Arguments.

Local Open Scope nat.

















Module TAC.
  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso

    (*** assume/guarantee ***)
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (guclo simg_indC_spec; econs; eauto; try (by ss);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .
  Ltac seal_left :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_src
    end.
  Ltac seal_right :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_tgt
    end.
  Ltac unseal_left :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ (@Seal.sealing _ _ ?i_src) ?i_tgt ] => unseal i_src
    end.
  Ltac unseal_right :=
    match goal with
    | [ |- gpaco7 _ _ _ _ _ _ _ _ _ ?i_src (@Seal.sealing _ _ ?i_tgt) ] => unseal i_tgt
    end.
  Ltac force_l := seal_right; _step; unseal_right.
  Ltac force_r := seal_left; _step; unseal_left.
  Ltac deflag := eapply simg_progress_flag.
  (* Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|]. *)
End TAC.
Import TAC.


Section CANCEL.

  (*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
  Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
  Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)



  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := Sk.sort (fold_right Sk.add Sk.unit (List.map SMod.sk mds)).
  (* Let skenv: SkEnv.t := Sk.load_skenv sk. *)

  Let _mss: Sk.t -> list SModSem.t := fun sk => (List.map ((flip SMod.get_modsem) sk) mds).
  Variable _stb: Sk.t -> gname -> fspec.

  Let mss: list SModSem.t := _mss sk.
  Let stb: (gname -> fspec) := _stb sk.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt _stb) mds.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).


  Lemma sk_eq:
    ModL.sk (Mod.add_list mds_tgt) = ModL.sk (Mod.add_list mds_src).
  Proof.
    unfold ms_tgt, ms_src, mds_src, mds_tgt, ModL.enclose.
    rewrite ! Mod.add_list_sk. f_equal.
    generalize mds. clear. i. induction mds; ss.
    rewrite IHl. auto.
  Qed.

  Lemma fst_initial_mrs_eq:
    List.map fst (ModSemL.initial_mrs ms_tgt) = List.map fst (ModSemL.initial_mrs ms_src).
  Proof.
    pose proof sk_eq.
    unfold ms_tgt, ms_src, mds_tgt, mds_src, ModL.enclose.
    unfold mds_src, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_src) mds))). i.
    rewrite ! Mod.add_list_initial_mrs.
    generalize mds. clear. i. induction mds; auto.
    ss. rewrite IHl. auto.
  Qed.

  Lemma fns_eq:
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_tgt))))
    =
    (List.map fst (ModSemL.fnsems (ModL.enclose (Mod.add_list mds_src)))).
  Proof.
    pose proof sk_eq. unfold ModL.enclose.
    unfold mds_src, mds_tgt, ModL.enclose.
    unfold mds_src, mds_tgt in H. rewrite H.
    generalize (ModL.sk (Mod.add_list (List.map (SMod.to_src) mds))). i.
    rewrite ! Mod.add_list_fns. rewrite ! List.map_map. f_equal.
    f_equal. extensionality sm. ss. rewrite ! List.map_map. f_equal.
    extensionality fnsb. destruct fnsb as [fn sb]. ss.
  Qed.

  Lemma alist_find_map2 K `{Dec K} V0 V1 (f: K -> V0 -> V1) (k: K) (l: alist K V0)
    :
      alist_find k (List.map (fun '(k, v) => (k, f k v)) l) = o_map (alist_find k l) (f k).
  Proof.
    induction l; ss. uo. destruct a. rewrite eq_rel_dec_correct in *.
    des_ifs.
  Qed.

  Lemma stb_find_iff fn
    :
      ((<<FINDSRC: alist_find fn (ModSemL.fnsems ms_src) = None>>) /\
       (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) = None>>)) \/

      (exists md body,
          (<<FINDSRC: alist_find fn (ModSemL.fnsems ms_src) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_src body)>>) /\
          (<<FINDTGT: alist_find fn (ModSemL.fnsems ms_tgt) =
                      Some (transl_all (T:=_)
                              (SModSem.mn (SMod.get_modsem md sk))
                              ∘ fun_to_tgt (stb) fn body)>>) /\
          (<<MIN: List.In (SModSem.mn (SMod.get_modsem md sk)) (List.map fst ms_tgt.(ModSemL.initial_mrs))>>)).
  Proof.
    unfold ms_src, ms_tgt, mds_tgt, mds_src, SMod.to_src, mds_tgt, SMod.to_tgt.
    rewrite SMod.transl_fnsems. rewrite SMod.transl_fnsems. rewrite SMod.transl_initial_mrs. fold sk.
    unfold _mss.
    generalize mds. induction mds0; ss; auto. rewrite ! alist_find_app_o.
    erewrite ! SMod.red_do_ret2. rewrite ! alist_find_map. rewrite ! alist_find_map2. uo.
    destruct (alist_find fn (SModSem.fnsems (SMod.get_modsem a sk))) eqn:FIND.
    { right. esplits; et. }
    des.
    { left. esplits; et. }
    { right. esplits; et. }
  Qed.


  Let W: Type := (p_state).

  Let r_state: Type := mname -> Σ.

  Let zip_state (mps: p_state) (mrs: r_state): p_state :=
    fun mn => match alist_find mn ms_tgt.(ModSemL.initial_mrs) with
              | Some r => Any.pair (mps mn) (mrs mn)↑
              | None => mps mn
              end.

  Let rsum_minus (mn: mname): r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (update mrs_tgt mn ε) (List.map fst ms_tgt.(ModSemL.initial_mrs))) ε).

  Let rsum: r_state -> Σ :=
    fun mrs_tgt => (fold_left (⋅) (List.map (mrs_tgt <*> fst) ms_tgt.(ModSemL.initial_mrs)) ε).



  Lemma fold_left_add (r: Σ) rs
    :
      fold_left URA.add rs r = (fold_left URA.add rs ε) ⋅ r.
  Proof.
    revert r. induction rs; ss.
    { i. rewrite URA.unit_idl. auto. }
    i. rewrite IHrs. rewrite (IHrs (ε ⋅ a)). r_solve.
  Qed.

  Let rsum_update mn (mrs: r_state) r (mns: list mname) r0
      (MIN: List.In mn mns)
      (NODUP: NoDup mns)
    :
      (fold_left (⋅) (List.map (update mrs mn r) mns) r0) ⋅ (mrs mn)
      =
      (fold_left (⋅) (List.map mrs mns) r0) ⋅ r.
  Proof.
    revert mn mrs r r0 MIN NODUP. induction mns; ss. i.
    inv NODUP. des.
    { subst. rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs mn)).
      rewrite <- ! URA.add_assoc. f_equal.
      { f_equal. apply map_ext_in. i.
        unfold update. des_ifs. }
      { unfold update. des_ifs. r_solve. }
    }
    { rewrite IHmns; et.
      rewrite fold_left_add. rewrite (fold_left_add (r0 ⋅ mrs a)).
      unfold update. des_ifs. }
  Qed.

  Lemma rsum_minus_update mn0 mn1 mrs r
        (MIN0: List.In mn0 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (MIN1: List.In mn1 (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum_minus mn0 mrs ⋅ r = rsum_minus mn1 (update mrs mn0 r) ⋅ update mrs mn0 r mn1.
  Proof.
    unfold rsum_minus.
    revert MIN0 MIN1 NODUP. generalize (List.map fst (ModSemL.initial_mrs ms_tgt)). i.
    rewrite rsum_update; et.
    transitivity (fold_left (⋅) (List.map (update (update mrs mn0 ε) mn0 r) l) ε ⋅ (update mrs mn0 ε mn0)).
    { rewrite rsum_update; et. }
    { f_equal.
      { f_equal. f_equal. extensionality mn. unfold update. des_ifs. }
      { unfold update. des_ifs. }
    }
  Qed.

  Lemma rsum_minus_rsum mn mrs
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (IN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      rsum_minus mn mrs ⋅ mrs mn = rsum mrs.
  Proof.
    unfold rsum_minus, rsum. revert NODUP IN.
    setoid_rewrite <- (List.map_map fst mrs).
    generalize (map fst (ModSemL.initial_mrs ms_tgt)) as mns.
    i. rewrite rsum_update; et. r_solve.
  Qed.

  Lemma initial_mrs_exist
        (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      exists (initial_mrs: r_state),
        (<<INITIALZIP:
           zip_state (ModSemL.initial_p_state ms_src) initial_mrs =
           ModSemL.initial_p_state ms_tgt>>) /\
        (<<INITIALRSUM:
           forall mn (MIN: List.In mn (map fst ms_tgt.(ModSemL.initial_mrs))),
             rsum_minus mn initial_mrs ⋅ initial_mrs mn = fold_left URA.add (List.map SModSem.initial_mr mss) ε>>).
  Proof.
    exists (fun mn =>
              match alist_find mn (SMod.load_initial_mrs
                                     (Sk.sort (foldr Sk.add Sk.unit (map SMod.sk mds))) mds
                                     SModSem.initial_mr) with
              | Some r => r
              | _ => ε
              end).
    split.
    { revert NODUP.
      unfold ModSemL.initial_p_state, zip_state.
      unfold ms_src, ms_tgt.
      unfold mds_src, mds_tgt, SMod.to_src, SMod.to_tgt. ss.
      rewrite ! SMod.transl_initial_mrs.
      change (alist string Sk.gdef) with Sk.t.
      generalize (Sk.sort (fold_right Sk.add Sk.unit (map SMod.sk mds))).
      intros sk0. i. red. extensionality mn.
      unfold SMod.load_initial_mrs.
      rewrite ! SMod.red_do_ret. clear. induction mds; ss.
      rewrite ! eq_rel_dec_correct. des_ifs.
    }
    { ii. rewrite rsum_minus_rsum; et. fold sk. unfold rsum. clear mn MIN.
      f_equal. revert NODUP.
      unfold mss, _mss, ms_tgt, mds_tgt, SMod.to_tgt.
      rewrite ! SMod.transl_initial_mrs.
      unfold SMod.load_initial_mrs.
      rewrite ! SMod.red_do_ret.
      rewrite ! List.map_map. ss. fold sk. generalize sk. clear. i.
      eapply map_ext_in. i. des_ifs.
      { eapply alist_find_some in Heq.
        eapply in_map_iff in Heq. des. clarify.
        destruct (classic (a = x)).
        { subst. auto. }
        eapply NoDup_inj_aux in H0; et. ss.
        exfalso. eapply H0. et.
      }
      { exfalso. eapply alist_find_none in Heq.
        eapply (in_map (fun x => (SModSem.mn (SMod.get_modsem x sk), SModSem.initial_mr (SMod.get_modsem x sk)))) in H; et.
      }
    }
  Qed.

  Local Opaque rsum rsum_minus.


  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).

  Ltac steps := repeat (mred; try _step; des_ifs_safe).


  Let zip_state_get st mrs mn
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      zip_state st mrs mn = Any.pair (st mn) (mrs mn)↑.
  Proof.
    unfold zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed.

  Let zip_state_mput st mrs mn r
      (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
      update (zip_state st mrs) mn (Any.pair (st mn) (Any.upcast r))
      =
      zip_state st (update mrs mn r).
  Proof.
    extensionality mn0.
    unfold update, zip_state. des_ifs.
    eapply in_map_iff in MIN. des. destruct x. subst.
    eapply alist_find_none in Heq.
    exfalso. eapply Heq. et.
  Qed.

  Lemma rsum_update2
        mrs0 mn mr
        (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
        (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    :
    rsum (update mrs0 mn mr) = rsum_minus mn mrs0 ⋅ mr
  .
  Proof.
    erewrite <- rsum_minus_rsum; et. unfold update at 2. des_ifs. f_equal.
    Local Transparent rsum_minus.
    unfold rsum_minus.
    Local Opaque rsum_minus. do 2 f_equal. unfold update. extensionality k. des_ifs.
  Qed.

  Let adequacy_type_aux
      (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs))):
    forall RT
           init_r mrs0 fr0
           st_src0 st_tgt0 (i0: itree _ RT)
           mn
           (ZIP: st_tgt0 = zip_state st_src0 mrs0)

           (RWF: URA.wf init_r)
           (UPD: URA.updatable init_r (fr0 ⋅ rsum mrs0)) (** some sort of "baked-in" upto **)
           (MIN: List.In mn (List.map fst ms_tgt.(ModSemL.initial_mrs)))
           (NODUP: NoDup (List.map fst ms_tgt.(ModSemL.initial_mrs)))
    ,
      simg (fun '(st_src1, v_src) '(st_tgt1, v_tgt) =>
              exists mrs1 fr1,
                (<<ZIP: st_tgt1 = zip_state st_src1 mrs1>>) /\
                (<<RET: (v_tgt: Σ * RT) = (fr1, v_src)>>) /\
                (<<UPD: URA.updatable init_r (fr1 ⋅ rsum mrs1)>>))
           false false
           (EventsL.interp_Es (ModSemL.prog ms_src) (transl_all mn (interp_Es'_src i0)) st_src0)
           (EventsL.interp_Es (ModSemL.prog ms_tgt)
              (transl_all mn (interp_condE_tgt (interp_Es'_tgt (stb) i0) fr0)) st_tgt0)
  .
  Proof.
    Opaque subevent.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i; subst.
    ides i0; try rewrite ! unfold_interp; cbn; mred.
    { steps. esplits; et. }
    { steps. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss. }
    rewrite <- bind_trigger.
    destruct e; ss.
    { destruct c; ss.
      - resub. steps. unfold handle_condE_src. steps.
      - resub. seal_right. steps. unfold handle_condE_src. steps.
    }
    destruct e; ss; cycle 1.
    {
      destruct s; ss.
      {
        destruct p; ss.
        - resub. steps.
          erewrite zip_state_get; et. steps. deflag.
          gbase. eapply CIH; et; ss.
          extensionality mn0. unfold update, zip_state. des_ifs.
          exfalso. eapply in_map_iff in MIN. des. destruct x. subst.
          eapply alist_find_none in Heq. et.
        - resub. steps.
          erewrite zip_state_get; et. steps. deflag.
          gbase. eapply CIH; ss.
      }
      { dependent destruction e.
        - resub. ired_both. force_r. steps. esplits; eauto. steps. deflag.
          gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. steps. esplits; eauto. steps. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss.
        - resub. steps. deflag. gbase. eapply CIH; [..|M]; Mskip et. ss.
      }
    }
    dependent destruction c. resub.
    set (ModSemL.prog ms_src) as p_src in *.
    set (ModSemL.prog ms_tgt) as p_tgt in *.
    ss.

    steps. set (f0:=stb fn). hexploit (stb_find_iff fn). i. des.
    { rewrite FINDSRC. steps. }
    steps.
    unfold unwrapU. des_ifs; steps.
    unfold HoareCall, ASSUME, ASSERT, mput, mget. steps.
    steps. unfold mput, mget. steps.
    erewrite zip_state_get; et. rewrite Any.pair_split. steps.
    erewrite zip_state_get; et. rewrite Any.pair_split. steps.

    rewrite FINDTGT. steps.
    rename c1 into fr1. rename c into mr1. rename c0 into rarg.

    guclo bindC_spec. econs.

    Focus 2.
    { instantiate (1:= fun '(st_src1, vret_src) '(st_tgt1, vret_tgt) =>
                         exists (mrs1: r_state) rret,
                           (<<ZIP: st_tgt1 = zip_state st_src1 mrs1>>) /\
                           (<<POST: f0.(postcond) x vret_src vret_tgt rret>>) /\
                           (<<RWF: URA.updatable (rarg ⋅ rsum_minus mn mrs0 ⋅ mr1) (rret ⋅ rsum mrs1)>>)).
      ii. ss. des_ifs_safe. des. subst.
      steps. esplits; steps.
      eexists (rret). steps. unfold mput, mget. steps.
      rewrite zip_state_get; et.
      rewrite Any.pair_split. steps.
      assert(UPD0: URA.updatable init_r (rret ⋅ rsum mrs1 ⋅ fr1)).
      { etrans; et. erewrite <- rsum_minus_rsum with (mn:=mn); et.
        replace (fr0 ⋅ (rsum_minus mn mrs0 ⋅ mrs0 mn)) with (fr0 ⋅ mrs0 mn ⋅ rsum_minus mn mrs0) by r_solve.
        etrans.
        { eapply URA.updatable_add; et. refl. }
        replace (rarg ⋅ fr1 ⋅ mr1 ⋅ rsum_minus mn mrs0) with ((rarg ⋅ rsum_minus mn mrs0 ⋅ mr1) ⋅ fr1) by r_solve.
        eapply URA.updatable_add; et. refl.
      }
      unshelve esplits; et.
      { eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable.
        erewrite <- rsum_minus_rsum with (mn:=mn); et. exists (rsum_minus mn mrs1). r_solve.
      }
      steps. unshelve esplits; et. steps. deflag. gbase. eapply CIH; et. etrans; et.
      replace (rret ⋅ rsum mrs1 ⋅ fr1) with (rret ⋅ fr1 ⋅ rsum mrs1) by r_solve. refl.
    }
    Unfocus.
    { fold sk. fold sk. set (mn0:=SModSem.mn (SMod.get_modsem md sk)) in *.
      unfold fun_to_src, fun_to_tgt, compose. des_ifs. unfold HoareFun, ASSUME, ASSERT, mget, mput.
      steps. exists x.
      steps. esplits; steps.
      eexists rarg. steps. unfold mput, mget. steps.
      erewrite ! zip_state_mput; et. erewrite zip_state_get; et.
      steps.
      assert(UPD0: URA.updatable init_r (rarg ⋅ fr1 ⋅ rsum (update mrs0 mn mr1))).
      { etrans; et.
        erewrite <- rsum_minus_rsum with (mn:=mn); et.
        replace (fr0 ⋅ (rsum_minus mn mrs0 ⋅ mrs0 mn)) with ((fr0 ⋅ mrs0 mn) ⋅ rsum_minus mn mrs0) by r_solve.
        etrans.
        { eapply URA.updatable_add; et. refl. }
        rewrite rsum_update2; ss.
        replace (rarg ⋅ fr1 ⋅ (rsum_minus mn mrs0 ⋅ mr1)) with (rarg ⋅ fr1 ⋅ mr1 ⋅ rsum_minus mn mrs0) by r_solve.
        refl.
      }
      unshelve esplits; eauto.
      { eapply URA.updatable_wf; et. etrans; et. rewrite URA.unit_id.
        rewrite <- URA.add_assoc. eapply URA.updatable_add; try refl. eapply URA.extends_updatable.
        r. eexists (fr1 ⋅ rsum_minus mn0 (update mrs0 mn mr1)); et.
        erewrite <- rsum_minus_rsum; ss; et. r_solve. }
      steps. unshelve esplits; et. steps.
      erewrite idK_spec at 1. unfold idK.
      deflag. guclo bindC_spec. econs.
      { gbase. eapply CIH; ss; try refl.
        eapply URA.updatable_wf; et. etrans; et.
        eapply URA.extends_updatable. r. exists fr1. r_solve. }
      { ii. ss. des_ifs_safe. des; ss. clarify.
        steps.
        rename c1 into fr3. rename c into mr2. rename c0 into rret.
        unfold mput, mget. steps.
        rewrite zip_state_get; et. rewrite Any.pair_split. steps.
        rewrite zip_state_get; et. rewrite Any.pair_split. steps.
        esplits; ss; et.
        { rewrite rsum_update2 in UPD1; ss. rewrite URA.add_assoc in UPD1. rewrite URA.unit_id in UPD1.
          etrans; et. erewrite <- rsum_minus_rsum; et.
          replace (fr2 ⋅ (rsum_minus mn0 mrs1 ⋅ mrs1 mn0)) with(fr2 ⋅ mrs1 mn0 ⋅ rsum_minus mn0 mrs1) by r_solve.
          etrans.
          { eapply URA.updatable_add; et. refl. }
          rewrite rsum_update2; ss. eapply URA.extends_updatable. exists fr3. r_solve. }
      }
    }
  Unshelve.
    all: try (by exact 0).
  Qed.

  Opaque EventsL.interp_Es.

  Context {CONFS: EMSConfig}.
  Context {CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_t2m
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb "main" = main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt r
                              (WFR: URA.wf r)
                              (POST: main_fsp.(postcond) x ret_src ret_tgt r),
                   ret_src = ret_tgt>>)):
    Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt)) <1=
    Beh.of_program (@ModL.compile _ CONFS (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_global_itree; ss.
    ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSemL.initial_itr, ModSemL.initial_itr. Local Opaque ModSemL.prog. ss.
    unfold ITree.map.

    hexploit (stb_find_iff "main"). i. des; clarify.
    { Local Transparent ModSemL.prog.
      seal_right. ss. unfold ms_src in FINDSRC. rewrite FINDSRC. steps.
      Local Opaque ModSemL.prog. }
    hexploit MAINM; et.
    i. des.

    unfold assume.
    steps. unfold ModL.wf in *. des.
    assert (NODUP: List.NoDup (map fst ms_tgt.(ModSemL.initial_mrs))).
    { inv WF. rewrite fst_initial_mrs_eq. unfold ms_src. auto. }
    esplits; et.
    { inv WF. econs; auto. rewrite fns_eq. auto. }
    { rewrite sk_eq. auto. }

    hexploit initial_mrs_exist; auto. i. des.
    steps. fold ms_tgt ms_src. rewrite <- INITIALZIP.

    Local Transparent ModSemL.prog. ss.
    unfold Any_src, Any_src, Any_tgt in *. rewrite FINDTGT. rewrite FINDSRC. steps.
    unfold fun_to_tgt, HoareFun. steps.
    eexists. steps. unfold ASSUME, ASSERT, mput, mget. steps. eexists. steps. eexists entry_r.
    unfold mput, mget. steps.
    rewrite zip_state_get; et.
    rewrite Any.pair_split. steps.
    unshelve esplits; et.
    { rewrite URA.unit_id. eapply URA.wf_extends; et. erewrite <- INITIALRSUM; et.
      exists (rsum_minus (SModSem.mn (SMod.get_modsem md sk)) initial_mrs). r_solve. }
    steps. eexists. steps. unshelve esplits; et. steps.
    assert(RWF: URA.wf (entry_r ⋅ rsum initial_mrs)).
    { r_wf WFR. erewrite <- rsum_minus_rsum; et. }
    steps. unshelve esplits; et. steps.
    guclo bindC_spec. econs.
    { deflag. gfinal. right. fold simg. unfold fun_to_src.
      eapply adequacy_type_aux; ss; et. rewrite URA.unit_id. refl. }
    i. ss.
    destruct vret_src as [mps_src v_src].
    destruct vret_tgt as [mps_tgt [? v_tgt]]. des. clarify.
    steps. unfold mput, mget.
    steps. rewrite zip_state_get; et. rewrite Any.pair_split.
    steps. rewrite zip_state_get; et. rewrite Any.pair_split. steps.
    { eapply RET; [|et]. eapply URA.wf_mon.
      instantiate (1:=ε). rewrite URA.unit_id. eapply URA.updatable_wf; et. etrans; et. etrans; et.
      { instantiate (1:=fr1 ⋅ mrs1 (SModSem.mn (SMod.get_modsem md sk))). eapply URA.extends_updatable.
        erewrite <- rsum_minus_rsum; et. exists (rsum_minus (SModSem.mn (SMod.get_modsem md sk)) mrs1).
        r_solve. }
      etrans; et. eapply URA.extends_updatable. exists (c1 ⋅ c). r_solve.
    }
    Unshelve. all: try (exact 0).
  Qed.

End CANCEL.
