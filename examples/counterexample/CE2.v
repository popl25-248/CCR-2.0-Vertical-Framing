Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.


Global Program Instance EMSConfigSimpl: EMSConfig := {|
  finalize := fun rv => Some rv;
  initial_arg := tt↑;
|}
.

Lemma modseml_step_eq a a' b c (EQ: a = a'): ModSemL.step a b c = ModSemL.step a' b c.
Proof.
  subst. ss.
Qed.

Variant car: Type :=
  | a: car
  | b: car
  | c: car
  | x: car
  | y: car
  | z: car
  | _ax: car
  | _ay: car
  | _bx: car
  | _by: car
  | _bz: car
  | _cy: car
  | _cz: car
  | none: car
  | boom: car
.
Definition add: car -> car -> car :=
  fun c0 c1 =>
    match c0, c1 with
    | a, x => _ax
    | x, a => _ax
    | a, y => _ay
    | y, a => _ay
    | b, x => _bx
    | x, b => _bx
    | b, y => _by
    | y, b => _by
    | b, z => _bz
    | z, b => _bz
    | c, y => _cy
    | y, c => _cy
    | c, z => _cz
    | z, c => _cz
    | none, _ => c1
    | _, none => c0
    | _, _ => boom
    end
.

Program Instance bipartite: URA.t := {
    car := car;
    unit := none;
    _add := add;
    _wf := fun c => c <> boom;
    core := fun _ => none;
  }.
Next Obligation. i. destruct a0, b0; ss. Qed.
Next Obligation. i. destruct a0, b0, c0; ss. Qed.
Next Obligation. i. rewrite Seal.sealing_eq. destruct a0; ss. Qed.
Next Obligation. i. rewrite Seal.sealing_eq. ss. Qed.
Next Obligation. i. rewrite ! Seal.sealing_eq in *. destruct a0, b0; ss. Qed.
Next Obligation. i. rewrite ! Seal.sealing_eq in *. destruct a0; ss. Qed.
Next Obligation. i. ss. Qed.
Next Obligation. i. rewrite ! Seal.sealing_eq in *. esplits; eauto. Qed.

Lemma bipartite_updatable_set_b
  :
  URA.updatable_set b (fun r => r = a \/ r = c)
.
Proof.
  ii. unfold URA.wf, URA.add in *. ss. unseal "ra". ss.
  set ctx as rem. des_ifs; try (by esplits; et).
  esplits. { left; et. } ss.
Qed.

Lemma bipartite_updatable_set_y
  :
  URA.updatable_set y (fun r => r = x \/ r = z)
.
Proof.
  ii. unfold URA.wf, URA.add in *. ss. unseal "ra". ss.
  set ctx as rem. des_ifs; try (by esplits; et).
  esplits. { left; et. } ss.
Qed.



Require Import HoareFacts SimModSem HTactics2.
Require Import ProofMode HSim2 ISim2 IProofMode2 Sealed.

Section DEF.

  (* Context `{Σ: GRA.t}. *)
  (* Context `{@GRA.inG bipartite Σ}. *)
  Let Σ: GRA.t := GRA.of_list [bipartite].
  Let inG: @GRA.inG bipartite Σ.
    exists 0. ss.
  Defined.
  Local Existing Instance Σ.
  Local Existing Instance inG.
  Local Existing Instance HasFreezeY.

  (* Lemma unembed: ∀ (p: Σ), ∃ (q: bipartite), p = GRA.embed q. *)
  (* Proof. *)
  (*   i. unfold Σ in *. ss. unfold GRA.of_list in *. ss. *)
  (*   exists (p 0). extensionality n. unfold GRA.embed. ss. des_ifs. *)
  (*   - destruct (p 1) eqn:T; ss. *)
  (*   - destruct (p (S (S n))) eqn:T; ss. *)
  (* Qed. *)

  (* (*** TODO: move to PCM.v ***) *)
  (* Lemma embed_inj: ∀ p q, GRA.embed p = GRA.embed q -> p = q. *)
  (* Proof. *)
  (*   i. *)
  (*   match goal with *)
  (*   | [H: ?x = ?y |- _ ] => *)
  (*       assert(T:= @equal_f_dep nat Σ x y H); clear H *)
  (*   end. *)
  (*   specialize (T 0). ss. *)
  (* Qed. *)

  (***
Q: remove frozen?
Q: choose in mid overly non-deterministic?
|=+> (x or z)
-------------------
   ***)

  Definition mpost (b: bool) := if (b: bool) then OwnM x else OwnM z.
  Definition spost (b: bool) := if (b: bool) then (OwnM (c: bipartite)) else (OwnM (a: bipartite)).

  (** for both mid and src **)
  Definition prog: Any.t -> itree Es' Any.t :=
    fun _ => b <- trigger (Choose bool);; Ret b↑
  .
  Definition prog_tgt: Any.t -> itree Es' Any.t :=
    fun _ => b <- trigger (Take bool);; Ret b↑
  .

  Definition modsem_tgt: SModSem.t := {|
    SModSem.fnsems := [("f", prog_tgt)];
    SModSem.mn := "";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition module_tgt := {|
    SMod.get_modsem := fun _ => modsem_tgt;
    SMod.sk := Sk.unit;
  |}.

  Definition modsem_mid: SModSem.t := {|
    SModSem.fnsems := [("f", prog)];
    SModSem.mn := "";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition module_mid := {|
    SMod.get_modsem := fun _ => modsem_mid;
    SMod.sk := Sk.unit;
  |}.

  Definition modsem_src: SModSem.t := {|
    SModSem.fnsems := [("f", prog)];
    SModSem.mn := "";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition module_src := {|
    SMod.get_modsem := fun _ => modsem_src;
    SMod.sk := Sk.unit;
  |}.





  Definition fspec_mid: fspec :=
    mk_fspec (λ (_: unit) _ _, (OwnM y)%I)
      (λ _ rm rt, (∃ b, ⌜rt = b↑ ∧ rm = rt⌝ ∧ mpost b))%I.

  Definition fspec_src: fspec :=
    mk_fspec (λ (_: unit) _ _, (OwnM y ** OwnM b)%I)
      (λ _ rs rt, (∃ b, ⌜rt = b↑ ∧ rt = rs⌝ ∧ mpost b ** spost b))%I.

  Definition mainspec_src: fspec :=
    mk_fspec (λ (_: unit) _ _, (OwnM y ** OwnM b)%I)
      (λ _ _ _, False)%I.

  Definition global_stb := (λ fn, if dec "f" fn then fspec_src else
                                    if dec "main" fn then mainspec_src else ε%fspec).

  Definition tgt: Mod.t := SMod.to_src module_tgt.
  Definition mid: Mod.t :=
    SMod.to_tgt (λ _ fn, if dec "f" fn then fspec_mid else ε%fspec) module_mid.
  Definition src: Mod.t :=
    SMod.to_tgt (λ _, global_stb) module_src.

  Let wf := mk_wf (λ (_: unit) st_src st_tgt, True%I).

  Hypothesis ORIGINALUPD: (∀ P, Upd P ≡ WeakUpd P).

  Ltac r_solve :=
    repeat rewrite URA.add_assoc; repeat (try rewrite URA.unit_id; try rewrite URA.unit_idl);
    match goal with
    | |- ?lhs = _ ⋅ _ =>
        let a := r_first lhs in
        try rewrite <- (URA.add_comm (a: bipartite)); repeat rewrite <- URA.add_assoc;
        try (eapply f_equal; r_solve)
    | _ => try reflexivity
    end.

  Theorem ref0
    :
    refines tgt mid
  .
  Proof.
    unfold mid.
    etrans.
    1: { eapply wrap_intro. }
    eapply adequacy_local.
    econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; ss. rr.
         replace (Any.pair tt↑ (Any.upcast (ε: Σ)), Any.pair tt↑ (Any.upcast (ε: Σ))) with
           (Any.pair tt↑ (Any.upcast (ε ⋅ ε: Σ)), Any.pair tt↑ (Any.upcast (ε: Σ))).
         2: { rewrite URA.unit_id. ss. }
         econs; et. eapply to_semantic. iIntros; ss. }
    econs; ss.
    { do 5 r. esplits; ss. r. clear_tac. clears sk. clear_tac.
      eapply adequacy_isim; ss.
      iIntros. des. des_u. ss. clear_tac.
      iModIntro. iIntros. iDes. iModIntro. iSplits; ss. des_ifs. ss.
      unfold prog, prog_tgt. unfold resum_ktr. ss. unfold fun_to_src.
      steps. resub. steps. des_u.
      {
        iAssert (#=> ∃ b, mpost b) with "[PRE]" as "A".
        { unfold bupd, bi_bupd_bupd. ss. rewrite ORIGINALUPD. clear - wf.
          iDestruct (OwnM_WeakUpd_set with "[PRE]") as "A".
          { eapply bipartite_updatable_set_y. }
          { ss. }
          { iApply WeakUpd_mono; et. iIntros. iDes. unfold mpost. des; subst.
            - iExists true; ss.
            - iExists false; ss.
          }
        }
        iMod "A". clear_tac. iDes.
        iApply isim_choose_src. iExists b0. steps.
        iApply isim_take_tgt. iExists b0. steps.
        iIntros. subst. iModIntro. iSplits; ss.
      }
    }
  Unshelve.
    all: ss.
  Qed.

  Theorem ref1
    :
    refines mid src
  .
  Proof.
    unfold mid, src.
    eapply adequacy_local.
    econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; ss. rr.
         replace (Any.pair tt↑ (Any.upcast (ε: Σ)), Any.pair tt↑ (Any.upcast (ε: Σ))) with
           (Any.pair tt↑ (Any.upcast (ε ⋅ ε: Σ)), Any.pair tt↑ (Any.upcast (ε: Σ))).
         2: { rewrite URA.unit_id. ss. }
         econs; et. eapply to_semantic. iIntros; ss. }
    econs; ss. do 5 r. esplits; ss. r. clear_tac. clears sk. clear_tac.
    eapply adequacy_isim; ss.
    iIntros. des. des_u. ss. clear_tac.
    iModIntro. iIntros. iDes. des_ifs. ss. iModIntro. iSplits; ss. iDes. iFrame.
    unfold prog. steps.
    iApply isim_upd_strong; ss. rename y0 into r.
    iAssert (sealed_upd (OwnM (y: bipartite)) (spost r)) with "[PRE1]" as "A".
    { destruct r; ss.
      - iApply sealed_upd_special0.
        { instantiate (1:=GRA.embed b). rewrite ! GRA.embed_add.
             eapply GRA.embed_updatable.
             ii. unfold URA.wf, URA.add in *. unseal "ra". destruct ctx; ss; des_ifs.
        }
        { iApply sealed_upd_ret. ss. }
      - iApply sealed_upd_special0.
        { instantiate (1:=GRA.embed b). rewrite ! GRA.embed_add.
             eapply GRA.embed_updatable.
             ii. unfold URA.wf, URA.add in *. unseal "ra". destruct ctx; ss; des_ifs.
        }
        { iApply sealed_upd_ret. ss. }
    }
    iApply sealed_upd_map; [|eauto]. iIntros. iDes.
    iApply isim_choose_src. iExists r. steps.
    iIntros. iDes. subst. iModIntro. iSplits; ss. iFrame. des; subst.
    apply Any.upcast_inj in H0. des; clarify. iFrame. ss.
  Unshelve.
    all: ss.
  Qed.


  (*** In the above, we have proven "False" as a postcond of "f". ***)
  (*** We would like to get a "closed" counterexample showing "False" outside the logic. ***)
  (*** For this, we will utilize the power of "False" in the logic to constitute a "False" refinement. ***)
  (*** In this "False" refinement, the target behavior is returning 1, and source is 0. ***)
  
  (********** client ***********)

  (** for both tgt and mid **)
  Definition main: Any.t -> itree Es' Any.t :=
    fun _ => trigger (Call "f" tt↑);;; Ret (1: nat)↑
  .

  Definition main_src: Any.t -> itree Es' Any.t :=
    fun _ => trigger (Call "f" tt↑);;; Ret (0: nat)↑
  .

  Definition modsem_clnt_tgt: SModSem.t := {|
    SModSem.fnsems := [("main", main)];
    SModSem.mn := "m";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition module_clnt_tgt := {|
    SMod.get_modsem := fun _ => modsem_clnt_tgt;
    SMod.sk := Sk.unit;
  |}.

  Definition modsem_clnt_src: SModSem.t := {|
    SModSem.fnsems := [("main", main_src)];
    SModSem.mn := "m";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition module_clnt_src := {|
    SMod.get_modsem := fun _ => modsem_clnt_src;
    SMod.sk := Sk.unit;
  |}.

  Definition clnt_tgt: Mod.t := SMod.to_src module_clnt_tgt.
  Definition clnt_src: Mod.t := SMod.to_tgt (λ _, global_stb) module_clnt_src.

  Theorem ref_clnt
    :
    refines clnt_tgt clnt_src
  .
  Proof.
    unfold mid.
    etrans.
    1: { eapply wrap_intro. }
    eapply adequacy_local.
    econs; ss. i.
    econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits; ss. rr.
         replace (Any.pair tt↑ (Any.upcast (ε: Σ)), Any.pair tt↑ (Any.upcast (ε: Σ))) with
           (Any.pair tt↑ (Any.upcast (ε ⋅ ε: Σ)), Any.pair tt↑ (Any.upcast (ε: Σ))).
         2: { rewrite URA.unit_id. ss. }
         econs; et. eapply to_semantic. iIntros; ss. }
    econs; ss.
    { do 5 r. esplits; ss. r. clear_tac. clears sk. clear_tac.
      eapply adequacy_isim; ss.
      iIntros. des. des_u. ss. clear_tac.
      iModIntro. iIntros. iDes. iModIntro. iSplits; ss. des_ifs. ss.
      unfold main, main_src. unfold resum_ktr. ss. unfold fun_to_src. steps. resub. steps. des_u.
      iIntros. iSplits; ss. subst. unfold inv_with. iFrame. iSplits; ss.
      iIntros. iDes. des; subst. clear_tac. iSplits; ss. steps.
      iIntros. subst. iModIntro. iSplits; ss.
      unfold mpost, spost. des_ifs.
      - iCombine "H H1" as "A". iOwnWf "A". unfold URA.wf, URA.add in *. unseal "ra". ss.
      - iCombine "H H1" as "A". iOwnWf "A". unfold URA.wf, URA.add in *. unseal "ra". ss.
    }
  Unshelve.
    all: ss.
  Qed.

  (*** the target returns "1", and the source returns "0". ***)
  Theorem false
    :
    refines_closed (Mod.add_list [clnt_tgt; tgt])
      (Mod.add_list (map SMod.to_src [module_clnt_src; module_src]))
  .
  Proof.
    etrans.
    - eapply refines_close.
      instantiate (1:=(Mod.add_list [clnt_src; src])).
      rewrite ! Mod.add_list_cons. unfold Mod.add_list. ss. rewrite ! ModL.add_empty_r.
      eapply refines_add.
      + eapply ref_clnt.
      + etrans. { eapply ref0. } eapply ref1.
    - unfold src, clnt_src.
      replace ([SMod.to_tgt (λ _, global_stb) module_clnt_src;
               SMod.to_tgt (λ _, global_stb) module_src]) with
        (map (SMod.to_tgt (λ _, global_stb)) [module_clnt_src; module_src]) by refl.
      eapply Hoare.adequacy_type; eauto.
      2: { i. ss. subst. unfold global_stb. ss. iSplits; ss.
           - iIntros "[A B]". iFrame.
           - i. iIntros. ss.
      }
      { cbn. rewrite ! URA.unit_id. rewrite GRA.embed_add. eapply GRA.wf_embed. ss.
        unfold URA.wf, URA.add. unseal "ra". ss.
      }
  Qed.

  Hint Resolve Beh.of_state_mon : paco.
  Goal False.
    assert(T:=false).
    rr in T. ss.
    set (ModL.compile
        (Mod.add_list [SMod.to_src module_clnt_src; SMod.to_src module_src])) as y in *.
    specialize T with (Tr.done 1↑). exploit T.
    { r. ss.
      set (ModL.compile (Mod.add_list [clnt_tgt; tgt])) as x.
      unfold ModSemL.initial_itr. cbn. unfold ITree.map. unfold assume.
      ginit. { eapply cpn2_wcompat. eauto with paco. }
      guclo Beh.astep_clo_spec. econs; ss. i. inv H; ss; irw in H1; csc.
      unfold main, fun_to_src.
      Ltac ired := try (Red.prw IRed._red_gen 2 0).
      ired.
      gstep. { eapply (@Beh.of_state_mon x). } eapply Beh.sb_demonic; ss.
      r. esplits; et.
      { econs; et. }
      unfold prog_tgt. ired.
      econsr; ss. ii. inv STEP; irw in H0; dependent destruction H0.
      esplits; ss.
      ired.
      eapply Beh.sb_demonic; ss. r. esplits; et. { ss. econs; et. }
      ired. eapply Beh.sb_demonic; ss. r. esplits; et. { ss. econs; et. }
      ired. eapply Beh.sb_demonic; ss. r. esplits; et. { ss. econs; et. }
      ired. eapply Beh.sb_demonic; ss. r. esplits; et. { ss. econs; et. }
      ired. eapply Beh.sb_demonic; ss. r. esplits; et. { ss. econs; et. }
      ired. eapply Beh.sb_demonic; ss. r. esplits; et. { ss. econs; et. }
      ired. econs; et.
    }
    clear T. intro T.
    punfold T.
    2: { eapply (@Beh.of_state_mon y). } inv T; ss.
    r in STEP. ss. unfold ModSemL.initial_itr in STEP. ss.
    Ltac ired2 := try (Red.prw IRed._red_gen 3 0).
    specialize (STEP None). exploit STEP; ss; et.
    { unfold assume, ITree.map. ired2. ss. irw. econs; et. }
    clear STEP. intro T; des.

    inv TL; ss.
    r in STEP. ss. des. unfold main_src in *.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { unfold fun_to_src. ired. refl. }
    ss.
    inv STEP0; ss.
    clear - TL.
    inv TL; ss. clear_tac. r in STEP. des. ss.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { unfold fun_to_src. unfold prog. ired. refl. }
    inv STEP0; irw in H0; dependent destruction H0.

    inv TL; ss. clear_tac. r in STEP. ss. des.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { ired. refl. }
    ss.
    inv STEP0; ss.
    clear - TL.


    inv TL; ss. clear_tac. r in STEP. ss. des.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { ired. refl. }
    ss.
    inv STEP0; ss.
    clear - TL.


    inv TL; ss. clear_tac. r in STEP. ss. des.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { ired. refl. }
    ss.
    inv STEP0; ss.
    clear - TL.


    inv TL; ss. clear_tac. r in STEP. ss. des.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { ired. refl. }
    ss.
    inv STEP0; ss.
    clear - TL.

    inv TL; ss. clear_tac. r in STEP. ss. des.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { ired. refl. }
    ss.
    inv STEP0; ss.
    clear - TL.


    inv TL; ss. clear_tac. r in STEP. ss. des.
    match goal with
    | [H: ModSemL.step ?a _ _ |- _] => erewrite modseml_step_eq in H; cycle 1
    end.
    { ired. refl. }
    ss.
    inv STEP0; ss.
    clear - TL.


    inv TL; ss. clear_tac.
    rewrite transl_all_ret in *. rewrite EventsL.interp_Es_ret in *. ss.
    irw in FINAL.
    rewrite interp_src_ret in FINAL. rewrite transl_all_ret in *.
    rewrite EventsL.interp_Es_ret in *. ss.
    irw in FINAL. clarify. eapply Any.upcast_inj in H0. des; ss. dependent destruction EQ0.
  Unshelve.
    { rr. unfold module_src, module_clnt_src. ss.
      unfold modsem_clnt_src, modsem_src.
      econs; ss; cbn.
      - unfold ModSemL.add. ss. repeat (econs; ss).
        { ii; des; ss. }
        { ii; des; ss. }
      - unfold ModSemL.add. ss. repeat (econs; ss).
    }
  Qed.

End DEF.
