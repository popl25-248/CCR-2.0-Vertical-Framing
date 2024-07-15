Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef STB.
Require Import SimModSem ProofMode.
Require Import AList.
Require Import HTactics HSim ISim.
Require Import IProofMode.
Require Import IRed Red.
Require Hoare.

Set Implicit Arguments.



Section PROOF.
  Context `{Σ: GRA.t}.
  Context `{EMSConfig}.

  Let wf: _ -> _ -> Prop :=
    @mk_wf
      _ unit
     (fun (_:unit) st_src st_tgt => ⌜st_src = st_tgt⌝%I)
  .

  Theorem wrap_intro_aux
    (ms: ModSem.t)
    :
    ModSemPair.sim (SModSem.to_tgt (fun _ => ε%fspec) (SModSem.from ms)) ms
  .
  Proof.
    econstructor 1 with
      (wf:=wf)
      (le:=top2); et; swap 2 3.
    { ss. }
    { ss. esplits; ss. econs; ss. eapply to_semantic. iIntros. iPureIntro. esplits; ss. }
    destruct ms. ss. clear_tac.
    eapply Forall2_fmap_l.
    eapply Forall2_fmap_l.
    eapply Reflexive_instance_0.
    ii. ss. des_ifs. ss. rr. esplits; ss. r.
    {
      ss.
      ii; subst; ss. des_u.
      unfold resum_ktr.
      rename y into arg. rename k0 into ktr.
      (* ginit. revert_until fnsems. clear_tac. gcofix CIH. i. *)
      eapply isim_fun_to_tgt; ss.
      i. des_u. iIntros "A". iDes. unfold inv_with. iDes. des_u; subst; ss.
      iDestruct "PRE" as "%A". subst. clear_tac.
      abstr (ktr arg_tgt) itr. clear_tac.
      iClear "INV".

      iStopProof.
      eapply isim_final. i.
      guclo hflagC_spec. econstructor 1 with (f_src0 := false) (f_tgt0 := false); ss.
      revert_until wf. gcofix CIH. i.
      eapply isim_init; try apply CUR; clear CUR.
      iIntros "_".

      ides itr.
      { steps. iSplits; ss. }
      { steps. iStopProof. eapply isim_final. i. gstep. econsr; et. gbase. eapply CIH; ss. et. }
      { rewrite <- bind_trigger.
        destruct e; ss.
        { destruct c; ss. resub. steps. resub.
          iApply isim_call_impure; et.
          { econs; eauto. ii. iIntros "A". iModIntro. iAssumption. }
          iSplits; ss. iSplitL; ss. iIntros. subst. destruct H; clear H. des; subst. clear_tac.
          steps.
          iStopProof.
          eapply isim_final. i. guclo hflagC_spec. econs.
          { gbase. eapply CIH; et. }
          { ss. }
          { ss. }
        }
        destruct s; ss.
        { destruct p; ss; resub; steps; resub; steps.
          - iStopProof. eapply isim_final. i. gstep. econsr; et. { gbase. eapply CIH; et. }
          - iStopProof. eapply isim_final. i. gstep. econsr; et. { gbase. eapply CIH; et. }
        }
        { destruct e; ss; resub; steps; resub; steps.
          - iApply isim_choose_src. iSplits; ss. steps.
            iStopProof. eapply isim_final. i. gstep. econsr; et. { gbase. eapply CIH; et. }
          - iApply isim_take_tgt. iSplits; ss. steps.
            iStopProof. eapply isim_final. i. gstep. econsr; et. { gbase. eapply CIH; et. }
          - iApply isim_syscall. iIntros. steps.
            iStopProof. eapply isim_final. i. gstep. econsr; et. { gbase. eapply CIH; et. }
        }
      }
    }
    Unshelve.
    all: ss.
  Qed.

  Theorem wrap_intro
    (ms: Mod.t)
    :
    refines ms (SMod.to_tgt (fun _ => ε%stb) (SMod.from ms))
  .
  Proof.
    eapply adequacy_local.
    econs; et.
    ii. eapply wrap_intro_aux.
  Qed.

  Lemma snoc_map
          X Y (f: X -> Y) xs x
    :
    map f (snoc xs x) = snoc (map f xs) (f x)
  .
  Proof.
    induction xs; ii; ss. congruence.
  Qed.

  Lemma from_to_src
    (md: Mod.t)
    :
    refines (SMod.to_src (SMod.from md)) md
  .
  Proof.
    eapply adequacy_local. econs; ss.
    i; ss.
    econstructor 1 with
      (wf:=fun (_: unit) '(st_src, st_tgt) => st_src = st_tgt)
      (le:=top2); ss.
    eapply Forall2_fmap_r. eapply Forall2_fmap_r.
    eapply Reflexive_instance_0.
    ii. ss. des_ifs. clear_tac. econs; ss. ii. subst. des_u. ss. rename i into ktr.
    clear_tac. clears sk. clear_tac.
    unfold fun_to_src, resum_ktr. ss. abstr (ktr y) itr. clear_tac.
    ginit. revert_until wf. gcofix CIH. i.
    ides itr; ss.
    - HTactics.steps.
    - HTactics.steps. gstep. econsr; et. gbase. eapply CIH; et.
    - rewrite <- ! bind_trigger. resub.
      HTactics.steps. destruct e; ss.
      { destruct c; ss. resub. steps. resub. HTactics.steps.
        gstep. econsr; et. gbase. eapply CIH; et.
      }
      destruct s; ss.
      { resub. steps. resub. HTactics.steps.
        destruct p; ss; HTactics.steps.
        - gstep. econsr; et. gbase. eapply CIH; et.
        - gstep. econsr; et. gbase. eapply CIH; et.
      }
      { resub. steps. resub. HTactics.steps.
        destruct e; ss; HTactics.steps.
        - gstep. econs; et. esplits; et. econsr; et. gbase. eapply CIH; et.
        - eapply sim_itreeC_spec. econs; et. esplits; et. HTactics.steps.
          gstep. econsr; et. gbase. eapply CIH; et.
        - gstep. econsr; et. gbase. eapply CIH; et.
      }
  Qed.

  Theorem wrap_elim
    (ms: Mod.t)
    :
    refines (SMod.to_tgt (fun _ => ε%stb) (SMod.from ms)) ms
  .
  Proof.
    Local Transparent HoareFun HoareCall handle_condE_tgt.
    eapply adequacy_local.
    econs; et.
    i.
    econstructor 1 with
      (wf:=fun (_: unit) '(st_src, st_tgt) =>
             ∃ c, URA.updatable ε c ∧ (Any.pair st_src (c: Σ)↑) = st_tgt)
      (le:=top2); et; swap 2 3.
    { ss. }
    { ss. esplits; et; ss. }
    destruct ms. ss. clear_tac.
    eapply Forall2_fmap_r.
    eapply Forall2_fmap_r.
    eapply Reflexive_instance_0.
    ii. ss. des_ifs. ss. rr. esplits; ss. r.
    {
      ss.
      ii; subst; ss. des_u.
      unfold resum_ktr.
      rename y into arg. rename i into ktr.
      clears sk. clear_tac. revert_until wf.
      ginit. gcofix CIH. i.
      unfold fun_to_tgt, HoareFun, ASSUME, ASSERT.
      HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
      HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
      HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
      unfold mput, mget, assume, guarantee.
      HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
      { rewrite ! URA.unit_idl. eapply URA.updatable_wf; et. eapply URA.wf_unit; ss. }
      HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
      { rr. uipropall. }
      HTactics.steps. erewrite (idK_spec (ktr arg)).
      guclo lbindC_spec. econs.
      { rewrite <- idK_spec. rewrite URA.unit_id.
        abstr (ktr arg) itr. clear_tac.
        guclo lflagC_spec. econs.
        2: { instantiate (1:=false). ss. }
        2: { instantiate (1:=false). ss. }
        assert(T: URA.updatable (ε: Σ) ε) by refl.
        revert T.
        generalize (ε: Σ) at 3 6.
        revert_until CIH. gcofix CIH. i.
        ides itr.
        - HTactics.steps.
          instantiate (1:=fun st_src st_tgt rt rs =>
                            ∃ c0 c1, (Any.pair st_src (c0: Σ)↑) = st_tgt
                           /\ rs = ((c1: Σ), rt) ∧ URA.updatable ε c0 ∧ URA.updatable ε c1
                      ).
          ss. esplits; et.
        - HTactics.steps.
          gstep. eapply sim_itree_progress; et.
          gbase. eapply CIH0; ss.
        - rewrite <-! bind_trigger. resub. HTactics.steps.
          destruct e; ss; resub.
          { destruct c1; ss; resub.
            * HTactics.steps.
              resub.
              match goal with
              | |- context [ @subevent ?E ?F ?X ?Y (?e|)%sum ] =>
                  replace (@subevent E F X Y (e|)%sum) with (@subevent _ F _ Y e)
              end.
              2: { ss. }
              (*** TODO: fix resub ***)
              HTactics.steps.
              unfold HoareCall, ASSUME, ASSERT.
              HTactics.steps. unfold mput, mget, assume, guarantee.
              HTactics.steps. rr in x2. uipropall. subst.
              eapply sim_itreeC_spec. econs; et.
              { esplits; [|et]. rewrite <- (URA.unit_idl ε). etrans; et.
                { eapply URA.updatable_add.
                  - eapply T.
                  - eapply SIMMRS.
                }
                etrans; et.
                eapply URA.extends_updatable. exists (c3 ⋅ c2). r_solve. }
              i. des. subst. des_u.
              HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
              HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
              unfold mput, mget, assume, guarantee.
              HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
              { rewrite URA.unit_idl. eapply URA.updatable_wf; et.
                { instantiate (1:=ε ⋅ ε ⋅ ε). rewrite ! URA.unit_id. eapply URA.wf_unit. }
                eapply URA.updatable_add; et. etrans; et.
                { eapply URA.updatable_add.
                  - eapply T.
                  - eapply SIMMRS.
                }
                etrans; et.
                eapply URA.extends_updatable. exists (c1 ⋅ c2). r_solve.
              }
              HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
              { rr. uipropall. }
              HTactics.steps. rewrite URA.unit_idl.
              gstep. econsr; et.
              gbase. eapply CIH0; et.
              { rewrite <- (URA.unit_idl ε). etrans; et.
                { eapply URA.updatable_add.
                  - eapply T.
                  - eapply SIMMRS.
                }
                etrans; et.
                eapply URA.extends_updatable. exists (c1 ⋅ c2). r_solve. }
          }
          destruct s; ss.
          { destruct p; ss; resub;
              match goal with
              | |- context [ @subevent ?E ?F ?X ?Y (|?e|)%sum ] =>
                  replace (@subevent E F X Y (|e|)%sum) with (@subevent _ F _ Y e) by ss
              end.
            - HTactics.steps. gstep. econsr; et. gbase. eapply CIH0; et.
            - HTactics.steps. gstep. econsr; et. gbase. eapply CIH0; et.
          }
          { destruct e; ss; resub;
              match goal with
              | |- context [ @subevent ?E ?F ?X ?Y (||?e)%sum ] =>
                  replace (@subevent E F X Y (||e)%sum) with (@subevent _ F _ Y e) by ss
              end.
            - HTactics.steps. gstep. econs; et. esplits; et. econsr; et. gbase. eapply CIH0; et.
            - HTactics.steps. eapply sim_itreeC_spec. econs; et. esplits; et.
              HTactics.steps. gstep. econs; et. gbase. eapply CIH0; et.
            - HTactics.steps. gstep. econsr; et. gbase. eapply CIH0; et.
          }
      }
      i. ss. des; clarify.
      unfold idK.
      HTactics.steps. unfold mput, mget, assume, guarantee.
      HTactics.steps. rr in x1. uipropall. subst. rr. esplits; ss.
      { rewrite <- (URA.unit_idl ε). etrans; et.
        { eapply URA.updatable_add.
          - eapply SIM2.
          - eapply SIM1.
        }
        etrans; et.
        eapply URA.extends_updatable. exists (c3 ⋅ c4). r_solve. }
    }
    Unshelve.
    all: ss.
  Qed.

  (* Theorem wrap_elim *)
  (*   (ms: Mod.t) *)
  (*   : *)
  (*   refines (SMod.to_tgt (fun _ => ε%stb) (SMod.from ms)) ms *)
  (* . *)
  (* Proof. *)
  (*   { *)
  (*     red. intro. *)
  (*     assert(T: Beh.of_program *)
  (*                 (ModL.compile (ModL.add (Mod.add_list ctx) *)
  (*                                  (SMod.to_tgt (fun _ => ε%stb) (SMod.from ms)))) *)
  (*               <1= *)
  (*                 Beh.of_program (ModL.compile (ModL.add *)
  (*                                                 (Mod.add_list (map (SMod.to_tgt (fun _ => ε%stb)) (map SMod.from ctx))) *)
  (*                                                 (SMod.to_tgt (fun _ => ε%stb) (SMod.from ms))))). *)
  (*     { admit "ez - apply wrap_intro". } *)
  (*     i. eapply T in PR. *)
  (*     replace (ModL.add (Mod.add_list (map (SMod.to_tgt (fun _ => ε%stb)) (map SMod.from ctx))) *)
  (*                (SMod.to_tgt (fun _ => ε%stb) (SMod.from ms))) *)
  (*       with *)
  (*       (Mod.add_list (map (SMod.to_tgt (fun _ => ε%stb)) (snoc (map SMod.from ctx) (SMod.from ms)))) in PR; cycle 1. *)
  (*     { rewrite <- Mod.add_list_snoc. f_equal. rewrite snoc_map. ss. } *)
  (*     eapply Hoareproof0.adequacy_type_t2m in PR; et. *)
  (*     { *)
  (*       assert(U: *)
  (*               Beh.of_program *)
  (*                 (ModL.compile (Mod.add_list (map SMod.to_src (snoc (map SMod.from ctx) (SMod.from ms))))) *)
  (*               <1= *)
  (*                 Beh.of_program *)
  (*                   (ModL.compile (Mod.add_list (snoc ctx ms))) *)
  (*             ). *)
  (*       { admit "ez - apply from_to_src". } *)
  (*       apply U in PR. *)
  (*       ss. rewrite Mod.add_list_snoc in PR. ss. *)
  (*     } *)
  (*     ii; ss. unfold stb_unit in MAIN. subst. ss. *)
  (*     esplits; ss; et. *)
  (*     { rr. uipropall. } *)
  (*     { admit "ez - After rebasing on top of RCL, move this to opsem". } *)
  (*     { ii; ss. rr in POST. uipropall. } *)
  (*   } *)
  (* Unshelve. *)
  (*   eapply ε. *)
  (* Qed. *)
  Context {stb_equiv_Proper: Proper ((eq ==> (≡)%stb) ==> eq ==> refines) SMod.to_tgt}.

  (*** generalized CCR ***)
  Definition gccr (sb: stb) (md_src md_tgt: SMod.t): Prop :=
    ∀ fr, refines (SMod.to_tgt (fun _ => fr) md_src) (SMod.to_tgt (fun _ => fr |> sb)%stb md_tgt)
  .

  (*** enhanced vertical compositionality ***)
  Theorem gccr_vcomp
    sb0 sb1
    md0 md1 md2
    (REF0: gccr sb0 md0 md1)
    (REF1: gccr sb1 md1 md2)
    :
    gccr (sb0 |> sb1) md0 md2
  .
  Proof.
    unfold gccr in *. i.
    etrans.
    { eapply REF0. }
    etrans.
    { eapply REF1. }
    eapply stb_equiv_Proper; et. red. i. subst.
    rewrite stb_append_assoc. refl.
  Qed.

  Definition ggccr (sb0 sb1: stb) (md_src md_tgt: SMod.t): Prop :=
    ∀ fr, refines (SMod.to_tgt (fun _ => fr |> sb0)%stb md_src) (SMod.to_tgt (fun _ => fr |> sb1)%stb md_tgt)
  .

  (*** enhanced vertical compositionality ***)
  Theorem ggccr_vcomp
    sb0 sb1 sb2
    md0 md1 md2
    (REF0: ggccr sb0 sb1 md0 md1)
    (REF1: ggccr sb1 sb2 md1 md2)
    :
    ggccr sb0 sb2 md0 md2
  .
  Proof.
    unfold ggccr in *. i.
    etrans.
    { eapply REF0. }
    etrans.
    { eapply REF1. }
    eapply stb_equiv_Proper; et. red. i. subst.
    refl.
  Qed.

End PROOF.
