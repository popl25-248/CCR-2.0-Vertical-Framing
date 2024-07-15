Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Export HoareDef STB.
Require Import Hoareproof0.
Require Import SimModSem ProofMode.

Set Implicit Arguments.



Lemma fold_right_map
      XS XI YS YI
      (xs: XS) (xi: list XI)
      (xadd: XI -> XS -> XS)

      (* (ys: YS) (yi: list YI) *)
      (yadd: YI -> YS -> YS)

      (fs: XS -> YS)
      (fi: XI -> YI)
      (HOM: forall xi xs, fs (xadd xi xs) = yadd (fi xi) (fs xs))
  :
    <<EQ: fs (fold_right xadd xs xi) = fold_right yadd (fs xs) (List.map fi xi)>>
.
Proof.
  r. ginduction xi; ii; ss.
  rewrite HOM. f_equal. eapply IHxi; et.
Qed.

(*** TODO: move to Coqlib ***)
Lemma find_app
      X (xs0 xs1: list X) (f: X -> bool) x
      (FIND: find f xs0 = Some x)
  :
    <<FIND: find f (xs0 ++ xs1) = Some x>>
.
Proof.
  revert_until xs0. induction xs0; ii; ss. des_ifs. erewrite IHxs0; et.
Qed.











Section CANCELSTB.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.

  Let sk: Sk.t := SMod.get_sk mds.

  Let _mss: Sk.t -> list SModSem.t := fun sk => (List.map ((flip SMod.get_modsem) sk) mds).

  Let mss: list SModSem.t := _mss sk.

  Variable stb: Sk.t -> gname -> fspec.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.



  Let W: Type := p_state.
  (* Let wf: Ord.t -> W -> W -> Prop := top3. *)

  Opaque EventsL.interp_Es.

  Let ms_src: ModSemL.t := ModL.enclose (Mod.add_list mds_src).
  Let ms_tgt: ModSemL.t := ModL.enclose (Mod.add_list mds_tgt).

  Section STRONGER.
  Context {CONFS CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_arg_stb
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<WFR: URA.wf (entry_r ⋅ fold_left (⋅) (List.map SModSem.initial_mr mss) ε)>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt)) <1=
      Beh.of_program (@ModL.compile _ CONFS (Mod.add_list mds_src)).
  Proof.
    ii. eapply adequacy_type_t2m; et.
    i. exploit MAINM; et. i. des. esplits; et.
    i. specialize (RET ret_src ret_tgt). uipropall.
    hexploit RET; et. i. rr in H. uipropall.
    all:ss.
  Qed.
  End STRONGER.


  Context {CONF: EMSConfig}.
  Variable entry_r: Σ.

  Hypothesis WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk).

  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb sk "main" = main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) x initial_arg initial_arg>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type_stb: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg_stb; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    { eapply to_semantic.
      { eapply PRE.  }
      { eapply URA.wf_mon; et. }
    }
    { r_wf WFR. unfold SMod.get_initial_mrs. ss. unfold mss, _mss.
      rewrite List.map_map. ss. }
  Qed.

End CANCELSTB.


Section CANCEL.

  Context `{Σ: GRA.t}.

  Variable mds: list SMod.t.
  Variable stb: Sk.t -> gname -> fspec.

  Let sk: Sk.t := SMod.get_sk mds.

  Let mds_src: list Mod.t := List.map (SMod.to_src) mds.
  Let mds_tgt: list Mod.t := List.map (SMod.to_tgt stb) mds.

  Section STRONGER.
  Context {CONFS CONFT: EMSConfig}.
  Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

  Theorem adequacy_type_arg
          (MAINM:
             forall (main_fsp: fspec) (MAIN: stb sk "main" = main_fsp),
             exists (x: main_fsp.(meta)) entry_r,
               (<<PRE: main_fsp.(precond) x (@initial_arg CONFS) (@initial_arg CONFT) entry_r>>) /\
               (<<WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk)>>) /\
               (<<RET: forall ret_src ret_tgt,
                   ((main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ ⌜ret_src = ret_tgt⌝)>>))
    :
      Beh.of_program (@ModL.compile _ CONFT (Mod.add_list mds_tgt)) <1=
      Beh.of_program (@ModL.compile _ CONFS (Mod.add_list mds_src)).
  Proof.
    eapply adequacy_type_arg_stb; et.
    { i. hexploit MAINM; et. i. des. esplits; et.
      r_wf WFR. rewrite map_map. ss. }
  Qed.

  End STRONGER.

  Context {CONF: EMSConfig}.
  Variable entry_r: Σ.

  Hypothesis WFR: URA.wf (entry_r ⋅ SMod.get_initial_mrs mds sk).

  Section TYPE0.
  Hypothesis MAINM: forall (main_fsp: fspec) (MAIN: stb sk "main" = main_fsp),
      exists (x: main_fsp.(meta)),
        (<<PRE: Own (entry_r) -∗ main_fsp.(precond) x initial_arg initial_arg>>) /\
        (<<RET: forall ret_src ret_tgt,
            (main_fsp.(postcond) x ret_src ret_tgt: iProp) -∗ (⌜ret_src = ret_tgt⌝)>>).

  Theorem adequacy_type: refines_closed (Mod.add_list mds_tgt) (Mod.add_list mds_src).
  Proof.
    ii. eapply adequacy_type_arg; et.
    i. hexploit MAINM; et. i. des. esplits; et.
    { eapply to_semantic.
      { uipropall. }
      { eapply URA.wf_mon; et. }
    }
  Qed.
  End TYPE0.

End CANCEL.




