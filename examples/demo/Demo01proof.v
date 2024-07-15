Require Import HoareDef DemoHeader Demo0 Demo1 SimModSem.
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

Require Import STB ProofMode.
Require Import HTactics2 HSim2 ISim2 IProofMode2.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Variable Σ: GRA.t.
  Context `{arbitrary_props}.
  Local Existing Instance HasFreezeN.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ st_tgt => True%I)
  .

  Theorem correct: refines2 [Demo0.Demo (fun _ => GlobalStb0)] [Demo1.Demo (fun _ => GlobalStb1)].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss; et; swap 2 3.
    { esplits. rp; [econs|..]; try refl; cycle 1.
      { repeat f_equal. rewrite URA.unit_idl; ss. }
      eapply to_semantic. iIntros "H". iSplits; ss. }

    econs; [|ss].
    (*** (Demo 1) Hoare Quadruple like in Simuliris ***)
    { econs; r; ss. eapply adequacy_isim; ss.
      iIntros. des. clear_tac.
      (*** [PROOF STATUS]
             SRC:   ASSUME(P); body; ASSERT(Q); return
                  ↑
             TGT:              body;            return
                  ↑
       ***)
      iModIntro. iIntros. iDes. ss. iDes. subst.
      (*** [PROOF STATUS]
             RES: P
             SRC:   ASSUME(P); body; ASSERT(Q); return
                              ↑
             TGT:              body;            return
                  ↑
       ***)
      iModIntro. iSplits; ss.
      (*** Execute program body ***)
      steps.
      (*** [PROOF STATUS]
             RES: P
             SRC:   ASSUME(P); body; ASSERT(Q); return
                                    ↑
             TGT:              body;            return
                                    ↑
       ***)
      (*** Now, prove the postcondition. ***)
      iIntros; subst.
      iDestruct (implication with "[$]") as ">PRE". iFrame.
      (*** [PROOF STATUS]
             SRC:   ASSUME(P); body; ASSERT(Q); return
                                               ↑
             TGT:              body;            return
                                    ↑
       ***)
      iModIntro. iSplits; ss.
      (*** [PROOF STATUS]
             SRC:   ASSUME(P); body; ASSERT(Q); return
                                                       ↑
             TGT:              body;            return
                                                       ↑
       ***)
    }
    econs; [|ss].
    (*** (Demo 2) Horizontal (usual) Frame Rule ***)
    { econs; r; ss. eapply adequacy_isim; ss.
      iIntros. des. clear_tac.
      (*** [PROOF STATUS]
             SRC:   ASSUME(X * P); body; ASSERT(X * Q); return
                  ↑
             TGT:                  body;            return
                  ↑
       ***)
      iModIntro. iIntros. iDes. ss. iDes. subst.
      (*** [PROOF STATUS]
             RES: X * P
             SRC:   ASSUME(X * P); body; ASSERT(X * Q); return
                                  ↑
             TGT:                  body;            return
                  ↑
       ***)
      iModIntro. iSplits; ss.
      (*** Execute program body ***)
      steps.
      (*** [PROOF STATUS]
             RES: X * P
             SRC:   ASSUME(X * P); body; ASSERT(X * Q); return
                                        ↑
             TGT:                  body;            return
                                        ↑
       ***)
      (*** Now, prove the postcondition. ***)
      (*** [[[POINT]]] The frame, X, is discharged here. ***)
      iIntros; subst. iFrame; ss.
      (*** Below is same as before. ***)
      iDestruct (implication with "[$]") as ">A". iFrame; ss.
    }
    econs; [|ss].
    (*** (Demo 3) Vertical Frame Rule ***)
    { econs; r; ss. eapply adequacy_isim; ss.
      iIntros. des. clear_tac.
      (*** [PROOF STATUS]
             SRC:   ASSUME(X * P); body; ASSERT(Y * Q); return
                  ↑
             TGT:   ASSUME(X);     body; ASSERT(Y);     return
                  ↑
       ***)
      iModIntro. iIntros. iDes. ss. iDes. subst.
      (*** [PROOF STATUS]
             RES: X * P
             SRC:   ASSUME(X * P); body; ASSERT(Y * Q); return
                                  ↑
             TGT:   ASSUME(X);     body; ASSERT(Y);     return
                  ↑
       ***)
      (*** [[[POINT]]] The frame, X, is discharged here. ***)
      iModIntro. iFrame. iSplits; ss.
      (*** [PROOF STATUS]
             RES: P
             SRC:   ASSUME(X * P); body; ASSERT(Y * Q); return
                                  ↑
             TGT:   ASSUME(X);     body; ASSERT(Y);     return
                                  ↑
       ***)
      (*** Execute program body ***)
      steps.
      (*** [PROOF STATUS]
             RES: P
             SRC:   ASSUME(X * P); body; ASSERT(Y * Q); return
                                        ↑
             TGT:   ASSUME(X);     body; ASSERT(Y);     return
                                        ↑
       ***)
      (*** Now, prove the postcondition. ***)
      (*** [[[POINT]]] We get Y from the target. ***)
      iIntros; subst. iDes.
      (*** [PROOF STATUS]
             RES: P
             SRC:   ASSUME(X * P); body; ASSERT(Y * Q); return
                                        ↑
             TGT:   ASSUME(X);     body; ASSERT(Y);     return
                                                       ↑
       ***)
      (*** [[[POINT]]] The frame, Y, is discharged here. ***)
      iFrame; ss.
      (*** Below is same as before. ***)
      iDestruct (implication with "[$]") as ">A". iFrame; ss.
    }
  Unshelve. all: ss.
  Qed.

End SIMMODSEM.

