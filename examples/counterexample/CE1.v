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

Let RA := (Excl.t unit).


Require Import SimModSem HTactics IProp IPM.
(* Require Import HoareFacts HTactics2. *)
(* Require Import ProofMode HSim2 ISim2 IProofMode2 Sealed. *)

Section DEF.

  (* Let Σ: GRA.t := GRA.of_list [RA]. *)
  (* Let inG: @GRA.inG RA Σ. *)
  (*   exists 0. ss. *)
  (* Defined. *)
  (* Local Existing Instance Σ. *)
  (* Local Existing Instance inG. *)
  Context `{@GRA.inG RA Σ}.
  (* Local Existing Instance HasFreezeN. *)

  Definition tok: RA := (Excl.just tt).

  Definition fspec_tgt: fspec :=
    mk_simple (λ (_: unit), ((λ _, True%I), (λ rt, OwnM tok%I))).

  Definition fspec_src: fspec :=
    mk_simple (λ (_: unit), ((λ _, True%I), (λ rt, False%I))).

  Definition fspec_frame: fspec :=
    mk_simple (λ (_: unit), ((λ _, OwnM tok%I), (λ rt, OwnM tok%I))).

  (** for both mid and src **)
  Definition prog: Any.t -> itree Es' Any.t := fun x => Ret x.

  Definition modsem_tgt: SModSem.t := {|
    SModSem.fnsems := [("f", prog)];
    SModSem.mn := "";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition module_tgt := {|
    SMod.get_modsem := fun _ => modsem_tgt;
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


  Definition Conds :=
    fun str =>
      match alist_find str ([("f", fspec_tgt)])
      with
      | Some res => res
      | _ => ε%fspec
      end.

  Definition CondsB :=
    fun str =>
      match alist_find str ([("f", fspec_src)])
      with
      | Some res => res
      | _ => ε%fspec
      end.



  Definition tgt: Mod.t := SMod.to_tgt (fun _ => Conds) module_tgt.
  Definition src: Mod.t := SMod.to_tgt (fun _ => CondsB) module_src.

  Ltac steps := HTactics.steps.
  Theorem ref
    :
    refines tgt src
  .
  Proof.
    unfold tgt, src.
    eapply adequacy_local.
    econs; ss. i.
    econstructor 1 with (wf := fun (_: unit) '(x, y) => x = y /\ x = Any.pair tt↑ (ε:Σ)↑) (le := top2); ss.
    econs; ss.
    rr. split; ss. rr. i; ss. subst.
    unfold fun_to_tgt, prog. ss.
    des. subst.
    ginit.
    Local Transparent HoareFun handle_condE_tgt.
    unfold HoareFun.
    steps.
    unfold ASSUME, ASSERT.
    steps.
    rename x1 into xxx.
    unfold mput, mget.
    steps.
    force_r.
    esplits; et. steps.
    force_r. esplits; et. steps.
    force_r. exists ε. esplits; et. steps.
    unfold mput, mget.
    steps.
    force_r; et.
    { rewrite ! URA.unit_id. eapply URA.wf_unit. }
    steps.
    force_r; et.
    { rr. uipropall. esplits; rr; uipropall; et. }
    steps.
    unfold mput, mget.
    steps.
    exfalso.
    clear - _GUARANTEE _GUARANTEE0.
    rr in _GUARANTEE0. uipropall. des.
    rr in _GUARANTEE0. uipropall.
    rr in _GUARANTEE0. des. subst.
    clear - _GUARANTEE. rename _GUARANTEE into T.
    r in T.
    specialize (T (GRA.embed tok)).
    exploit T; et.
    { rewrite ! URA.unit_idl. eapply GRA.wf_embed.
      rr. unseal "ra". ss.
    }
    clear T; intro U.
    assert(URA.wf ((GRA.embed (tok ⋅ tok)))).
    { rewrite <- GRA.embed_add. eapply URA.wf_extends; et. exists (ctx ⋅ c1 ⋅ c). r_solve. }
    clear - H0.
    eapply GRA.embed_wf in H0.
    rr in H0. unseal "ra". ss. unfold tok in *.
    unfold URA.add in *. unseal "ra". ss.
  Unshelve.
    all: ss.
  Qed.

End DEF.
