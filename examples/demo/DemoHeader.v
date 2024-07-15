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
Require Import ProofMode.

Set Implicit Arguments.



Class arbitrary_props `{Σ: GRA.t} := {
  X: iProp;
  Y: iProp;
  P: iProp;
  Q: iProp;
  implication: P ==∗ Q;
}.
  
Section PROOF.

  Variable Σ: GRA.t.
  Context `{arbitrary_props}.

  Definition e_spec0: fspec := fspec_trivial.
  Definition e_spec1: fspec :=
    mk_simple (fun (_: unit) => (
                                  (fun _ => (P)),
                                  (fun _ => (Q)))).

  Definition f_spec0: fspec := fspec_trivial.
  Definition f_spec1: fspec :=
    mk_simple (fun (_: unit) => (
                                  (fun _ => (X ** P)),
                                  (fun _ => (X ** Q)))).

  Definition g_spec0: fspec :=
    mk_simple (fun (_: unit) => (
                                  (fun _ => X),
                                  (fun _ => Y))).
  Definition g_spec1: fspec :=
    mk_simple (fun (_: unit) => (
                                  (fun _ => (X ** P)),
                                  (fun _ => (Y ** Q)))).

  Definition GlobalStb0: gname -> fspec.
    (* eapply (Seal.sealing "stb"). *)
    set (a:=[("e", e_spec0); ("f", f_spec0); ("g", g_spec0)]).
    eapply (fun fn => match alist_find fn a with | Some fs => fs | _ => ε%fspec end).
  Defined.

  Definition GlobalStb1: gname -> fspec.
    (* eapply (Seal.sealing "stb"). *)
    set (a:=[("e", e_spec1); ("f", f_spec1); ("g", g_spec1)]).
    eapply (fun fn => match alist_find fn a with | Some fs => fs | _ => ε%fspec end).
  Defined.

  (* Definition GlobalStb0: gname -> option fspec := to_stb [("f", f_spec0); ("g", g_spec); ("h", h_spec0)]. *)
  (* Definition GlobalStb1: gname -> option fspec := to_stb [("f", f_spec1); ("g", g_spec); ("h", h_spec1)]. *)

  (***
(f) arg/ret only
(g) tgt call meaningful spec
(h) tgt call trivial spec

update
module resource
APC
   ***)
End PROOF.

Global Hint Unfold GlobalStb0: stb.
Global Hint Unfold GlobalStb1: stb.

(*** TODO: move to PCM.v ***)
Lemma GRA_unit: ∀ {A : URA.t} {Σ : GRA.t} {H : GRA.inG A Σ}, GRA.embed (ε: A) = ε.
Proof.
 i. destruct H. subst. unfold GRA.embed.
 Local Transparent GRA.to_URA.
 unfold GRA.to_URA.
 cbn.
 Local Opaque GRA.to_URA.
 eapply func_ext_dep. i. des_ifs.
Qed.
