Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import DemoHeader.

Set Implicit Arguments.



Section PROOF.
  Variable Σ: GRA.t.
  Context `{arbitrary_props}.

  Definition demoSbtb: list (gname * (Any.t -> itree Es' Any.t)) :=
    [("e", (fun _ => Ret 42↑));
     ("f", (fun _ => Ret 42↑));
     ("g", (fun _ => Ret 42↑))].

  Definition SDemoSem: SModSem.t := {|
    SModSem.fnsems := demoSbtb;
    SModSem.mn := "Demo";
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SDemo: SMod.t := {|
    SMod.get_modsem := fun _ => SDemoSem;
    SMod.sk := [];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> fspec.
  Definition Demo: Mod.t := (SMod.to_tgt GlobalStb) SDemo.
End PROOF.

