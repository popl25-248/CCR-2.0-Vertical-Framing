Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB IPM.
Require Import MapHeader.

Set Implicit Arguments.


(*** module A Map
private map := (fun k => 0)

def init(sz: int) ≡
  skip

def get(k: int): int ≡
  return map[k]

def set(k: int, v: int) ≡
  map := map[k ← v]
***)

Section A.
  Context `{@GRA.inG MapRA1 Σ}.
  Context `{@GRA.inG memRA Σ}.

  Let Es := Es'.

  Definition initF: list val -> itree Es val :=
    fun varg =>
      Ret Vundef
  .

  Definition setF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      f <- pget;;
      _ <- pput (fun n => if Z.eq_dec n k then v else f n);;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      f <- pget;;
      Ret (Vint (f k))
  .

  Definition MapSbtb: list (string * _) :=
    [("init", (cfunU initF));
     ("get", (cfunU getF));
     ("set", (cfunU setF))].

  Definition SMapSem: SModSem.t := {|
    SModSem.fnsems := MapSbtb;
    SModSem.mn := "Map";
    SModSem.initial_mr := GRA.embed ((Excl.unit, Auth.excl ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra) ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra)): MapRA1) ⋅ (ε ⋅ ε);

    SModSem.initial_st := (fun (_: Z) => 0%Z)↑;
  |}
  .

  Definition SMap: SMod.t := {|
    SMod.get_modsem := fun _ => SMapSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition Map: Mod.t := (SMod.to_tgt (fun _ => CondsB) SMap).
End A.
