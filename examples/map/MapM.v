Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB IPM.
Require Import Mem1.
Require Import MapHeader.

Set Implicit Arguments.


(*** module M Map
private map := (fun k => 0)
private size := 0

def init(sz: int) ≡
  size := sz

def get(k: int): int ≡
  assume(0 ≤ k < size)
  return map[k]

def set(k: int, v: int) ≡
  assume(0 ≤ k < size)
  map := map[k ← v]
***)

Section M.
  Context `{@GRA.inG MapRA1 Σ}.
  Context `{@GRA.inG memRA Σ}.

  Let Es := Es'.

  Definition initF: list val -> itree Es val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      `data: option ((Z -> Z) * Z) <- pget;;
      guarantee(data = None);;;
      _ <- pput (Some ((fun (_: Z) => 0%Z), sz));;
      Ret Vundef
  .

  Definition getF: list val -> itree Es val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      `data: option ((Z -> Z) * Z) <- pget;;
      data <- data ?;;
      let (f, sz) := data in
      _ <- assume(0 <= k < sz)%Z;;
      Ret (Vint (f k))
  .

  Definition setF: list val -> itree Es val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      `data: option ((Z -> Z) * Z) <- pget;;
      data <- data ?;;
      let (f, sz) := data in
      assume(0 <= k < sz)%Z;;;
      _ <- pput (Some (fun n => if Z.eq_dec n k then v else f n, sz));;
      Ret Vundef
  .

  Definition MapSbtbM: list (string * _) :=
    [("init", (cfunU initF));
     ("get", (cfunU getF));
     ("set", (cfunU setF))]
  .

  Definition SMapSem: SModSem.t := {|
    SModSem.fnsems := MapSbtbM;
    SModSem.mn := "Map";
    SModSem.initial_mr := ε ⋅ ε;
    SModSem.initial_st := (None: option ((Z -> Z) * Z))↑;
  |}
  .

  Definition SMap: SMod.t := {|
    SMod.get_modsem := fun _ => SMapSem;
    SMod.sk := Sk.unit;
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Map: Mod.t := (SMod.to_tgt (fun _ => Conds) SMap).
End M.
