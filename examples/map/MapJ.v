
Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import HoareDef PCM.
Require Import Mem1 MapHeader.

Set Implicit Arguments.


(*** module I Map
private data := NULL

def init(sz: int) ≡
  data := calloc(sz)

def get(k: int): int ≡
  return *(data + k)

def set(k: int, v: int) ≡
  *(data + k) := v

def set_by_user(k: int) ≡
  set(k, input())
***)

Section I.
  Local Open Scope string_scope.
  Context `{@GRA.inG memRA Σ}.

  Definition initF: list val -> itree Es' val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      r <- ( (specbody calloc_spec)) [Vint sz]↑;;
      `r: val <- r↓?;;
      pput r;;;
      Ret Vundef
  .

  Definition getF: list val -> itree Es' val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; vptr <- (vadd data (Vint (k * 8)))?;;
      r <- ( (specbody load_spec)) [vptr]↑;;
      `r: val <- r↓?;;
      r <- (unint r)?;;
      Ret (Vint r)
  .

  Definition setF: list val -> itree Es' val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      data <- trigger PGet;; data <- data↓?;; vptr <- (vadd data (Vint (k * 8)))?;;
      r <- ( (specbody store_spec)) [vptr; Vint v]↑;;
      `r: val <- r↓?;;
      Ret Vundef
  .

  Definition MapSem: SModSem.t := {|
    SModSem.fnsems := [("init", cfunU initF); ("get", cfunU getF); ("set", cfunU setF)];
    SModSem.mn := "Map";
    SModSem.initial_mr := ε;
    SModSem.initial_st := (Vnullptr)↑;
  |}
  .

  Definition Map: SMod.t := {|
    SMod.get_modsem := fun _ => MapSem;
    SMod.sk := Sk.unit;
  |}
  .
End I.
