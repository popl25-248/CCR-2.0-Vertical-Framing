Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HTactics HSim.
Require Export ISim.
From iris.bi Require Import bi telescopes.
From iris.proofmode Require Import base environments coq_tactics.



Ltac ired_l := try Red.prw ltac:(IRed._red_gen) 1 2 1 0.
Ltac ired_r := try Red.prw ltac:(IRed._red_gen) 1 1 1 0.
Ltac ired_both := ired_l; ired_r.
Ltac prep := cbn; ired_both.

Ltac force_l :=
  prep;
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
      (* let tvar := fresh "tmp" in *)
      (* let thyp := fresh "TMP" in *)
      (* remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar; *)
      (* let name := fresh "G" in *)
      (* destruct (ox) eqn:name; [|exfalso]; cycle 1 *)
      idtac
      (* let name := fresh "y" in *)
      (* iApply isim_unwrapN_src; iIntros (name) "%"; *)
      (* match goal with *)
      (* | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in * *)
      (* end *)
  end
.

Ltac force_r :=
  prep;
  (* match goal with *)
  (* | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] => *)
  (*   let tvar := fresh "tmp" in *)
  (*   let thyp := fresh "TMP" in *)
  (*   remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar; *)
  (*   let name := fresh "_UNWRAPU" in *)
  (*   destruct (ox) eqn:name; [|exfalso]; cycle 1 *)
  (* | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] => *)
  (*   let tvar := fresh "tmp" in *)
  (*   let thyp := fresh "TMP" in *)
  (*   remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar; *)
  (*   let name := fresh "_ASSUME" in *)
  (*   destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_tgt; [exists name]|contradict name]; cycle 1 *)

  (* | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] => *)
  (*   seal i_src; apply sim_itreeC_spec; econs; unseal i_src *)
  (* end *)
  match goal with
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
      (* let name := fresh "y" in *)
      (* iApply isim_unwrapN_tgt; iIntros (name) "%"; *)
      (* match goal with *)
      (* | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in * *)
      (* end *)
      idtac
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
      let name := fresh "G" in
      cut (P); [intros name; iApply isim_assume_tgt; iSplitR; [iPureIntro; exact name|]|]; cycle 1
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, trigger (PPut _) >>= _)) ] =>
      iApply isim_pput_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, trigger (PGet) >>= _)) ] =>
      iApply isim_pget_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_choose_tgt; iIntros (name)
  end
.

Ltac step0 :=
  match goal with
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
      iApply isim_assume_src; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, trigger (PPut _) >>= _) (_, _)) ] =>
      iApply isim_pput_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, trigger (PGet) >>= _) (_, _)) ] =>
      iApply isim_pget_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, trigger (Take _) >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_take_src; iIntros (name)

  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
      iApply isim_guarantee_tgt; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, trigger (PPut _) >>= _)) ] =>
      iApply isim_pput_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, trigger (PGet) >>= _)) ] =>
      iApply isim_pget_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_choose_tgt; iIntros (name)

  (** impure call **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _)
                                           (_, trigger (Call ?x1 ?y1) >>= _)) ] =>
      match goal with
      | [ STBINCL: stb_incl _ _ |- _ ] =>
          iApply isim_call_impure; [eapply fn_has_spec_in_stb; [eapply STBINCL; stb_tac; ss|ss|ss]|]
      end

  (** ret **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  end.

Ltac steps :=
  repeat (prep; try step0; simpl(* ; des_ifs_safe *)).
