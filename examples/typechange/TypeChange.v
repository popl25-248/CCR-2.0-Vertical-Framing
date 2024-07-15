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
Require Import HoareFacts SimModSem HTactics2.
Require Import ProofMode HSim2 ISim2 IProofMode2 Sealed.
From compcert Require Import Integers.

Set Implicit Arguments.


(* Definition lessbits (a b: Z): Prop := ∀ n, Z.testbit a n -> Z.testbit b n. *)
Definition lessbits (a b: Z): Prop := Z.ldiff a b = 0.

(* Lemma ldiff_spec a b n : *)
(*  testbit (ldiff a b) n = testbit a n && negb (testbit b n). *)
(* Lemma lessbits_alt: ∀ a b, lessbits a b = *)

Lemma lessbits_less: ∀ a b (NONNEG: (0 <= b)%Z), lessbits a b -> (a <= b)%Z.
Proof.
  i. unfold lessbits in *.
  eapply Z.ldiff_le; et.
Qed.

Lemma Zlor_max
  (a b c: Z)
  (T: lessbits a c)
  (U: lessbits b c)
  (NONNEG: (0 <= c)%Z)
  :
  (Z.lor a b <= c)%Z
.
Proof.
  eapply lessbits_less; ss.
  unfold lessbits in *.
  rewrite Z.ldiff_land in *.
  rewrite Z.land_lor_distr_l. rewrite T. rewrite U.
  ss.
Qed.

Lemma lbits_zero
        n l
        (T: (0 <= n <= l)%Z)
        (* (SHIFT: exists m, l = Z.shiftl 1 m) *)
        m
        (NONNEG: (0 < m)%Z)
        (SHIFT: l = Z.ones m)
  :
  lessbits n l
.
Proof.
  des; subst. unfold lessbits.
  rewrite Z.ldiff_ones_r; ss; try lia.
  assert(n ≫ m = 0).
  {
    unfold Z.ones in *. ss.
    unfold Z.pred in *.
    eapply Z.shiftr_eq_0; ss.
    eapply Z.le_lt_trans.
    { eapply Z.log2_le_mono; et. }
    clears n. clear_tac.
    eapply Z.log2_lt_pow2; ss.
    { rewrite Z.shiftl_1_l.
      cut ((2 <= 2 ^ m)%Z).
      { i. lia.
      }
      assert((∃ n, m = n + 1 ∧ 0 <= n)%Z).
      { exists (Z.pred m). lia. }
      des; subst.
      rewrite Z.pow_add_r; ss.
      lia.
    }
    rewrite Z.shiftl_mul_pow2; ss; try lia.
  }
  rewrite H.
  rewrite Z.shiftl_0_l; et.
Qed.

Lemma max_unsigned_zeros: Int.max_unsigned = Z.ones Int.zwordsize.
Proof.
  unfold Int.max_unsigned. ss.
Qed.



Section DEF.

  Context `{Σ: GRA.t}.
  Local Existing Instance HasFreezeN.

  Definition setT: Any.t -> itree Es' Any.t :=
    fun arg =>
      `x: Int.int <- arg↓?;;
      s <- trigger PGet;;
      `s: Int.int <- s↓?;;
      trigger (PPut (Int.or s (Int.shl Int.one x))↑);;;
      Ret tt↑
  .

  Definition getT: Any.t -> itree Es' Any.t :=
    fun arg =>
      `x: Int.int <- arg↓?;;
      s <- trigger PGet;;
      `s: Int.int <- s↓?;;
      (* let res := Int.eq x (Int.and s (Int.shl Int.one x)) in *)
      let res := Int.testbit s (Int.unsigned x) in
      Ret res↑
  .

  Definition setM: Any.t -> itree Es' Any.t :=
    fun n =>
      `n: Z <- n↓?;;
      s <- trigger PGet;;
      `s: Z <- s↓?;;
      trigger (PPut (Z.setbit s n)↑);;;
      Ret tt↑
  .

  Definition getM: Any.t -> itree Es' Any.t :=
    fun n =>
      `n: Z <- n↓?;;
      s <- trigger PGet;;
      `s: Z <- s↓?;;
      let res := Z.testbit s n in
      Ret res↑
  .

  Variant my_flags :=
  | flag0
  | flag1
  | flag2
  .

  Program Instance my_flags_Dec: Dec my_flags.
  Next Obligation.
    decide equality.
  Qed.

  Definition to_Z (mf: my_flags): Z :=
    match mf with
    | flag0 => 0
    | flag1 => 1
    | flag2 => 2
    end
  .

  Definition setS: Any.t -> itree Es' Any.t :=
    fun n =>
      `n: my_flags <- n↓?;;
      s <- trigger PGet;;
      `s: (my_flags -> bool) <- s↓?;;
      trigger (PPut (λ x, if dec x n then true else s x)↑);;;
      Ret tt↑
  .

  Definition getS: Any.t -> itree Es' Any.t :=
    fun n =>
      `n: my_flags <- n↓?;;
      s <- trigger PGet;;
      `s: (my_flags -> bool) <- s↓?;;
      Ret (s n)↑
  .

  Definition modsem_tgt: SModSem.t := {|
    SModSem.fnsems := [("set", setT); ("get", getT)];
    SModSem.mn := "";
    SModSem.initial_mr := ε;
    SModSem.initial_st := Int.zero↑;
  |}
  .

  Definition module_tgt := {|
    SMod.get_modsem := fun _ => modsem_tgt;
    SMod.sk := Sk.unit;
  |}.

  Definition modsem_mid: SModSem.t := {|
    SModSem.fnsems := [("set", setM); ("get", getM)];
    SModSem.mn := "";
    SModSem.initial_mr := ε;
    SModSem.initial_st := (0: Z)↑;
  |}
  .

  Definition module_mid := {|
    SMod.get_modsem := fun _ => modsem_mid;
    SMod.sk := Sk.unit;
  |}.

  Definition modsem_src: SModSem.t := {|
    SModSem.fnsems := [("set", setS); ("get", getS)];
    SModSem.mn := "";
    SModSem.initial_mr := ε;
    SModSem.initial_st := (λ (_: my_flags), false)↑;
  |}
  .

  Definition module_src := {|
    SMod.get_modsem := fun _ => modsem_src;
    SMod.sk := Sk.unit;
  |}.





  Definition setspec_mid: fspec :=
    mk_fspec (λ (_: unit) m t, ⌜∃ i, m = (Int.unsigned i)↑ ∧ t = i↑ ∧ (0 <= (Int.unsigned i) < Int.zwordsize)%Z⌝%I)
      (λ _ m t, ⌜m = t ∧ m = tt↑⌝%I).

  Definition getspec_mid: fspec :=
    mk_fspec (λ (_: unit) m t, ⌜ ∃ i, m = (Int.unsigned i)↑ ∧ t = i↑ ∧ (0 <= (Int.unsigned i) < Int.zwordsize)%Z⌝%I)
      (λ _ m t, ⌜m = t⌝%I).

  Definition stb_mid := (λ fn, if dec "set" fn then setspec_mid else
                                 if dec "get" fn then getspec_mid else ε%fspec).

  Definition setspec_src: fspec :=
    mk_fspec (λ (_: unit) s m, ⌜∃ (f: my_flags), s = f↑ ∧ m = (to_Z f)↑⌝%I)
      (λ _ m t, ⌜m = t ∧ m = tt↑⌝%I).

  Definition getspec_src: fspec :=
    mk_fspec (λ (_: unit) s m, ⌜∃ (f: my_flags), s = f↑ ∧ m = (to_Z f)↑⌝%I)
      (λ _ m t, ⌜m = t⌝%I).

  Definition stb_src := (λ fn, if dec "set" fn then setspec_src else
                                 if dec "get" fn then getspec_src else ε%fspec).

  Definition tgt: Mod.t := SMod.to_tgt (λ _, ε%stb) module_tgt.
  Definition mid: Mod.t := SMod.to_tgt (λ _, stb_mid) module_mid.
  Definition src: Mod.t := SMod.to_tgt (λ _, (stb_mid |> stb_src)%stb) module_src.

  Let wf0 := mk_wf (λ (_: unit) st_mid st_tgt,
                (⌜∃ n, st_mid = n↑ ∧ (0 <= n <= Int.max_unsigned)%Z ∧ st_tgt = (Int.repr n)↑⌝)%I).

  Theorem ref0
    :
    refines tgt mid
  .
  Proof.
    unfold mid.
    eapply adequacy_local.
    econs; ss. i.
    econstructor 1 with (wf:=wf0) (le:=top2); ss.
    2: { esplits; ss. rr.
         replace (Any.pair (0%Z)↑ (Any.upcast (ε: Σ)), Any.pair Int.zero↑ (Any.upcast (ε: Σ))) with
           (Any.pair (0%Z)↑ (Any.upcast (ε ⋅ ε: Σ)), Any.pair Int.zero↑ (Any.upcast (ε: Σ))).
         2: { rewrite URA.unit_id. ss. }
         econs; et. eapply to_semantic. iIntros; ss. iPureIntro. esplits; et; try lia.
         eapply (Int.unsigned_range_2 Int.zero). }
    econs; ss.
    { do 5 r. esplits; ss. r. clear_tac. clears sk. clear_tac.
      eapply adequacy_isim; ss.
      iIntros. des. des_u. ss. clear_tac. subst.
      iModIntro. iIntros. iDes. iModIntro. iSplits; ss. des_ifs. ss. des; subst.
      unfold setT, setM. rewrite Any.upcast_downcast. ss. steps.
      iIntros. subst. iModIntro. iSplits; ss. iPureIntro. esplits; ss; try lia.
      3: { f_equal. unfold Int.or. f_equal.
           rewrite Int.unsigned_repr; ss.
           rewrite Z.setbit_spec'.
           unfold Int.shl. ss.
           rewrite Z.shiftl_mul_pow2; ss. rewrite Int.unsigned_one. rewrite Z.mul_1_l.
           f_equal. rewrite Int.unsigned_repr; ss. split; ss.
           { lia. }
           { exploit Int.two_p_range; et. intro T; des.
             rewrite two_p_correct in *. ss. }
      }
      { rewrite Z.setbit_spec'.
        eapply Z.lor_nonneg. esplits; ss. lia.
      }
      { rewrite Z.setbit_spec'.
        rewrite max_unsigned_zeros in *.
        eapply Zlor_max; ss.
        - eapply lbits_zero; et; ss.
        - eapply lbits_zero; et; ss.
          split; try lia.
          assert(U: (Int.unsigned i <= (Int.zwordsize - 1))%Z).
          { lia. }
          clear H4.
          unfold Z.ones. etrans.
          { eapply Z.pow_le_mono_r; et. ss. }
          rewrite Z.shiftl_mul_pow2; ss.
      }
    }
    econs; ss.
    { do 5 r. esplits; ss. r. clear_tac. clears sk. clear_tac.
      eapply adequacy_isim; ss.
      iIntros. des. des_u. ss. clear_tac. subst.
      iModIntro. iIntros. iDes. iModIntro. iSplits; ss. des_ifs. ss. des; subst.
      unfold getT, getM. rewrite ! Any.upcast_downcast. ss. steps.
      iIntros. subst. iModIntro. iSplits; ss. iPureIntro. esplits; ss; try lia.
      iPureIntro. f_equal. rewrite Int.testbit_repr; ss.
    }
  Unshelve.
    all: ss.
  Qed.

  Let wf1 := mk_wf (λ (_: unit) st_src st_mid,
                (⌜∃ f n, st_src = f↑ ∧ st_mid = n↑ ∧ ∀ mf, f mf = Z.testbit n (to_Z mf)⌝)%I).

  Theorem ref1
    :
    gccr stb_src module_mid module_src
  .
  Proof.
    red; i.
    etrans.
    { eapply stb_equiv_Proper; ss. instantiate (1:= λ _, (fr |> ε)%stb); ss.
      red; i. eapply stb_append_unit_r. }
    eapply adequacy_local.
    econs; ss. i.
    econstructor 1 with (wf:=wf1) (le:=top2); ss.
    2: { esplits; ss. rr.
         replace (Any.pair (λ _ : my_flags, false)↑ (Any.upcast (ε: Σ)), Any.pair (0%Z)↑ (Any.upcast (ε: Σ))) with
           (Any.pair (λ _ : my_flags, false)↑ (Any.upcast (ε ⋅ ε: Σ)), Any.pair (0%Z)↑ (Any.upcast (ε: Σ))).
         2: { rewrite URA.unit_id. ss. }
         econs; et. eapply to_semantic. iIntros; ss. iPureIntro. esplits; et; try lia.
         i. ss. rewrite Z.testbit_0_l in *; ss.
    }
    econs; ss.
    { do 5 r. esplits; ss. r. clear_tac. clears sk. clear_tac.
      eapply adequacy_isim; ss.
      revert fr.
      eapply isim_vframe; ss.
      iIntros. des. des_u. ss. clear_tac. subst.
      iModIntro. iIntros. iDes. iModIntro. iSplits; ss. des_ifs. ss. des; subst.
      unfold setM, setS. rewrite Any.upcast_downcast. ss. steps.
      iIntros. subst. iModIntro. iSplits; ss. iPureIntro. esplits; ss; try lia.
      i. rewrite Z.setbit_eqb; ss.
      2: { destruct f0; ss. }
      - des_ifs; ss.
        + rewrite Z.eqb_refl. ss.
        + assert((to_Z f0 =? to_Z mf)%Z = false).
          { destruct f0, mf; ss. }
          rewrite H. ss.
    }
    econs; ss.
    { do 5 r. esplits; ss. r. clear_tac. clears sk. clear_tac.
      eapply adequacy_isim; ss.
      revert fr.
      eapply isim_vframe; ss.
      iIntros. des. des_u. ss. clear_tac. subst.
      iModIntro. iIntros. iDes. iModIntro. iSplits; ss. des_ifs. ss. des; subst.
      unfold getM, getS. rewrite Any.upcast_downcast. ss. steps.
      iIntros. subst. iModIntro. iSplits; ss. iPureIntro. esplits; ss; try lia.
      iPureIntro. f_equal. eapply H2.
    }
  Unshelve.
    all: ss.
  Qed.

End DEF.
