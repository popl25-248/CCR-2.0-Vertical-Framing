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
Require Import HTactics2.

Set Implicit Arguments.

Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.


Require Import Sealed.

Goal ∀ `{Σ: GRA.t} x P X, current_iProp x (sealed_upd X P ** X) -> current_iProp x (P ** X).
Proof.
  i. eapply current_iProp_upd. eapply current_iProp_entail; et.
  iIntros; iDes. iDestruct (sealed_upd_unseal with "[H1] [H]") as ">[A B]"; eauto; iFrame. ss.
Qed.

Section FSP.

  Context `{Σ: GRA.t}.
  (*** TODO: change the version in IPM.v ***)
  Lemma from_semantic (a: Σ) (P: iProp') (SAT: P a)
    :
      Own a ⊢ P.
  Proof.
    uipropall. ss. i. unfold URA.extends in *. des. subst.
    eapply iProp_mono; et. exists ctx; r_solve.
  Qed.

  Lemma unit_own_true: (Own ε) ≡ True%I.
  Proof.
    rr. econs. split; i; rr; uipropall; ss. exists x; r_solve.
  Qed.

  Lemma current_iProp_updatable (res0 res1: Σ) P
        (WF: URA.wf res1)
        (UPD: URA.updatable res1 res0)
        (CUR: current_iProp res0 P)
    :
      current_iProp res1 P.
  Proof.
    inv CUR. econs; try eassumption. etrans; et.
  Qed.

  Lemma current_iProp_frame_own res0 res1 P
        (WF: URA.wf ((res0 ⋅ res1): Σ))
        (CUR: current_iProp (res0) (Own res1 -* P))
    :
      current_iProp (res0 ⋅ res1) P.
  Proof.
    inv CUR. uipropall. hexploit IPROP.
    2:{ refl. }
    { eapply URA.updatable_wf; try apply WF; et. eapply URA.updatable_add; et. refl. }
    i. econs; eauto. eapply URA.updatable_add; et. refl.
  Qed.

  Lemma current_iProp_frame_own_rev res0 res1 P
        (CUR: current_iProp res0 (Own res1 ** P))
    :
      exists res2, URA.wf res0 /\ URA.updatable res0 (res2 ⋅ res1) ∧ current_iProp res2 P.
  Proof.
    inv CUR. uipropall.
    unfold URA.extends in *. des; clarify.
    exists (ctx ⋅ b). esplits; et.
    { etrans; et. replace (ctx ⋅ b ⋅ res1) with (res1 ⋅ ctx ⋅ b) by r_solve; ss. }
    econs; eauto.
    { eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists res1. r_solve. }
    { eapply URA.extends_updatable. exists ctx. r_solve. }
  Qed.

  (* Lemma current_iProp_own_wf ctx res *)
  (*       (CUR: current_iProp ctx (Own res)) *)
  (*   : *)
  (*     URA.wf (ctx ⋅ res). *)
  (* Proof. *)
  (*   inv CUR. uipropall. unfold URA.extends in *. des. clarify. *)
  (*   eapply URA.wf_mon. *)
  (*   instantiate (1:=ctx0). r_wf GWF. *)
  (* Qed. *)

End FSP.



(*** `hsim` is an intermediate step towards `isim`, which is defined in iProp like weakest precondition (wp).
Both `hsim` and `isim` take the postcondition (Q) as an argument like the weakest precondition (wp). ***)

Section SIM.
  Context `{Σ: GRA.t}.
  Variable world: Type.
  Variable le: relation world.
  Variable I: world -> Any.t -> Any.t -> iProp.

  Definition inv_with w0 st_src st_tgt: iProp :=
    (∃ w1, I w1 st_src st_tgt ** ⌜le w0 w1⌝)%I.

  Lemma inv_with_current `{PreOrder _ le} w0 st_src st_tgt
    :
      bi_entails (I w0 st_src st_tgt) (inv_with w0 st_src st_tgt).
  Proof.
    unfold inv_with. iIntros "H". iExists w0. iSplit; auto.
  Qed.

  Lemma inv_with_le `{PreOrder _ le} w0 w1 st_src st_tgt
        (LE: le w0 w1)
    :
      bi_entails (inv_with w1 st_src st_tgt) (inv_with w0 st_src st_tgt).
  Proof.
    unfold inv_with. iIntros "H". iDestruct "H" as (w2) "[H0 %]".
    iExists w2. iSplit; auto. iPureIntro. etrans; eauto.
  Qed.

  Class HasFreeze := has_freeze: bool.
  Instance HasFreezeY: HasFreeze := true.
  Instance HasFreezeN: HasFreeze := false.


  Context `{HF: HasFreeze}.
  Inductive _hsim
            (hsim: forall R_src R_tgt
                          (stb_src stb_tgt: gname -> fspec)
                          (OwnT: Σ)
                          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                          (fmr: Σ),
                bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
            {R_src R_tgt}
            (stb_src stb_tgt: gname -> fspec)
            (OwnT: Σ)
            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
            (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hsim_ret
      v_src v_tgt
      st_src st_tgt
      f_src f_tgt
      (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  (* | hsim_call *)
  (*     fsp_src fsp_tgt w0 *)
  (*     fn arg_src arg_tgt *)
  (*     st_src0 st_tgt0 ktr_src ktr_tgt *)
  (*     f_src f_tgt *)
  (*     (SPEC: stb_src fn = fsp_src) *)
  (*     (SPEC: stb_tgt fn = fsp_tgt) *)
  (*     (PRE: forall (x_tgt: fsp_tgt.(meta)), ∃ x_src FR, *)
  (*         (<<PRE: current_iProp fmr (Own OwnT ** (∀ argp, (fsp_tgt.(precond) x_tgt arg_tgt argp) ==∗ *)
  (*                                              (FR ** inv_with w0 st_src0 st_tgt0 ** *)
  (*                                                  fsp_src.(precond) x_src arg_src argp)))>>) *)
  (*         /\ *)
  (*         (<<POST: forall st_src1 st_tgt1 ret_src, *)
  (*               (<<UPD: ∀ retp, (FR ** inv_with w0 st_src1 st_tgt1 ** *)
  (*                                       fsp_src.(postcond) x_src ret_src retp) *)
  (*                        ==∗ ∃ ret_tgt J, (fsp_tgt.(postcond) x_tgt ret_tgt retp ** J ** *)
  (*      ⌜(<<SIM: forall fmr1 OwnT (TGT: fsp_tgt.(postcond) x_tgt ret_tgt retp OwnT) (ACC: current_iProp fmr1 (Own OwnT ** J)), *)
  (*           hsim _ _ OwnT Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)⌝)>>) *)
  (*                 >>) *)
  (*     ) *)
  (*   : *)
  (*     _hsim hsim OwnT Q fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src) *)
  (*           (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt) *)
  | hsim_call
      fsp_src fsp_tgt w0
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      f_src f_tgt
      (SPEC: stb_src fn = fsp_src)
      (SPEC: stb_tgt fn = fsp_tgt)
      (PRE: current_iProp fmr (Own OwnT **
        (∀ x_tgt argp, (fsp_tgt.(precond) x_tgt arg_tgt argp) ==∗
            ∃ x_src FR, (FR ** inv_with w0 st_src0 st_tgt0 **
                         fsp_src.(precond) x_src arg_src argp **
                         (∀ st_src1 st_tgt1 ret_src retp,
                            (FR ** inv_with w0 st_src1 st_tgt1 **
                             fsp_src.(postcond) x_src ret_src retp)
                             ==∗ ∃ ret_tgt J, (fsp_tgt.(postcond) x_tgt ret_tgt retp ** J **
       ⌜(<<SIM: forall fmr1 OwnT
                       (TGT: if has_freeze then fsp_tgt.(postcond) x_tgt ret_tgt retp OwnT else True)
                       (ACC: current_iProp fmr1 (Own OwnT ** J)),
            hsim _ _ stb_src stb_tgt OwnT Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)⌝))))
              )
      )
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src)
            (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsim_assert_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
          _hsim hsim stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_assume_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
          _hsim hsim stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt)
  (** Note: It may seem that "forall fmr1" in "SIM" is not needed in tgt cases.
   But these are indeed needed to justify frameC. **)
  | hsim_assert_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
          _hsim hsim stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassert COND) >>= ktr_tgt)
  | hsim_assume_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
          _hsim hsim stb_src stb_tgt OwnT Q fmr1 f_src true  (st_src, itr_src) (st_tgt, ktr_tgt tt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassume COND) >>= ktr_tgt)
  | hsim_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      f_src f_tgt
      (POST: forall ret,
          hsim _ _ stb_src stb_tgt OwnT Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsim_tau_src
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsim_tau_tgt
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsim_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: exists x, _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: forall x, _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsim_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: forall x, _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: exists x, _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsim_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      f_src f_tgt
      (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsim_pget_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsim_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsim_progress
      st_src st_tgt itr_src itr_tgt
      (SIM: hsim _ _ stb_src stb_tgt OwnT Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      _hsim hsim stb_src stb_tgt OwnT Q fmr true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Lemma _hsim_ind2
        (hsim: forall R_src R_tgt
                      (stb_src stb_tgt: gname -> fspec)
                      (OwnT: Σ)
                      (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                      (fmr: Σ),
            bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
        R_src R_tgt
        (P: (gname -> fspec) -> (gname -> fspec) -> Σ -> (Any.t -> Any.t -> R_src -> R_tgt -> iProp) -> Σ -> bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
        (RET: forall
            stb_src stb_tgt
            OwnT Q fmr
            v_src v_tgt
            st_src st_tgt
            f_src f_tgt
            (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            stb_src stb_tgt
            OwnT Q fmr
            fsp_src fsp_tgt w0
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            f_src f_tgt
            (SPEC: stb_src fn = fsp_src)
            (SPEC: stb_tgt fn = fsp_tgt)
            (PRE: current_iProp fmr (Own OwnT **
        (∀ x_tgt argp, (fsp_tgt.(precond) x_tgt arg_tgt argp) ==∗
            ∃ x_src FR, (FR ** inv_with w0 st_src0 st_tgt0 **
                         fsp_src.(precond) x_src arg_src argp **
                         (∀ st_src1 st_tgt1 ret_src retp,
                            (FR ** inv_with w0 st_src1 st_tgt1 **
                             fsp_src.(postcond) x_src ret_src retp)
                             ==∗ ∃ ret_tgt J, (fsp_tgt.(postcond) x_tgt ret_tgt retp ** J **
       ⌜(<<SIM: forall fmr1 OwnT
                       (TGT: if has_freeze then fsp_tgt.(postcond) x_tgt ret_tgt retp OwnT else True)
                       (ACC: current_iProp fmr1 (Own OwnT ** J)),
            hsim _ _ stb_src stb_tgt OwnT Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)⌝))))
              )
      ),
      P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src)
            (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (ASRTSRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
                <<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>>
            )
          ,
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt))
        (ASMESRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
                <<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>>
            ),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt))
        (ASRTTGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
                <<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>>
            ),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassert COND) >>= ktr_tgt))
        (ASMETGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
                <<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>>
            ),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassume COND) >>= ktr_tgt))
        (SYSCALL: forall
            stb_src stb_tgt
            OwnT Q fmr
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            f_src f_tgt
            (POST: forall ret,
                hsim _ _ stb_src stb_tgt OwnT Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            (stb_src stb_tgt: gname -> fspec)
            OwnT Q fmr
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            f_src f_tgt
            (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: _hsim hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src itr_tgt
            (SIM: hsim _ _ stb_src stb_tgt OwnT Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt
             (SIM: @_hsim hsim _ _ stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt),
        P stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt.
  Proof.
    fix IH 10. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply ASRTSRC; eauto. i. split; eauto. }
    { eapply ASMESRC; eauto. i. split; eauto. }
    { eapply ASRTTGT; eauto. i. split; eauto. }
    { eapply ASMETGT; eauto. i. split; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { des. eapply CHOOSESRC; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKESRC; eauto. }
    { des. eapply TAKETGT; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Definition hsim := paco11 _hsim bot11.
  Arguments hsim [_ _] _ _ _ _ _ _ _ _.

  Lemma _hsim_mon: monotone11 _hsim.
  Proof.
    ii. induction IN using _hsim_ind2.
    { econs 1; eauto. }
    { subst. econs 2; try refl.
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H"; [done|].
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. eauto.
    }
    { econs 3; i; eauto. eapply SIM; et. }
    { econs 4; i; eauto. eapply SIM; et. }
    { econs 5; i; eauto. eapply SIM; et. }
    { econs 6; i; eauto. eapply SIM; et. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 12; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 13; eauto. des. esplits; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
    { econs 18; eauto. }
  Qed.
  Hint Resolve _hsim_mon: paco.

  Lemma hsim_ind
        R_src R_tgt
        (P: _ -> _ -> _ -> _ -> _ -> bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
        (RET: forall
            stb_src stb_tgt
            Q OwnT fmr
            v_src v_tgt
            st_src st_tgt
            f_src f_tgt
            (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt)))
        (CALL: forall
            stb_src stb_tgt
            Q OwnT fmr
            fsp_src fsp_tgt w0
            fn arg_src arg_tgt
            st_src0 st_tgt0 ktr_src ktr_tgt
            f_src f_tgt
            (SPEC: stb_src fn = fsp_src)
            (SPEC: stb_tgt fn = fsp_tgt)
            (PRE: current_iProp fmr (Own OwnT **
        (∀ x_tgt argp, (fsp_tgt.(precond) x_tgt arg_tgt argp) ==∗
            ∃ x_src FR, (FR ** inv_with w0 st_src0 st_tgt0 **
                         fsp_src.(precond) x_src arg_src argp **
                         (∀ st_src1 st_tgt1 ret_src retp,
                            (FR ** inv_with w0 st_src1 st_tgt1 **
                             fsp_src.(postcond) x_src ret_src retp)
                             ==∗ ∃ ret_tgt J, (fsp_tgt.(postcond) x_tgt ret_tgt retp ** J **
       ⌜(<<SIM: forall fmr1 OwnT
                       (TGT: if has_freeze then fsp_tgt.(postcond) x_tgt ret_tgt retp OwnT else True)
                       (ACC: current_iProp fmr1 (Own OwnT ** J)),
            hsim stb_src stb_tgt OwnT Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)⌝))))
              )
      ),
      P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src)
            (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt))
        (ASRTSRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
                <<SIM: hsim stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>>
            )
          ,
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt))
        (ASMESRC: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
                <<SIM: hsim stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt)>>
            ),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt))
        (ASRTTGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
                <<SIM: hsim stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>>
            ),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassert COND) >>= ktr_tgt))
        (ASMETGT: forall
            stb_src stb_tgt
            OwnT Q fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt COND
            IPROPS
            (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
            (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
                <<SIM: hsim stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>> ∧
                         <<IH: P stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt)>>
            ),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassume COND) >>= ktr_tgt))
        (SYSCALL: forall
            stb_src stb_tgt
            Q OwnT fmr
            fn arg rvs
            st_src st_tgt ktr_src ktr_tgt
            f_src f_tgt
            (POST: forall ret,
                hsim stb_src stb_tgt OwnT Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt))
        (TAUSRC: forall
            stb_src stb_tgt
            Q OwnT fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
          ,
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt))
        (TAUTGT: forall
            stb_src stb_tgt
            Q OwnT fmr
            st_src st_tgt itr_src itr_tgt
            f_src f_tgt
            (SIM: hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt))
        (CHOOSESRC: forall
            stb_src stb_tgt
            Q OwnT fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt))
        (CHOOSETGT: forall
            stb_src stb_tgt
            Q OwnT fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt))
        (TAKESRC: forall
            stb_src stb_tgt
            Q OwnT fmr
            X
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: forall x, (<<SIM: hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt))
        (TAKETGT: forall
            stb_src stb_tgt
            Q OwnT fmr
            X
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: exists x, (<<SIM: hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>) /\ (<<IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x)>>)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt))
        (PPUTSRC: forall
            stb_src stb_tgt
            Q OwnT fmr
            st_src1
            st_src0 st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt))
        (PPUTTGT: forall
            stb_src stb_tgt
            Q OwnT fmr
            st_tgt1
            st_src st_tgt0 itr_src ktr_tgt
            f_src f_tgt
            (SIM: hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
            (IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt))
        (PGETSRC: forall
            stb_src stb_tgt
            Q OwnT fmr
            st_src st_tgt ktr_src itr_tgt
            f_src f_tgt
            (SIM: hsim stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt))
        (PGETTGT: forall
            stb_src stb_tgt
            Q OwnT fmr
            st_src st_tgt itr_src ktr_tgt
            f_src f_tgt
            (SIM: hsim stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
            (IH: P stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt)),
            P stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt))
        (PROGRESS: forall
            stb_src stb_tgt
            Q OwnT fmr
            st_src st_tgt itr_src itr_tgt
            (SIM: hsim stb_src stb_tgt OwnT Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt)),
            P stb_src stb_tgt OwnT Q fmr true true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      forall stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt
             (SIM: hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt),
        P stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _hsim_ind2.
    { eapply RET; eauto. }
    { eapply CALL.
      { eauto. }
      { eauto. }
      eapply current_iProp_entail; try apply PRE.
      iIntros. iDes. iSplitL "H".
      { eauto. }
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iModIntro.
      iDes. iSplits; et. iSplitR "H11".
      { iFrame. iAssumption. }
      iIntros. iDes. iSpecialize ("H11" with "[H H2 H1]").
      { iFrame. }
      iMod "H11". iModIntro. iDes. iSplits; ss.
      { iFrame. iAssumption. }
      iPureIntro. i. specialize (H _ _ TGT ACC). pclearbot. eauto.
    }
    { eapply ASRTSRC; eauto. i. specialize (SIM _ _ ACC); des. split; eauto. pfold. eauto. }
    { eapply ASMESRC; eauto. i. specialize (SIM _ _ ACC); des. split; eauto. pfold. eauto. }
    { eapply ASRTTGT; eauto. i. specialize (SIM _ _ ACC); des. split; eauto. pfold. eauto. }
    { eapply ASMETGT; eauto. i. specialize (SIM _ _ ACC); des. split; eauto. pfold. eauto. }
    { eapply SYSCALL; eauto. i. hexploit POST; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. pfold. eauto. }
    { eapply TAUTGT; eauto. pfold. eauto. }
    { des. eapply CHOOSESRC; eauto. esplits; eauto. pfold. eauto. }
    { eapply CHOOSETGT; eauto. i. hexploit SIM; eauto. i. des. pclearbot. splits; eauto. pfold. eauto. }
    { eapply TAKESRC; eauto. i. hexploit SIM; eauto. i. des. pclearbot. splits; eauto. pfold. eauto. }
    { des. eapply TAKETGT; eauto. esplits; eauto. pfold. eauto. }
    { eapply PPUTSRC; eauto. pfold. eauto. }
    { eapply PPUTTGT; eauto. pfold. eauto. }
    { eapply PGETSRC; eauto. pfold. eauto. }
    { eapply PGETTGT; eauto. pfold. eauto. }
    { eapply PROGRESS; eauto. pclearbot. eauto. }
  Qed.

  Local Transparent HoareFunRet HoareCall.
  Lemma hsim_adequacy_aux `{PreOrder _ le}:
    forall
      stb_src stb_tgt
      f_src f_tgt st_src st_tgt (itr_src: itree Es' Any.t) itr_tgt (mr_src mr_tgt: Σ) fr_src fr_tgt
      X_src (x_src: X_src) X_tgt (x_tgt: X_tgt) Q_src Q_tgt w0
      (SIM: hsim stb_src stb_tgt (fr_tgt ⋅ mr_tgt)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    (∀ retp, (Q_tgt x_tgt ret_tgt retp) ==∗
                     ((inv_with w0 st_src st_tgt) ** (Q_src x_src ret_src retp)))%I)
                 (fr_src ⋅ mr_src)
                 f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt)),
      paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 (@eq Any.t))
            f_src f_tgt w0
            (Any.pair st_src mr_src↑,
              ('(fr1, r) <- interp_condE_tgt (interp_Es'_tgt stb_src itr_src) fr_src;;
              '(_, r) <- interp_condE_tgt (HoareFunRet Q_src x_src r) fr1;;
              Ret r))
            (Any.pair st_tgt mr_tgt↑,
              ('(fr1, r) <- interp_condE_tgt (interp_Es'_tgt stb_tgt itr_tgt) fr_tgt;;
              '(_, r) <- interp_condE_tgt (HoareFunRet Q_tgt x_tgt r) fr1;;
              Ret r)).
  Proof.
    ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    revert st_src st_tgt itr_src itr_tgt Heqp Heqp0 CIH.
    remember (fr_src ⋅ mr_src) as tmp0.
    remember (λ st_src st_tgt ret_src ret_tgt : Any.t,
             (∀ retp : Any.t,
                Q_tgt x_tgt ret_tgt retp ==∗ inv_with w0 st_src st_tgt ** Q_src x_src ret_src retp)%I) as tmp1.
    remember (fr_tgt ⋅ mr_tgt) as tmp2.
    revert Heqtmp0 Heqtmp1 Heqtmp2.
    revert mr_src mr_tgt fr_src fr_tgt.
    induction SIM using hsim_ind; i; clarify.
    { eapply current_iPropL_convert in RET. mDesAll.
      unfold inv_with in RET. mDesAll.
      unfold HoareFunRet, ASSERT. steps.
      mAssert (_ ** _) with "H".
      { iDestruct "H" as "[A B]". iSplitL "A"; iAssumption. }
      mDesAll.
      eapply hassert_tgt_clo.
      { eapply current_iProp_entail; et.
        { iIntros "[A [B C]]". iFrame. iAssumption. }
      }
      clear RET. i. steps.
      eapply sim_itreeC_spec; econs; i.
      esplits. steps.
      eapply current_iPropL_convert in ACC. mDesAll.
      mAssert (#=> _) with "A2 H".
      { iSpecialize ("A2" with "H"). iAssumption. }
      mClear "A3". mUpd "A4". mDesAll.
      eapply hassert_src_clo_strong.
      { eapply current_iProp_entail; et.
        { iIntros "[A B]". iDes. iFrame. iClear "B111". iSplitL "B1"; iAssumption. }
      }
      i. steps. rr. esplits; ss; et. econs; et.
    }
    { steps. unfold HoareCall, ASSERT, ASSUME. steps.
      eapply hassert_tgt_clo.
      { eapply current_iProp_entail; et.
        { iIntros "[[A B] C]". iFrame. iAssumption. }
      }
      clear PRE. i. steps.
      eapply current_iPropL_convert in ACC. mDesAll.
      mAssert (#=> _) with "A2 H".
      { iSpecialize ("A2" with "H"). iAssumption. }
      mUpd "A3". mDesAll.
      eapply sim_itreeC_spec; econs; i. esplits. steps.
      eapply sim_itreeC_spec; econs; i. esplits. steps.
      eapply hassert_src_clo_strong.
      { eapply current_iProp_entail; et.
        iIntros "[A B]". iDes. iFrame. iClear "B11111".
        iSplitR "A".
        - xtra.
        - xtra.
      }
      clear ACC. i. steps.
      assert(T: ∃ w2, le w1 w2 ∧ (URA.wf mr_src1 -> I w2 st_src st_tgt mr_src1)).
      { clear - ACCMR. i. rr in ACCMR. uipropall. des. uipropall. des; subst. exists x.
        rr in ACCMR1. uipropall.
        i. esplits; et. i. eapply iProp_mono; et. exists b. r_solve.
      }
      clear ACCMR. des.
      eapply sim_itreeC_spec; econs; i.
      { econs; et. }
      clear T0.
      steps.
      inv WF0.
      eapply hassume_src_clo.
      { i.
        instantiate (1:=_ ** (I w3 mp_src mp_tgt ** Own mr_tgt0)).
        econs; try refl; et.
        clear - ACCFR RSRC H0.
        rr.
        repeat (autounfold with iprop; autorewrite with iprop).
        esplits; et.
        rr.
        repeat (autounfold with iprop; autorewrite with iprop).
        esplits; et.
        - eapply RSRC. eapply URA.wf_extends; try apply H0. exists (fr1 ⋅ mr_tgt0). r_solve.
        - rr. exists ε. r_solve.
      }
      clear ACCFR. i.

      eapply current_iPropL_convert in ACC. mDesAll.
      (* (*** postcond is achieved via fr0 ⋅ mr_src0 ***) *)
      (* assert(U: postcond (stb_tgt fn) x a1 vret (cr ⋅ fr_tgt1 ⋅ mr_tgt0)). *)
      mAssert (#=> _) with "A3 H A1 A".
      { iSpecialize ("A3" with "[H A A1]").
        - iFrame. unfold inv_with. iSplits; et. iPureIntro. etrans; et.
        - eauto.
      }
      mUpd "A5". mDesAll.

      steps.
      eapply sim_itreeC_spec; econs; i. esplits. steps.
      eapply hassume_tgt_clo_strong.
      { eapply current_iProp_entail; et.
        iIntros "[A B]"; iDes. iFrame.
        { iClear "B111". iAssumption. }
      }
      clear ACC. i. steps.
      gbase. eapply CIH.
      eapply current_iProp_entail in ACC; cycle 1.
      { iIntros. iDes; iFrame. instantiate (1:=_ ** _). iSplitR "H"; [|iAccu]. xtra. }
      eapply PURE; ss.
      { des_ifs. eapply iProp_mono; et.
        { eapply current_iProp_frame_own_rev in ACC. des.
          eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable.
          exists res2; r_solve. }
        exists (fr_tgt1 ⋅ mr_tgt0); r_solve.
      }
      eapply current_iProp_entail; et.
      { iIntros; iDes. iFrame. iDestruct "H" as "[A [B C]]". iSplitR "C"; iFrame.
        iSplitL "B"; iFrame.
      }
    }
    { steps. eapply hassert_src_clo; et.
      { eapply current_iProp_entail; et.
        iIntros; iDes. iFrame. iDestruct "H" as "[A B]". iFrame. iAccu. }
      i. steps.
      exploit SIM; eauto.
      { eapply current_iProp_entail; et.
        iIntros; iDes. iSplitR "H2"; [|ss]. { iCombineAll. iAccu. } }
      i; des. eapply IH; eauto.
    }
    { steps. eapply hassume_src_clo; et.
      i. steps.
      exploit SIM; eauto.
      { eapply current_iProp_entail; et.
        iIntros; iDes. iFrame. }
      i; des. eapply IH; eauto.
    }
    { steps. eapply hassert_tgt_clo; et.
      { eapply current_iProp_entail; et.
        iIntros; iDes. iFrame. iDestruct "H" as "[A B]". iFrame. iAccu. }
      i. steps.
      eapply SIM; eauto.
      { eapply current_iProp_entail; et.
        iIntros; iDes. iFrame. iSplitL "H2"; ss. }
    }
    { steps. eapply hassume_tgt_clo; et.
      { eapply current_iProp_entail; et.
        iIntros; iDes. iFrame. iDestruct "H" as "[A B]". iFrame. iAccu. }
      i. steps.
      eapply SIM; eauto.
      { eapply current_iProp_entail; et.
        iIntros; iDes. iFrame. iSplitL "H2"; ss. }
    }
    { steps. gbase. hexploit CIH; eauto. }
    { steps. exploit IHSIM; eauto. }
    { steps. exploit IHSIM; eauto. }
    { des. exploit IH; eauto. i. steps. force_l. eexists. steps. eauto. }
    { steps. exploit SIM; eauto. i. des. eauto. }
    { steps. exploit SIM; eauto. i. des. eauto. }
    { des. exploit IH; eauto. i. force_r. eexists. steps. eauto. }
    { steps. exploit IHSIM; eauto. }
    { steps. exploit IHSIM; eauto. }
    { steps. exploit IHSIM; eauto. }
    { steps. exploit IHSIM; eauto. }
    { deflag. gbase. eapply CIH; eauto. }
  Unshelve. all: ss.
  Qed.

  Lemma hsim_adequacy `{PreOrder _ le}:
    forall
      stb_src stb_tgt
      f_src f_tgt st_src st_tgt (itr_src: itree Es' Any.t) itr_tgt
      mr_src mr_tgt fr_src fr_tgt X_src (x_src: X_src) X_tgt (x_tgt: X_tgt) Q_src Q_tgt w0
      (SIM: hsim stb_src stb_tgt (fr_tgt ⋅ mr_tgt)
                 (fun st_src st_tgt ret_src ret_tgt =>
                    (∀ retp, (Q_tgt x_tgt ret_tgt retp) ==∗
                     ((inv_with w0 st_src st_tgt) ** (Q_src x_src ret_src retp)))%I)
                 (fr_src ⋅ (mr_src ⋅ mr_tgt))
                 f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt)),
      paco8 (_sim_itree (mk_wf I) le) bot8 Any.t Any.t (lift_rel (mk_wf I) le w0 (@eq Any.t))
            f_src f_tgt w0
            (Any.pair st_src (mr_src ⋅ mr_tgt)↑,
              ('(fr1, r) <- interp_condE_tgt (interp_Es'_tgt stb_src itr_src) fr_src;;
              '(_, r) <- interp_condE_tgt (HoareFunRet Q_src x_src r) fr1;;
              Ret r))
            (Any.pair st_tgt mr_tgt↑,
              ('(fr1, r) <- interp_condE_tgt (interp_Es'_tgt stb_tgt itr_tgt) fr_tgt;;
              '(_, r) <- interp_condE_tgt (HoareFunRet Q_tgt x_tgt r) fr1;;
              Ret r)).
  Proof.
    i. hexploit hsim_adequacy_aux; eauto.
  Qed.

  Lemma hsim_progress_flag R_src R_tgt r g stb_src stb_tgt Q fmr st_src st_tgt OwnT
        (SIM: gpaco11 _hsim (cpn11 _hsim) g g R_src R_tgt stb_src stb_tgt OwnT Q fmr false false st_src st_tgt)
    :
      gpaco11 _hsim (cpn11 _hsim) r g _ _ stb_src stb_tgt OwnT Q fmr true true st_src st_tgt.
  Proof.
    destruct st_src, st_tgt. gstep. eapply hsim_progress; eauto.
  Qed.

  Lemma _hsim_flag_mon
        r
        R_src R_tgt stb_src stb_tgt OwnT Q fmr
        f_src0 f_tgt0 f_src1 f_tgt1 st_src st_tgt
        (SIM: @_hsim r R_src R_tgt stb_src stb_tgt OwnT Q fmr f_src0 f_tgt0 st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_hsim r R_src R_tgt stb_src stb_tgt OwnT Q fmr f_src1 f_tgt1 st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _hsim_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. i. eapply SIM; eauto. }
    { econs 4; eauto. i. eapply SIM; eauto. }
    { econs 5; eauto. i. eapply SIM; eauto. }
    { econs 6; eauto. i. eapply SIM; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9. eauto. }
    { econs 10; eauto. des. esplits. eapply IH; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. eauto. }
    { econs 12; eauto. i. hexploit SIM; eauto. i. des. eapply IH; eauto. }
    { econs 13; eauto. des. esplits; eauto. }
    { econs 14. eapply IHSIM; auto. }
    { econs 15. eapply IHSIM; auto. }
    { econs 16. eapply IHSIM; auto. }
    { econs 17. eapply IHSIM; auto. }
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs 18; eauto. }
  Qed.

  Variant hflagC (r: forall R_src R_tgt
                            (stb_src stb_tgt: gname -> fspec)
                            (OwnT: Σ)
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
                     bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          stb_src stb_tgt
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1
      st_src st_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr f_src0 f_tgt0 st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      hflagC r stb_src stb_tgt OwnT Q fmr f_src1 f_tgt1 st_src st_tgt
  .

  Lemma hflagC_mon:
    monotone11 hflagC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hflagC_mon: paco.

  Structure grespectful clo : Prop :=
    grespect_intro {
        grespect_mon: monotone11 clo;
        grespect_respect :
          forall l r
                 (LE: l <11= r)
                 (GF: l <11= @_hsim r),
            clo l <11= gpaco11 _hsim (cpn11 _hsim) bot11 (rclo11 (clo \12/ gupaco11 _hsim (cpn11 _hsim)) r);
      }.

  Lemma grespect_uclo clo
        (RESPECT: grespectful clo)
    :
      clo <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply grespect11_uclo; eauto with paco.
    econs.
    { eapply RESPECT. }
    i. hexploit grespect_respect.
    { eauto. }
    { eapply LE. }
    { eapply GF. }
    { eauto. }
    i. inv H. eapply rclo11_mon.
    { eauto. }
    i. ss. des; ss. eapply _paco11_unfold in PR0.
    2:{ ii. eapply _hsim_mon; [eapply PR1|]. i. eapply rclo11_mon; eauto. }
    ss. eapply _hsim_mon.
    { eapply PR0; eauto. }
    i. eapply rclo11_clo. right. econs.
    eapply rclo11_mon; eauto. i. inv PR2.
    { left. eapply paco11_mon; eauto. i. ss. des; ss.
      left. auto. }
    { des; ss. right. auto. }
  Qed.

  Lemma hflagC_spec: hflagC <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply grespect_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    gstep.
    eapply _hsim_flag_mon; eauto.
    eapply _hsim_mon; eauto. i. gbase. eapply rclo11_base. auto.
  Qed.

  Variant hsimC
          (r g: forall R_src R_tgt
                       (stb_src stb_tgt: gname -> fspec)
                       (OwnT: Σ)
                       (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                       (fmr: Σ),
              bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          (stb_src stb_tgt: gname -> fspec)
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hsimC_ret
      v_src v_tgt
      st_src st_tgt
      f_src f_tgt
      (RET: current_iProp fmr (Own OwnT ** Q st_src st_tgt v_src v_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, (Ret v_src)) (st_tgt, (Ret v_tgt))
  | hsimC_call
      fsp_src fsp_tgt w0
      fn arg_src arg_tgt
      st_src0 st_tgt0 ktr_src ktr_tgt
      f_src f_tgt
      (SPEC: stb_src fn = fsp_src)
      (SPEC: stb_tgt fn = fsp_tgt)
      (PRE: current_iProp fmr (Own OwnT **
        (∀ x_tgt argp, (fsp_tgt.(precond) x_tgt arg_tgt argp) ==∗
            ∃ x_src FR, (FR ** inv_with w0 st_src0 st_tgt0 **
                         fsp_src.(precond) x_src arg_src argp **
                         (∀ st_src1 st_tgt1 ret_src retp,
                            (FR ** inv_with w0 st_src1 st_tgt1 **
                             fsp_src.(postcond) x_src ret_src retp)
                             ==∗ ∃ ret_tgt J, (fsp_tgt.(postcond) x_tgt ret_tgt retp ** J **
       ⌜(<<SIM: forall fmr1 OwnT
                       (TGT: if has_freeze then fsp_tgt.(postcond) x_tgt ret_tgt retp OwnT else True)
                       (ACC: current_iProp fmr1 (Own OwnT ** J)),
            g _ _ stb_src stb_tgt OwnT Q fmr1 true true (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt)>>)⌝))))
              )
      )
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (Call fn arg_src) >>= ktr_src)
            (st_tgt0, trigger (Call fn arg_tgt) >>= ktr_tgt)
  | hsimC_assert_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
          r _ _ stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassert COND) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_assume_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
          r _ _ stb_src stb_tgt OwnT Q fmr1 true f_tgt (st_src, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Cassume COND) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_assert_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** COND ** IPROPS)),
          r _ _ stb_src stb_tgt OwnT Q fmr1 f_src true (st_src, itr_src) (st_tgt, ktr_tgt tt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassert COND) >>= ktr_tgt)
  | hsimC_assume_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt COND
      IPROPS
      (PRE: current_iProp fmr (Own OwnT ** COND ** IPROPS))
      (SIM: forall fmr1 OwnT (ACC: current_iProp fmr1 (Own OwnT ** IPROPS)),
          r _ _ stb_src stb_tgt OwnT Q fmr1 f_src true  (st_src, itr_src) (st_tgt, ktr_tgt tt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Cassume COND) >>= ktr_tgt)
  | hsimC_syscall
      fn arg rvs
      st_src st_tgt ktr_src ktr_tgt
      f_src f_tgt
      (POST: forall ret,
          g _ _ stb_src stb_tgt OwnT Q fmr true true (st_src, ktr_src ret) (st_tgt, ktr_tgt ret))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Syscall fn arg rvs) >>= ktr_src) (st_tgt, trigger (Syscall fn arg rvs) >>= ktr_tgt)
  | hsimC_tau_src
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, tau;; itr_src) (st_tgt, itr_tgt)
  | hsimC_tau_tgt
      st_src st_tgt itr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, tau;; itr_tgt)
  | hsimC_choose_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: exists x, r _ _ stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Choose X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_choose_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: forall x, r _ _ stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Choose X) >>= ktr_tgt)
  | hsimC_take_src
      X
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: forall x, r _ _ stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src x) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (Take X) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_take_tgt
      X
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: exists x, r _ _ stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt x))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (Take X) >>= ktr_tgt)
  | hsimC_pput_src
      st_src1
      st_src0 st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr true f_tgt (st_src1, ktr_src tt) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, trigger (PPut st_src1) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_pput_tgt
      st_tgt1
      st_src st_tgt0 itr_src ktr_tgt
      f_src f_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt1, ktr_tgt tt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt0, trigger (PPut st_tgt1) >>= ktr_tgt)
  | hsimC_pget_src
      st_src st_tgt ktr_src itr_tgt
      f_src f_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr true f_tgt (st_src, ktr_src st_src) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, trigger (PGet) >>= ktr_src) (st_tgt, itr_tgt)
  | hsimC_pget_tgt
      st_src st_tgt itr_src ktr_tgt
      f_src f_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr f_src true (st_src, itr_src) (st_tgt, ktr_tgt st_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, trigger (PGet) >>= ktr_tgt)
  | hsimC_progress
      st_src st_tgt itr_src itr_tgt
      (SIM: g _ _ stb_src stb_tgt OwnT Q fmr false false (st_src, itr_src) (st_tgt, itr_tgt))
    :
      hsimC r g stb_src stb_tgt OwnT Q fmr true true (st_src, itr_src) (st_tgt, itr_tgt)
  .

  Lemma hsim_indC_mon_gen r0 r1 g0 g1
        (LE0: r0 <11= r1)
        (LE1: g0 <11= g1)
    :
      @hsimC r0 g0 <11= @hsimC r1 g1.
  Proof.
    ii. inv PR.
    { econs 1; eauto. }
    { econs 2; try refl.
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H"; [done|].
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. eauto.
    }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. des. esplits; eauto. }
    { econs 11; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. des. esplits; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
    { econs 18; eauto. }
  Qed.

  Lemma hsim_indC_mon: monotone11 (fun r => @hsimC r r).
  Proof.
    ii. eapply hsim_indC_mon_gen; eauto.
  Qed.

  Lemma hsim_indC_spec:
    (fun r => @hsimC r r) <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply wrespect11_uclo; eauto with paco. econs.
    { eapply hsim_indC_mon. }
    i. inv PR.
    { econs 1; eauto. }
    { econs 2; try refl.
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H"; [done|].
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. i. eapply rclo11_base. eauto.
    }
    { econs 3; et. i. eapply GF in SIM; et. eapply _hsim_mon; et. i. eapply rclo11_base; et. }
    { econs 4; et. i. eapply GF in SIM; et. eapply _hsim_mon; et. i. eapply rclo11_base; et. }
    { econs 5; et. i. eapply GF in SIM; et. eapply _hsim_mon; et. i. eapply rclo11_base; et. }
    { econs 6; et. i. eapply GF in SIM; et. eapply _hsim_mon; et. i. eapply rclo11_base; et. }
    { econs 7; eauto. i. eapply rclo11_base. eauto. }
    { econs 8; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 9; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 10; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 11; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 12; eauto. i. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 13; eauto. des. esplits; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 14; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 15; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 16; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 17; eauto. eapply _hsim_mon; eauto. i. eapply rclo11_base. eauto. }
    { econs 18; eauto. eapply rclo11_base. eauto. }
  Qed.

  Lemma hsimC_spec:
    hsimC <13= gpaco11 (_hsim) (cpn11 _hsim).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; try refl.
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H"; [done|].
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. i. gbase. eauto.
    }
    { guclo hsim_indC_spec. ss. econs 3; eauto. i. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 4; eauto. i. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 5; eauto. i. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 6; eauto. i. gbase. eauto. }
    { gstep. econs 7; eauto. i. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 8; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 9; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 10; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 11; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 12; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 13; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 14; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 15; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 16; eauto. gbase. eauto. }
    { guclo hsim_indC_spec. ss. econs 17; eauto. gbase. eauto. }
    { gstep. econs 18; eauto. i. gbase. eauto. }
  Qed.

  Lemma hsimC_uclo r g:
    @hsimC (gpaco11 (_hsim) (cpn11 _hsim) r g) (gupaco11 (_hsim) (cpn11 _hsim) g) <11= gpaco11 (_hsim) (cpn11 _hsim) r g.
  Proof.
    i. eapply hsimC_spec in PR.  ss.
    eapply gpaco11_gpaco; [eauto with paco|].
    eapply gpaco11_mon; eauto. i. eapply gupaco11_mon; eauto.
  Qed.

  Variant hbindC (r: forall R_src R_tgt
                            (stb_src stb_tgt: gname -> fspec)
                            (OwnT: Σ)
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
        bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          (stb_src stb_tgt: gname -> fspec)
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    :  bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hbindC_intro
      S_src S_tgt
      (P: Any.t -> Any.t -> S_src -> S_tgt -> iProp)
      f_src f_tgt st_src0 st_tgt0 itr_src itr_tgt ktr_src ktr_tgt
      (SIM: @r S_src S_tgt stb_src stb_tgt OwnT P fmr f_src f_tgt (st_src0, itr_src) (st_tgt0, itr_tgt))
      (SIMK: forall fmr1 st_src1 st_tgt1 ret_src ret_tgt OwnT
                    (POST: current_iProp fmr1 (Own OwnT ** P st_src1 st_tgt1 ret_src ret_tgt)),
          @r R_src R_tgt stb_src stb_tgt OwnT Q fmr1 false false (st_src1, ktr_src ret_src) (st_tgt1, ktr_tgt ret_tgt))
    :
      hbindC r stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src0, itr_src >>= ktr_src) (st_tgt0, itr_tgt >>= ktr_tgt)
  .

  Lemma hbindC_mon:
    monotone11 hbindC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hbindC_mon: paco.

  Lemma hbindC_spec: hbindC <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply grespect_uclo.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    remember (st_src0, itr_src). remember (st_tgt0, itr_tgt).
    revert st_src0 itr_src st_tgt0 itr_tgt Heqp Heqp0.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { hexploit SIMK; eauto. i.
      eapply GF in H. guclo hflagC_spec. econs.
      2:{ instantiate (1:=false). ss. }
      2:{ instantiate (1:=false). ss. }
      gstep. eapply _hsim_mon; eauto. i. gbase. eapply rclo11_base. auto.
    }
    { gstep. econs 2; try refl.
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H"; [done|].
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. i. gbase. eapply rclo11_clo_base. left. econs; eauto.
    }
    { eapply hsimC_uclo. econs 3; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { eapply hsimC_uclo. econs 4; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { eapply hsimC_uclo. econs 5; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { eapply hsimC_uclo. econs 6; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { gstep. econs 7; eauto. i. gbase. eapply rclo11_clo_base. left. econs; eauto. }
    { eapply hsimC_uclo. econs 8; eauto. }
    { eapply hsimC_uclo. econs 9; eauto. }
    { des. eapply hsimC_uclo. econs 10; eauto. }
    { eapply hsimC_uclo. econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { eapply hsimC_uclo. econs 12; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { des. eapply hsimC_uclo. econs 13; eauto. }
    { eapply hsimC_uclo. econs 14; eauto. }
    { eapply hsimC_uclo. econs 15; eauto. }
    { eapply hsimC_uclo. econs 16; eauto. }
    { eapply hsimC_uclo. econs 17; eauto. }
    { gstep. econs 18; eauto. gbase. eapply rclo11_clo_base. left. econs; eauto. }
  Unshelve. all: try by ss.
  Qed.

  Variant hmonoC (r: forall R_src R_tgt
                            (stb_src stb_tgt: gname -> fspec)
                            (OwnT: Σ)
                            (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                            (fmr: Σ),
        bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          (stb_src stb_tgt: gname -> fspec)
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hmonoC_intro
      f_src f_tgt Q0
      st_src st_tgt
      (SIM: r _ _ stb_src stb_tgt OwnT Q0 fmr f_src f_tgt st_src st_tgt)
      (MONO: forall st_src st_tgt ret_src ret_tgt,
          (bi_entails (Q0 st_src st_tgt ret_src ret_tgt) (#=> Q st_src st_tgt ret_src ret_tgt)))
    :
      hmonoC r stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt
  .

  Lemma hmonoC_mon:
    monotone11 hmonoC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hmonoC_mon: paco.

  Lemma hmonoC_spec: hmonoC <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply wrespect11_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_upd.
      eapply current_iProp_entail; eauto.
      iIntros "[A B]". iFrame. iStopProof. eauto.
    }
    { econs 2; try refl.
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H"; [done|].
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. i. eapply rclo11_clo_base. econs; eauto.
    }
    { econs 3; eauto. i. hexploit SIM; eauto. i; des. eauto. }
    { econs 4; eauto. i. hexploit SIM; eauto. i; des. eauto. }
    { econs 5; eauto. i. hexploit SIM; eauto. i; des. eauto. }
    { econs 6; eauto. i. hexploit SIM; eauto. i; des. eauto. }
    { econs 7; eauto. i. eapply rclo11_clo_base. econs; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 12; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 13; eauto. des. esplits; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
    { econs 18; eauto. eapply rclo11_clo_base. econs; eauto. }
  Qed.

  Variant hframeC_aux (r: forall R_src R_tgt
                                 (stb_src stb_tgt: gname -> fspec)
                             (OwnT: Σ)
                             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                             (res: Σ),
        bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          (stb_src stb_tgt: gname -> fspec)
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (res: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hframeC_aux_intro
      res0 frm
      f_src f_tgt
      st_src st_tgt
      (PRE: URA.wf res)
      (UPD: URA.updatable res (res0 ⋅ frm))
      (SIM: r _ _ stb_src stb_tgt OwnT (fun st_src st_tgt ret_src ret_tgt => Own frm -* #=> Q st_src st_tgt ret_src ret_tgt)
              res0 f_src f_tgt st_src st_tgt)
    :
      hframeC_aux r stb_src stb_tgt OwnT Q res f_src f_tgt st_src st_tgt
  .

  Lemma hframeC_aux_mon:
    monotone11 hframeC_aux.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hframeC_aux_mon: paco.

  Lemma hframeC_aux_spec: hframeC_aux <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply wrespect11_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    remember (λ (st_src st_tgt : Any.t) (ret_src : x0) (ret_tgt : x1),
             (Own frm ==∗ x5 st_src st_tgt ret_src ret_tgt)%I) as Q2.
    rename x4 into OwnT. rename x5 into Q. rename x6 into fmr_before. rename res0 into fmr_after.
    rename frm into frame.
    revert HeqQ2. revert frame Q fmr_before PRE UPD.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_upd. eapply current_iProp_updatable; et.
      eapply current_iProp_frame_own; eauto.
      { eapply URA.updatable_wf; et. }
      eapply current_iProp_entail; eauto. iIntros "[A B]". iFrame. eauto.
    }
    { econs 2; try refl.
      eapply current_iProp_updatable; [et|et|]. eapply current_iProp_frame_own.
      { eapply URA.updatable_wf; et. }
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H1"; [done|].
      iIntros. iDes. iSpecialize ("H11" with "H1"). iMod "H11". iDes.
      iModIntro. iSplits. iSplitR "H111".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H111" with "[H H1 H2]").
        { iFrame. }
        iMod "H111". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. i.
        eapply current_iProp_entail in ACC; cycle 1.
        { iIntros "[H0 [H1 H2]]". iCombine "H0 H2" as "H". instantiate (1:= _ ** _).
          iSplitR "H"; iAssumption. }
        eapply current_iProp_frame_own_rev in ACC. des.
        eapply rclo11_clo_base. econs; eauto.
    }
    { econs 3; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail; try eassumption.
        iIntros; iDes. iFrame. iAccu.
      } clear PRE.
      i. eapply current_iProp_entail in ACC; cycle 1.
      { iIntros. iDes. instantiate (1:=Own frame ** _). iFrame. iAccu. }
      eapply current_iProp_frame_own_rev in ACC. des.
      eapply SIM; et.
    }
    { econs 4; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail; try eassumption.
        iIntros; iDes. iFrame. iAccu.
      } clear PRE.
      i. eapply current_iProp_entail in ACC; cycle 1.
      { iIntros. iDes. instantiate (1:=Own frame ** _). iFrame. iAccu. }
      eapply current_iProp_frame_own_rev in ACC. des.
      eapply SIM; et.
      eapply current_iProp_entail; et. iIntros; iDes; iFrame.
    }
    { econs 5; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail; try eassumption.
        iIntros; iDes. iFrame. iAccu.
      } clear PRE.
      i. eapply current_iProp_entail in ACC; cycle 1.
      { iIntros. iDes. instantiate (1:=Own frame ** _). iFrame. iAccu. }
      eapply current_iProp_frame_own_rev in ACC. des.
      eapply SIM; et.
      eapply current_iProp_entail; et. iIntros; iDes; iFrame.
    }
    { econs 6; eauto.
      { eapply current_iProp_updatable; et. eapply current_iProp_frame_own; eauto.
        { eapply URA.updatable_wf; et. }
        eapply current_iProp_entail; try eassumption.
        iIntros; iDes. iFrame. iAccu.
      } clear PRE.
      i. eapply current_iProp_entail in ACC; cycle 1.
      { iIntros. iDes. instantiate (1:=Own frame ** _). iFrame. iAccu. }
      eapply current_iProp_frame_own_rev in ACC. des.
      eapply SIM; et.
    }
    { econs 7; eauto. i. eapply rclo11_clo_base. econs; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 12; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 13; eauto. des. esplits; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
    { econs 18; eauto. eapply rclo11_clo_base. econs; eauto. }
  Qed.

  Variant hframeC (r: forall R_src R_tgt
                             (stb_src stb_tgt: gname -> fspec)
                             (OwnT: Σ)
                             (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                             (fmr: Σ),
                      bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          (stb_src stb_tgt: gname -> fspec)
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hframeC_intro
      P0 P1
      f_src f_tgt
      st_src st_tgt
      (PRE: current_iProp fmr (P0 ** P1))
      (SIM: forall fmr (PRE: current_iProp fmr P1),
          r _ _ stb_src stb_tgt OwnT (fun st_src st_tgt ret_src ret_tgt => P0 -* #=> Q st_src st_tgt ret_src ret_tgt) fmr f_src f_tgt st_src st_tgt)
    :
      hframeC r stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt
  .

  Lemma hframeC_spec: hframeC <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    ii. inv PR.
    inv PRE. rr in IPROP.
    autounfold with iprop in IPROP.
    autorewrite with iprop in IPROP. des. clarify.
    guclo hframeC_aux_spec. econs.
    { ss. }
    { rewrite URA.add_comm. eauto. }
    { guclo hmonoC_spec. econs.
      { gbase. eapply SIM. econs; eauto.
        - eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists a; r_solve.
        - refl.
      }
      { i. ss. iIntros "H0". iModIntro. iIntros "H1".
        iApply bupd_trans. iApply "H0".
        iStopProof. uipropall.
        i. red in H. des. clarify. esplits; [eassumption|eauto].
        i. eapply URA.wf_extends. { exists ctx. r_solve. } r_wf H.
      }
    }
  Qed.

  Variant hupdC (r: forall R_src R_tgt
                           (stb_src stb_tgt: gname -> fspec)
                           (OwnT: Σ)
                           (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                           (fmr: Σ),
                     bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          (stb_src stb_tgt: gname -> fspec)
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hupdC_intro
      f_src f_tgt
      st_src st_tgt
      fmr1
      (WF: URA.wf fmr)
      (UPD: URA.updatable fmr fmr1)
      (SIM: r _ _ stb_src stb_tgt OwnT Q fmr1 f_src f_tgt st_src st_tgt)
    :
      hupdC r stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt
  .

  Lemma hupdC_mon:
    monotone11 hupdC.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hupdC_mon: paco.

  Lemma hupdC_spec: hupdC <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply wrespect11_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    gen x6.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto. eapply current_iProp_updatable; et. }
    { econs 2; try refl.
      eapply current_iProp_updatable; [et|et|].
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H"; [done|].
      iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. i. eapply rclo11_clo_base. econs; eauto.
        { eapply ACC. }
        { refl. }
    }
    { econs 3; et. { eapply current_iProp_updatable; et. } i. eapply SIM; try apply ACC; refl. }
    { econs 4; et. { eapply current_iProp_updatable; et. } i. eapply SIM; try apply ACC; refl. }
    { econs 5; et. { eapply current_iProp_updatable; et. } i. eapply SIM; try apply ACC; refl. }
    { econs 6; et. { eapply current_iProp_updatable; et. } i. eapply SIM; try apply ACC; refl. }
    { econs 7; eauto. i. eapply rclo11_clo_base; econs; et. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 12; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 13; eauto. des. esplits; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
    { econs 18; eauto. eapply rclo11_clo_base. econs; eauto. }
  Qed.

  Variant hupdC2 (r: forall R_src R_tgt
                            (stb_src stb_tgt: gname -> fspec)
                           (OwnT: Σ)
                           (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
                           (fmr: Σ),
                     bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop)
          {R_src R_tgt}
          (stb_src stb_tgt: gname -> fspec)
          (OwnT: Σ)
          (Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fmr: Σ)
    : bool -> bool -> Any.t * itree Es' R_src -> Any.t * itree Es' R_tgt -> Prop :=
  | hupdC2_intro
      f_src f_tgt
      st_src st_tgt
      OwnT1
      (* (WF: URA.wf fmr) *)
      (UPD: URA.updatable OwnT1 OwnT)
      (SIM: r _ _ stb_src stb_tgt OwnT1 Q fmr f_src f_tgt st_src st_tgt)
    :
      hupdC2 r stb_src stb_tgt OwnT Q fmr f_src f_tgt st_src st_tgt
  .

  Lemma hupdC2_mon:
    monotone11 hupdC2.
  Proof. ii. inv IN; econs; et. Qed.
  Hint Resolve hupdC2_mon: paco.

  Lemma hupdC2_spec: hupdC2 <12= gupaco11 (_hsim) (cpn11 _hsim).
  Proof.
    eapply wrespect11_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM.
    gen x4.
    induction SIM using _hsim_ind2; i; clarify; ired_both.
    { econs 1; eauto.
      eapply current_iProp_upd.
      eapply current_iProp_entail; eauto.
      iIntros "[A B]". iFrame. iApply Own_Upd; eauto. }
    { econs 2; try refl.
      eapply current_iProp_upd.
      eapply current_iProp_entail; try eassumption.
      iIntros; iDes. iSplitL "H".
      { iApply Own_Upd; eauto. }
      iModIntro. iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
      iModIntro. iSplits. iSplitR "H11".
      - iFrame. iAccu.
      - iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
        { iFrame. }
        iMod "H11". iDes. iModIntro. iSplits; iFrame.
        { iAccu. }
        iPureIntro. i. eapply rclo11_clo_base. econs; eauto.
        { refl. }
    }
    { econs 3; eauto.
      {
        eapply current_iProp_upd.
        eapply current_iProp_entail; try eassumption.
        iIntros. iDes. iFrame. iSplitL "H".
        { iApply Own_Upd; eauto. }
        iModIntro. iAccu.
      }
      i. eapply SIM; eauto; refl.
    }
    { econs 4; eauto.
      {
        eapply current_iProp_upd.
        eapply current_iProp_entail; try eassumption.
        iIntros. iDes. iFrame. iSplitL "H".
        { iApply Own_Upd; eauto. }
        iModIntro. iAccu.
      }
      i. eapply SIM; eauto; refl.
    }
    { econs 5; eauto.
      {
        eapply current_iProp_upd.
        eapply current_iProp_entail; try eassumption.
        iIntros. iDes. iFrame. iSplitL "H".
        { iApply Own_Upd; eauto. }
        iModIntro. iAccu.
      }
      i. eapply SIM; eauto; refl.
    }
    { econs 6; eauto.
      {
        eapply current_iProp_upd.
        eapply current_iProp_entail; try eassumption.
        iIntros. iDes. iFrame. iSplitL "H".
        { iApply Own_Upd; eauto. }
        iModIntro. iAccu.
      }
      i. eapply SIM; eauto; refl.
    }
    { econs 7; eauto. i. eapply rclo11_clo_base. econs; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. des. esplits; eauto. }
    { econs 11; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 12; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
    { econs 13; eauto. des. esplits; eauto. }
    { econs 14; eauto. }
    { econs 15; eauto. }
    { econs 16; eauto. }
    { econs 17; eauto. }
    { econs 18; eauto. eapply rclo11_clo_base. econs; eauto. }
  Qed.

  Definition add_hframe (FRAME: iProp) (fsp: fspec): fspec :=
    mk_fspec (λ x a b, fsp.(precond) x a b ** FRAME)
      (λ x a b, fsp.(postcond) x a b ** FRAME).

  Lemma current_iProp_frame_own_rev_gen res0 Q P
        (CUR: current_iProp res0 (Q ** P))
    :
      exists qres res1, URA.wf res0 /\ URA.updatable res0 (res1 ⋅ qres) ∧ (Own qres ⊢ Q) ∧ current_iProp res1 P.
  Proof.
    inv CUR. uipropall.
    unfold URA.extends in *. des; clarify.
    esplits.
    3: { uipropall. i. des; subst. eapply iProp_mono; et. exists ctx. instantiate (1:=a). r_solve. }
    all: et.
    { rewrite URA.add_comm; et. }
    econs; et; try refl.
    eapply URA.updatable_wf; et. etrans; et. eapply URA.extends_updatable. exists a; r_solve.
  Qed.

  Theorem hframing_right
    R_src R_tgt
    stb_src stb_tgt
    OwnT Q fmr f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    :
    (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    ->
    (∀ (FRAME: iProp) xr (FRAMERES: Own xr ⊢ FRAME), URA.wf (fmr ⋅ xr) ->
          hsim (λ fn, add_hframe FRAME (stb_src fn)) stb_tgt
            (OwnT) (λ a b c d, Q a b c d ** FRAME)
            (fmr ⋅ xr) f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    (* split; i. *)
    i.
    - ginit. { eapply cpn11_wcompat. eauto with paco. }
      revert_until I. gcofix CIH. i.
      remember (st_tgt, itr_tgt) as tmp.
      remember (st_src, itr_src) as tmp'.
      revert Heqtmp Heqtmp'. revert st_src itr_src st_tgt itr_tgt.
      hexploit1 H0.
      { eapply URA.wf_extends; et. eexists xr; r_solve. }
      induction H0 using hsim_ind; i; clarify.
      + eapply hsimC_uclo; econs 1.
        eapply current_iProp_frame_own; et.
        eapply current_iProp_entail; eauto. iIntros; iDes. iFrame. iApply FRAMERES; et.
      + eapply hsimC_uclo. econs 2; try refl.
        eapply current_iProp_frame_own; et.
        eapply current_iProp_entail; try eassumption. clear PRE.
        iIntros; iDes. iSplitL "H1"; [done|].
        iIntros. iDes. iSpecialize ("H11" with "H1"). iMod "H11". iDes.
        iModIntro. iSplits. iSplitR "H11".
        * iFrame. iDestruct (FRAMERES with "H") as "H". iFrame. iAccu.
        * iIntros. iDes. iSpecialize ("H" with "[H11 H1 H2]").
          { iFrame. }
          iMod "H". iDes. iModIntro. iSplits; iFrame.
          { iAccu. }
          iPureIntro. i.
          eapply current_iProp_entail in ACC.
          2: { iIntros; iDes. instantiate (1:=_ ** _). iSplitL "H1"; iAccu. }
          eapply current_iProp_frame_own_rev_gen in ACC. des.
          guclo hupdC_spec. econs; et.
          gbase. eapply CIH; et.
          { eapply URA.updatable_wf; et. }
      + eapply hsimC_uclo. econs 3; eauto.
        { eapply current_iProp_frame_own; et.
          eapply current_iProp_entail; try eassumption.
          iIntros; iDes. iFrame. iAccu.
        }
        clear PRE. i. eapply current_iProp_entail in ACC.
        2: { instantiate (1:=_ ** _). iIntros. iDes. iSplitL "H11"; iAccu. }
        eapply current_iProp_frame_own_rev in ACC. des.
        exploit SIM; et.
        i; des. guclo hupdC_spec. econs; et. eapply IH; et.
        eapply URA.updatable_wf; et.
      + eapply hsimC_uclo. econs 4; eauto.
        { eapply current_iProp_frame_own; et.
          eapply current_iProp_entail; try eassumption.
          iIntros; iDes. iFrame. iAccu.
        }
        clear PRE. i. eapply current_iProp_entail in ACC.
        2: { instantiate (1:=_ ** _). iIntros. iDes. iSplitL "H11"; iAccu. }
        eapply current_iProp_frame_own_rev in ACC. des.
        exploit SIM; et. { eapply current_iProp_entail; et. iIntros; iDes; iFrame. }
        i; des. guclo hupdC_spec. econs; et. eapply IH; et.
        eapply URA.updatable_wf; et.
      + eapply hsimC_uclo. econs 5; eauto.
        { eapply current_iProp_frame_own; et.
          eapply current_iProp_entail; try eassumption.
          iIntros; iDes. iFrame. iAccu.
        }
        clear PRE. i. eapply current_iProp_entail in ACC.
        2: { instantiate (1:=_ ** _). iIntros. iDes. iSplitL "H11"; iAccu. }
        eapply current_iProp_frame_own_rev in ACC. des.
        exploit SIM; et. { eapply current_iProp_entail; et. iIntros; iDes; iFrame. }
        i; des. guclo hupdC_spec. econs; et. eapply IH; et.
        eapply URA.updatable_wf; et.
      + eapply hsimC_uclo. econs 6; eauto.
        { eapply current_iProp_frame_own; et.
          eapply current_iProp_entail; try eassumption.
          iIntros; iDes. iFrame. iAccu.
        }
        clear PRE. i. eapply current_iProp_entail in ACC.
        2: { instantiate (1:=_ ** _). iIntros. iDes. iSplitL "H11"; iAccu. }
        eapply current_iProp_frame_own_rev in ACC. des.
        exploit SIM; et.
        i; des. guclo hupdC_spec. econs; et. eapply IH; et.
        eapply URA.updatable_wf; et.
      + eapply hsimC_uclo. econs; eauto. i. gbase. eapply CIH; et.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. gbase. eapply CIH; et.
  Qed.

  (* Lemma iProp_eta: ∀ (x y: iProp), x.(iProp_pred) = y.(iProp_pred) -> x = y. *)
  (* Proof. *)
  (*   i. destruct x, y; ss. subst. f_equal. eapply proof_irr. *)
  (* Qed. *)

  (* Lemma add_hframe_True: ∀ (stb: gname -> fspec), (add_hframe True ∘ stb) = stb. *)
  (* Proof. *)
  (*   i. extensionality fn. destruct (stb fn) eqn:T; ss. unfold add_hframe. ss. *)
  (*   f_equal; ss. *)
  (*   - extensionalities x y z. eapply iProp_eta; ss. extensionalities r. eapply Axioms.prop_ext. *)
  (*     split; i. *)
  (*     + uipropall; des; subst. eapply iProp_mono; et. (*** no way to prove URA.wf (a ⋅ b ***) *)
  (* Qed. *)

  Theorem hframing_left_strong
    R_src R_tgt
    stb_src stb_tgt
    OwnT Q fmr f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    :
    (URA.wf fmr ->
          hsim (λ fn, add_hframe True%I (stb_src fn)) stb_tgt
            OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    ->
    (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    i. hexploit1 H; ss.
    - ginit. { eapply cpn11_wcompat. eauto with paco. }
      revert_until I. gcofix CIH. i.
      remember (st_tgt, itr_tgt) as tmp.
      remember (st_src, itr_src) as tmp'.
      revert Heqtmp Heqtmp'. revert st_src itr_src st_tgt itr_tgt.
      remember (add_hframe True ∘ stb_src) as tmp''. revert Heqtmp''.
      induction H1 using hsim_ind; i; clarify.
      + eapply hsimC_uclo; econs 1. ss.
      + eapply hsimC_uclo. econs 2; try refl.
        eapply current_iProp_entail; try eassumption. clear PRE.
        iIntros; iDes. iSplitL "H"; [done|].
        iIntros. iDes. iSpecialize ("H1" with "H"). iMod "H1". iDes.
        iModIntro. iSplits. iSplitR "H11".
        * iFrame. iFrame. iAccu.
        * iIntros. iDes. iSpecialize ("H11" with "[H H1 H2]").
          { iFrame. }
          iMod "H11". iDes. iModIntro. iSplits; iFrame.
          { iAccu. }
          iPureIntro. i.
          eapply current_iProp_entail in ACC.
          2: { iIntros; iDes. instantiate (1:=_ ** _). iSplitL "H1"; iAccu. }
          eapply current_iProp_frame_own_rev_gen in ACC. des.
          guclo hupdC_spec. econs; et.
          gbase. eapply CIH; et.
          { eapply URA.updatable_wf; et. }
          eapply H1; et. eapply current_iProp_frame_own.
          { eapply URA.updatable_wf; et. }
          { eapply current_iProp_entail; et. iIntros; iFrame. iApply ACC1; ss. }
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. gbase. eapply CIH; et.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. gbase. eapply CIH; et.
  Qed.

  Theorem hframing_left
    R_src R_tgt
    stb_src stb_tgt
    OwnT Q fmr f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    :
    (∀ (FRAME: iProp) xr (FRAMERES: Own xr ⊢ FRAME), URA.wf (fmr ⋅ xr) ->
          hsim (λ fn, add_hframe FRAME (stb_src fn)) stb_tgt
            (OwnT) (λ a b c d, Q a b c d ** FRAME)
            (fmr ⋅ xr) f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    ->
    (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    i. eapply hframing_left_strong; et. i.
    ginit. { eapply cpn11_wcompat. eauto with paco. }
    guclo hmonoC_spec. econs.
    { gfinal. right. specialize (H True%I ε). rewrite URA.unit_id in H. eapply H; et. }
    iIntros; iDes. iModIntro. ss.
  Qed.

  Theorem hframing
    R_src R_tgt
    stb_src stb_tgt
    OwnT Q fmr f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    :
    (∀ (FRAME: iProp) xr (FRAMERES: Own xr ⊢ FRAME), URA.wf (fmr ⋅ xr) ->
          hsim (λ fn, add_hframe FRAME (stb_src fn)) stb_tgt
            (OwnT) (λ a b c d, Q a b c d ** FRAME)
            (fmr ⋅ xr) f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    <->
    (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    split.
    - eapply hframing_left.
    - eapply hframing_right.
  Qed.
  Require Import HoareFacts.

  Theorem vframing_right
    (NOFREEZE: has_freeze = false)
    R_src R_tgt
    stb_src stb_tgt
    Q f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    fmr OwnT
    :
    (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    ->
      (∀ stb_fr,
          URA.wf fmr -> hsim (stb_fr |> stb_src)%stb (stb_fr |> stb_tgt)%stb OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    (* split; i. *)
    i.
    - ginit. { eapply cpn11_wcompat. eauto with paco. }
      revert_until I. gcofix CIH. i.
      remember (st_tgt, itr_tgt) as tmp.
      remember (st_src, itr_src) as tmp'.
      revert Heqtmp Heqtmp'. revert st_src itr_src st_tgt itr_tgt.
      specialize (H0 H1).
      induction H0 using hsim_ind; i; clarify.
      + eapply hsimC_uclo; econs 1. eauto.
      + eapply hsimC_uclo. econs 2; try refl.
        eapply current_iProp_entail; try eassumption. clear PRE.
        iIntros; iDes. iSplitL "H"; [done|].
        iIntros. iDes. ss. destruct x_tgt as [x_fr x_tgt]. ss. iDes.
        iSpecialize ("H1" with "H2"). iMod "H1". iDes.
        iModIntro. iExists (x_fr, x_src). ss. iSplits. iSplitR "H11".
        * iFrame. iSplitL "H1"; [iAssumption|]. iSplits; iFrame.
        * iIntros. iDes. iSpecialize ("H11" with "[H H2 H12]").
          { iFrame. }
          iMod "H11". iDes. iModIntro. iSplits; iFrame.
          { iSplitR "H111"; [|iAssumption]. iSplits; iFrame. }
          iPureIntro. i.
          gbase. eapply CIH; et.
          { eapply ACC. }
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. gbase. eapply CIH; et.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. gbase. eapply CIH; et.
  Qed.

  Theorem vframing_left_strong
    (NOFREEZE: has_freeze = false)
    R_src R_tgt
    stb_src stb_tgt
    Q f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    fmr OwnT
    :
    (URA.wf fmr -> hsim (ε |> stb_src)%stb (ε |> stb_tgt)%stb OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    ->
    (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    (* split; i. *)
    i.
    - ginit. { eapply cpn11_wcompat. eauto with paco. }
      revert_until I. gcofix CIH. i.
      remember (st_tgt, itr_tgt) as tmp.
      remember (st_src, itr_src) as tmp'.
      revert Heqtmp Heqtmp'. revert st_src itr_src st_tgt itr_tgt.
      specialize (H0 H1).
      remember (ε |> stb_src)%stb as tmp0.
      remember (ε |> stb_tgt)%stb as tmp1. gen stb_src stb_tgt.
      induction H0 using hsim_ind; i; clarify.
      + eapply hsimC_uclo; econs 1. eauto.
      + eapply hsimC_uclo. econs 2; try refl.
        eapply current_iProp_entail; try eassumption. clear PRE.
        iIntros; iDes. iSplitL "H"; [done|].
        iIntros. iDes. ss.
        iSpecialize ("H1" $! (tt, x_tgt)). ss.
        iDestruct ("H1" with "[H]") as "A".
        { iSplits; ss. }
        iMod "A". iDes. des_ifs. ss. des_u. iDes. subst. rename m into x_src.
        iModIntro. iExists (x_src). ss. iSplits. iSplitR "A1".
        * iFrame. iAccu.
        * iIntros. iDes. iSpecialize ("A1" with "[H H1 H2]").
          { iFrame. iSplits; ss. }
          iMod "A1". iDes. subst. iModIntro. iSplits; iFrame.
          { iAccu. }
          iPureIntro. i.
          gbase. eapply CIH; et.
          { eapply ACC. }
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et. eapply ACC.
      + eapply hsimC_uclo. econs; eauto. i. gbase. eapply CIH; et.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. econs; eauto. i. eapply SIM; et.
      + eapply hsimC_uclo. des. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto.
      + eapply hsimC_uclo. econs; eauto. gbase. eapply CIH; et.
  Qed.

  Theorem vframing_left
    (NOFREEZE: has_freeze = false)
    R_src R_tgt
    stb_src stb_tgt
    Q f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    fmr OwnT
    :
    (∀ stb_fr, URA.wf fmr -> hsim (stb_fr |> stb_src)%stb (stb_fr |> stb_tgt)%stb OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    ->
      (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    i. eapply vframing_left_strong; et.
  Qed.

  Theorem vframing
    (NOFREEZE: has_freeze = false)
    R_src R_tgt
    stb_src stb_tgt
    Q f_src f_tgt st_src st_tgt (itr_src: itree Es' R_src) (itr_tgt: itree Es' R_tgt)
    fmr OwnT
    :
    (∀ stb_fr, URA.wf fmr -> hsim (stb_fr |> stb_src)%stb (stb_fr |> stb_tgt)%stb OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
    <->
    (URA.wf fmr -> hsim stb_src stb_tgt OwnT Q fmr f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt))
  .
  Proof.
    split.
    - eapply vframing_left; et.
    - eapply vframing_right; et.
  Qed.

End SIM.
#[export] Hint Resolve _hsim_mon: paco.
#[export] Hint Resolve cpn11_wcompat: paco.
Arguments hsim [_ _] _ _ [_ _].
