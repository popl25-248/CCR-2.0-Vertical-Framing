Require Import Coqlib AList.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.
Require Import Any.
Require Import IRed.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.



(*** TODO: move to ITreelib, and replace raw definitions with this ***)
Definition trivial_Handler `{E -< F}: Handler E F := fun T X => trigger X.

Inductive ord: Type :=
| ord_pure (n: Ord.t)
| ord_top
.

Definition is_pure (o: ord): bool := match o with | ord_pure _ => true | _ => false end.

Definition ord_lt (next cur: ord): Prop :=
  match next, cur with
  | ord_pure next, ord_pure cur => (next < cur)%ord
  | _, ord_top => True
  | _, _ => False
  end
.

(**
(defface hi-light-green-b
  '((((min-colors 88)) (:weight bold :foreground "dark magenta"))
    (t (:weight bold :foreground "dark magenta")))
  "Face for hi-lock mode."
  :group 'hi-lock-faces)

 **)


Section PSEUDOTYPING.

(*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)

Require Import IPM.

Section FSPEC.
  Context `{Σ: GRA.t}.

  (*** spec table ***)
  Record fspec: Type := mk_fspec {
    meta: Type;
    precond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
    postcond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
  }
  .

  (** only works if there is no varg **)
  Definition fspec_add (f0 f1: fspec): fspec :=
    @mk_fspec
      (f0.(meta) * f1.(meta))
      (fun '(x0, x1) arg_src arg_tgt =>
         (⌜arg_src = arg_tgt⌝ ** f0.(precond) x0 arg_src arg_tgt ** f1.(precond) x1 arg_src arg_tgt)%I)
      (fun '(x0, x1) ret_src ret_tgt =>
         (⌜ret_src = ret_tgt⌝ ** f0.(postcond) x0 ret_src ret_tgt ** f1.(postcond) x1 ret_src ret_tgt)%I)
  .

  Definition fspec_append (f0 f1: fspec): fspec :=
    @mk_fspec
      (f0.(meta) * f1.(meta))
      (fun '(x0, x1) arg_src arg_tgt =>
         (∃ arg_mid, f0.(precond) x0 arg_mid arg_tgt ** f1.(precond) x1 arg_src arg_mid)%I)
      (fun '(x0, x1) ret_src ret_tgt =>
         (∃ ret_mid, f0.(postcond) x0 ret_mid ret_tgt ** f1.(postcond) x1 ret_src ret_mid)%I)
  .

  Definition fspec_equiv (f0 f1: fspec): Prop :=
    exists (to: f0.(meta) -> f1.(meta))
           (from: f1.(meta) -> f0.(meta)),
      <<PATH: to ∘ from = id ∧ from ∘ to = id>> ∧
        <<PRE: ∀ x a b, f0.(precond) x a b ≡ f1.(precond) (to x) a b>> ∧
        <<POST: ∀ x a b, f0.(postcond) x a b ≡ f1.(postcond) (to x) a b>>
  .

  Definition fspec_trivial: fspec :=
    mk_fspec (meta:=unit) (fun _ argh argl => (⌜argh = argl⌝: iProp)%I)
             (fun _ reth retl => (⌜reth = retl⌝: iProp)%I)
  .

  Class FspecSimpl (fsp: fspec): Prop := {
    fspecSimplPre: ∀ x a b, fsp.(precond) x a b ⊢ ⌜a = b⌝;
    fspecSimplPost: ∀ x a b, fsp.(postcond) x a b ⊢ ⌜a = b⌝;
  }
  .

  Global Program Instance fspec_trivial_fspecSimpl: FspecSimpl fspec_trivial.
  Next Obligation.
    i. iIntros. ss.
  Qed.
  Next Obligation.
    i. iIntros. ss.
  Qed.

  (* Definition fspec_unit: fspec := *)
  (*   mk_fspec (meta:=unit) (fun _ argh argl => True%I) (fun _ reth retl => True%I) *)
  (* . *)

  Declare Scope fspec_scope.
  Delimit Scope fspec_scope with fspec.
  Bind Scope fspec_scope with fspec.
  Notation "(≡)" := fspec_equiv : fspec_scope.
  Infix "≡" := fspec_equiv (at level 70) : fspec_scope.
  Notation "(**)" := fspec_add : fspec_scope.
  Infix "**" := fspec_add (at level 99): fspec_scope.
  Notation "(|>)" := fspec_append : fspec_scope.
  Infix "|>" := fspec_append (at level 99): fspec_scope.
  Notation "'ε'" := fspec_trivial (at level 0): fspec_scope.
  Local Open Scope fspec_scope.

  Global Program Instance fspec_equiv_Equiv: Equivalence (≡).
  Next Obligation.
    ii. r. exists id, id. ss.
  Qed.
  Next Obligation.
    ii. r. r in H. des. esplits; et.
    { ii. rewrite PRE. change (to (from x0)) with ((to ∘ from) x0). rewrite PATH. ss. }
    { ii. rewrite POST. change (to (from x0)) with ((to ∘ from) x0). rewrite PATH. ss. }
  Qed.
  Next Obligation.
    ii. r. r in H. r in H0. des. esplits; et.
    { instantiate (1:=from0 ∘ from). instantiate (1:=to ∘ to0).
      change (to ∘ to0 ∘ (from0 ∘ from)) with (to ∘ (to0 ∘ from0) ∘ from).
      rewrite PATH1. unfold id. rewrite PATH. ss.
    }
    { change (from0 ∘ from ∘ (to ∘ to0)) with (from0 ∘ (from ∘ to) ∘ to0).
      rewrite PATH0. unfold id. rewrite PATH2. ss.
    }
    { ii. rewrite PRE0. rewrite PRE. ss. }
    { ii. rewrite POST0. rewrite POST. ss. }
  Qed.


  (* Lemma iProp_eta: ∀ (P0 P1: iProp), P0.(iProp_pred) = P1.(iProp_pred) -> P0 = P1. *)
  (* Proof. *)
  (*   i. destruct P0, P1; ss. clarify. f_equal. eapply proof_irr. *)
  (* Qed. *)

  (* Lemma iProp_ext: ∀ (P0 P1: iProp), (P0 ⊣⊢ P1)%I -> P0 = P1. *)
  (* Proof. *)
  (*   i. eapply iProp_eta. extensionality x. *)
  (*   inv H. eapply Axioms.prop_ext. eauto. *)
  (* Qed. *)

  Lemma fspec_add_comm: ∀ (f0 f1: fspec), (f0 ** f1) ≡ (f1 ** f0).
  Proof.
    ii. r. ss. esplits; et.
    { instantiate (1:= fun '(a, b) => (b, a)).
      instantiate (1:= fun '(a, b) => (b, a)).
      extensionality x. des_ifs.
    }
    { extensionality x. des_ifs. }
    { ii. des_ifs. iIntros. iSplit; iIntros "[A B]"; iFrame. }
    { ii. des_ifs. iIntros. iSplit; iIntros "[A B]"; iFrame. }
  Qed.

  Lemma fspec_add_assoc: ∀ (f0 f1 f2: fspec), (((f0 ** f1) ** f2) ≡ (f0 ** (f1 ** f2))).
  Proof.
    ii. r. ss. esplits; et.
    { instantiate (1:= fun '(a, (b, c)) => (a, b, c)).
      instantiate (1:= fun '((a, b), c) => (a, (b, c))).
      extensionality x. des_ifs.
    }
    { extensionality x. des_ifs. }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes; subst. iSplits; et. iFrame. ss.
      - iDes; subst. iSplits; et. iFrame. ss.
    }
    { ii. des_ifs. iIntros.
      iSplit; iIntros; iDes; subst; iSplits; iFrame; ss.
    }
  Qed.

  Lemma fspec_add_unit_l: ∀ `{FspecSimpl f0}, (f0) ≡ (ε ** f0).
  Proof.
    ii. r. esplits; ss.
    { instantiate (1:= fun '(_, a) => a).
      instantiate (1:= fun a => (tt, a)).
      extensionality x. des_ifs. des_u; ss.
    }
    { extensionality x. des_ifs. }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. inv H. iDestruct (fspecSimplPre0 with "A") as "%B". subst. iSplits; ss.
      - iDes. inv H. ss.
    }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. inv H. iDestruct (fspecSimplPost0 with "A") as "%B". subst. iSplits; ss.
      - iDes. inv H. ss.
    }
  Qed.

  Lemma fspec_add_unit_r: ∀ `{FspecSimpl f0}, (f0) ≡ (f0 ** ε).
  Proof.
    ii. r. esplits; ss.
    { instantiate (1:= fun '(a, _) => a).
      instantiate (1:= fun a => (a, tt)).
      extensionality x. des_ifs. des_u; ss.
    }
    { extensionality x. des_ifs. }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. inv H. iDestruct (fspecSimplPre0 with "A") as "%B". subst. iSplits; ss.
      - iDes. inv H. ss.
    }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. inv H. iDestruct (fspecSimplPost0 with "A") as "%B". subst. iSplits; ss.
      - iDes. inv H. ss.
    }
  Qed.

  Lemma fspec_append_assoc: ∀ (f0 f1 f2: fspec), (((f0 |> f1) |> f2) ≡ (f0 |> (f1 |> f2))).
  Proof.
    ii. r. ss. esplits; et.
    { instantiate (1:= fun '(a, (b, c)) => (a, b, c)).
      instantiate (1:= fun '((a, b), c) => (a, (b, c))).
      extensionality x. des_ifs.
    }
    { extensionality x. des_ifs. }
    { ii. des_ifs. iSplit; iIntros.
      - iDes; subst. iSplits; et. iFrame. iSplits; iFrame.
      - iDes; subst. iSplits; et. iFrame. iSplits; iFrame.
    }
    { ii. des_ifs. iSplit; iIntros.
      - iDes; subst. iSplits; et. iFrame. iSplits; iFrame.
      - iDes; subst. iSplits; et. iFrame. iSplits; iFrame.
    }
  Qed.

  Lemma fspec_append_unit_l: ∀ f0, (f0) ≡ (ε |> f0).
  Proof.
    ii. r. esplits; ss.
    { instantiate (1:= fun '(_, a) => a).
      instantiate (1:= fun a => (tt, a)).
      extensionality x. des_ifs. des_u; ss.
    }
    { extensionality x. des_ifs. }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. iSplits; ss.
      - iDes. subst. iSplits; ss.
    }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. iSplits; ss.
      - iDes. subst. iSplits; ss.
    }
  Qed.

  Lemma fspec_append_unit_r: ∀ f0, (f0) ≡ (f0 |> ε).
  Proof.
    ii. r. esplits; ss.
    { instantiate (1:= fun '(a, _) => a).
      instantiate (1:= fun a => (a, tt)).
      extensionality x. des_ifs. des_u; ss.
    }
    { extensionality x. des_ifs. }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. iSplits; ss.
      - iDes. subst. iSplits; ss.
    }
    { ii. des_ifs. iIntros.
      iSplit; iIntros "A".
      - iDes. iSplits; ss.
      - iDes. subst. iSplits; ss.
    }
  Qed.

  Definition mk (X AA AR: Type) (precond: X -> AA -> Any_tgt -> iProp) (postcond: X -> AR -> Any_tgt -> iProp) :=
    @mk_fspec
      X
      (fun x arg_src arg_tgt => (∃ (aa: AA), ⌜arg_src = aa↑⌝ ∧ precond x aa arg_tgt)%I)
      (fun x ret_src ret_tgt => (∃ (ar: AR), ⌜ret_src = ar↑⌝ ∧ postcond x ar ret_tgt)%I)
  .

  Section STB.
    Definition stb := gname -> fspec.
    Class StbSimpl (sb: stb): Prop := {
        stbSimpl:> ∀ fn, FspecSimpl (sb fn);
      }
    .

    Definition stb_equiv := λ (s0 s1: stb), ∀ fn, s0 fn ≡ s1 fn.
    Definition stb_add := λ (s0 s1: stb), λ fn, (s0 fn ** s1 fn).
    Definition stb_append := λ (s0 s1: stb), λ fn, (s0 fn |> s1 fn).
    Definition stb_unit: stb := λ fn, ε.

    Declare Scope stb_scope.
    Delimit Scope stb_scope with stb.
    Bind Scope stb_scope with stb.
    Notation "(≡)" := stb_equiv : stb_scope.
    Infix "≡" := stb_equiv (at level 70) : stb_scope.
    Infix "**" := stb_add (at level 99): stb_scope.
    Notation "(**)" := stb_add : stb_scope.
    Infix "|>" := stb_append (at level 99): stb_scope.
    Notation "(|>)" := stb_append : stb_scope.
    Notation "'ε'" := stb_unit (at level 0): stb_scope.
    Local Open Scope stb_scope.

    Global Program Instance stb_equiv_Equiv: Equivalence stb_equiv.
    Next Obligation.
      ii. refl.
    Qed.
    Next Obligation.
      ii. sym; ss.
    Qed.
    Next Obligation.
      ii. etrans; ss.
    Qed.

    Lemma stb_add_comm: ∀ (f0 f1: stb), (f0 ** f1) ≡ (f1 ** f0).
    Proof.
      ii. eapply fspec_add_comm.
    Qed.
    Lemma stb_add_assoc: ∀ (f0 f1 f2: stb), (((f0 ** f1) ** f2) ≡ (f0 ** (f1 ** f2))).
    Proof.
      ii. eapply fspec_add_assoc.
    Qed.
    Lemma stb_add_unit_l: ∀ `{StbSimpl f0}, (f0) ≡ (ε ** f0).
    Proof.
      ii. unshelve eapply fspec_add_unit_l.
    Qed.
    Lemma stb_add_unit_r: ∀ `{StbSimpl f0}, (f0) ≡ (f0 ** ε).
    Proof.
      ii. unshelve eapply fspec_add_unit_r.
    Qed.
    Lemma stb_append_assoc: ∀ (f0 f1 f2: stb), (((f0 |> f1) |> f2) ≡ (f0 |> (f1 |> f2))).
    Proof.
      ii. eapply fspec_append_assoc.
    Qed.
    Lemma stb_append_unit_l: ∀ f0, (f0) ≡ (ε |> f0).
    Proof.
      ii. unshelve eapply fspec_append_unit_l.
    Qed.
    Lemma stb_append_unit_r: ∀ f0, (f0) ≡ (f0 |> ε).
    Proof.
      ii. unshelve eapply fspec_append_unit_r.
    Qed.
  End STB.

End FSPEC.



Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.

  Definition mput E `{pE -< E} `{eventE -< E} (mr: Σ): itree E unit :=
    st <- trigger PGet;; '(mp, _) <- ((Any.split st)?);;
    trigger (PPut (Any.pair mp mr↑))
  .

  Definition mget E `{pE -< E} `{eventE -< E}: itree E Σ :=
    st <- trigger PGet;; '(_, mr) <- ((Any.split st)?);;
    mr↓?
  .

  Definition pput E `{pE -< E} `{eventE -< E} (mp: Any.t): itree E unit :=
    st <- trigger PGet;; '(_, mr) <- ((Any.split st)?);;
    trigger (PPut (Any.pair mp mr))
  .

  Definition pget E `{pE -< E} `{eventE -< E}: itree E Any.t :=
    st <- trigger PGet;; '(mp, _) <- ((Any.split st)?);;
    Ret mp
  .

End PROOF.

Notation "'update_and_discard' fr0" :=
  ('(rarg, fr1, mr1) <- trigger (Choose (_ * _ * _));;
   mr0 <- mget;;
   guarantee(URA.updatable (fr0 ⋅ mr0) (rarg ⋅ fr1 ⋅ mr1));;;
   mput mr1;;;
   Ret (fr1, rarg)) (at level 60)
.

Section PROOF.
  Context {Σ: GRA.t}.

  Variant condE: Type -> Type :=
    (* | Cassert X (P: X -> iProp): condE X *)
    (* | Cassume X (P: X -> iProp): condE X *)
    | Cassert (P: iProp): condE unit
    | Cassume (P: iProp): condE unit
  .

  Definition handle_condE_tgt `{eventE -< E, pE -< E}: condE ~> stateT Σ (itree E) :=
    fun _ e fr0 =>
      match e with
      (* | Cassert Cond =>  *)
      (*     '(fr1, cres) <- update_and_discard fr0;; *)
      (*     x <- trigger (Choose _);; *)
      (*     guarantee(Cond x cres);;; *)
      (*     Ret (fr1, x) *)
      (* | Cassume Cond => *)
      (*     cres <- trigger (Take Σ);; *)
      (*     mr0 <- mget;; *)
      (*     assume(URA.wf (cres ⋅ fr0 ⋅ mr0));;; *)

      (*     x <- trigger (Take _);; *)
      (*     assume(Cond x cres);;; *)

      (*     Ret (cres ⋅ fr0, x) *)
      | Cassert Cond => 
          '(fr1, cres) <- update_and_discard fr0;;
          guarantee(Cond cres);;;
          Ret (fr1, tt)
      | Cassume Cond =>
          cres <- trigger (Take Σ);;
          mr0 <- mget;;
          assume(URA.wf (cres ⋅ fr0 ⋅ mr0));;;

          assume(Cond cres);;;

          Ret (cres ⋅ fr0, tt)
      end.

  Definition interp_condE_tgt `{eventE -< E, pE -< E}: itree (condE +' E) ~> stateT Σ (itree E) :=
    State.interp_state (case_ handle_condE_tgt pure_state)
  .

  Definition handle_condE_src `{eventE -< E}: condE ~> (itree E) :=
    fun _ _ => triggerUB
  (* match e with *)
  (* | Cassert Cond =>  *)
  (*     Ret (tt) *)
  (* | Cassume Cond => *)
  (*     triggerUB *)
  (* end *)
  (*** We could in theory give above definition, but that breaks symmetry && would break linearity if we want to extend to linear logic later. ***)
  .

  Definition interp_condE_src `{eventE -< E}: itree (condE +' E) ~> (itree E) :=
    interp (case_ handle_condE_src trivial_Handler)
  .

  Definition ASSERT (Cond: Any.t -> Any.t -> iProp) (valv: Any.t): (itree (condE +' Es)) Any.t :=
    valp <- trigger (Choose _);;
    trigger (Cassert (Cond valv valp));;;
    Ret valp
  .

  Definition ASSUME (Cond: Any.t -> Any.t -> iProp) (valp: Any.t): (itree (condE +' Es)) Any.t :=
    valv <- trigger (Take _);;
    trigger (Cassume (Cond valv valp));;;
    Ret valv
  .



  Definition HoareCall (fsp: fspec):
    gname -> Any.t -> (itree (condE +' Es)) Any.t :=
    fun fn varg_src =>
      x <- trigger (Choose fsp.(meta));;
      '(varg_tgt) <- (ASSERT (fsp.(precond) x) varg_src);;
      vret_tgt <- trigger (Call fn varg_tgt);;
      ASSUME (fsp.(postcond) x) vret_tgt
  .

End PROOF.













Notation Es' := (condE +' Es).





Section CANCEL.

  Context `{Σ: GRA.t}.


  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: Any.t -> itree Es' Any.t;
  }
  .

  (*** argument remains the same ***)
  (* Definition mk_simple (mn: string) {X: Type} (P: X -> Any_tgt -> Σ -> ord -> Prop) (Q: X -> Any_tgt -> Σ -> Prop): fspec. *)
  (*   econs. *)
  (*   { apply mn. } *)
  (*   { i. apply (P X0 X2 X3 H /\ X1↑ = X2). } *)
  (*   { i. apply (Q X0 X2 X3 /\ X1↑ = X2). } *)
  (* Unshelve. *)
  (*   apply (list val). *)
  (*   apply (val). *)
  (* Defined. *)


  (*** Don't use these two. Use mk_simple2 instead ***)
  Definition mk_simple {X: Type} (DPQ: X -> (Any_tgt -> iProp) * (Any_tgt -> iProp)): fspec :=
    mk_fspec (fun x y a => (((fst ∘ DPQ) x a: iProp) ∧ ⌜y = a⌝)%I)
             (fun x z a => (((snd ∘ DPQ) x a: iProp) ∧ ⌜z = a⌝)%I)
  .

  Definition mk_irr {X: Type} (DPQ: X -> (Any.t -> iProp) * (Any.t -> iProp)): fspec :=
    mk_fspec (fun x _ a => (((fst ∘ DPQ) x a: iProp))%I)
             (fun x _ a => (((snd ∘ DPQ) x a: iProp))%I)
  .



  Section INTERP.
  (* Variable stb: gname -> option fspec. *)
  (*** TODO: I wanted to use above definiton, but doing so makes defining ms_src hard ***)
  (*** We can fix this by making ModSemL.fnsems to a function, but doing so will change the type of
       ModSemL.add to predicate (t -> t -> t -> Prop), not function.
       - Maybe not. I thought one needed to check uniqueness of gname at the "add",
         but that might not be the case.
         We may define fnsems: string -> option (list val -> itree Es val).
         When adding two ms, it is pointwise addition, and addition of (option A) will yield None when both are Some.
 ***)
  (*** TODO: try above idea; if it fails, document it; and refactor below with alist ***)

  Variable mn: mname.
  Variable stb: gname -> fspec.

  Definition interp_Es'_src: itree Es' ~> itree Es :=
    interp (case_ handle_condE_src trivial_Handler)
  .

  Definition fun_to_src (body: Any.t -> itree Es' Any.t): (Any.t -> itree Es Any_src) :=
    (@interp_Es'_src _) ∘ body
  .



  Definition handle_callE_tgt: callE ~> itree Es' :=
    fun _ '(Call fn varg_src) =>
      HoareCall (stb fn) fn varg_src
  .

  Definition handle_pE_tgt `{eventE -< E, pE -< E}: pE ~> itree E :=
    Eval unfold pput, pget in
      (fun _ e =>
         match e with
         | PPut st => pput st
         | PGet => pget
         end).

  Definition interp_Es'_tgt: itree Es' ~> itree Es' :=
    interp (case_ (bif:=sum1) trivial_Handler
              (case_ (handle_callE_tgt)
                 (case_ handle_pE_tgt trivial_Handler))).

  Definition body_to_tgt (ord_cur: ord)
             {X} (body: X -> itree Es' Any_src): X -> itree Es' Any_src :=
    (@interp_Es'_tgt _) ∘ body.


  Definition HoareFun
             {X: Type}
             (P: X -> Any.t -> Any_tgt -> iProp)
             (Q: X -> Any.t -> Any_tgt -> iProp)
             (body: Any.t -> itree Es' Any.t): Any_tgt -> itree Es' Any_tgt := fun varg_tgt =>
    x <- trigger (Take X);;
    '(varg_src) <- (ASSUME (P x) varg_tgt);;

    '(vret_src) <- interp_Es'_tgt (body varg_src);;

    ASSERT (Q x) vret_src
  .

  Definition fun_to_tgt (fn: string) (body: Any.t -> itree Es' Any.t)
    (varg_tgt: Any_tgt): itree (Es) Any_tgt :=
    let fs := (stb fn) in
    let hf: itree (condE +' Es) Any_tgt :=
      (HoareFun (fs.(precond)) (fs.(postcond)) body varg_tgt) in
    '(_, r) <- (interp_condE_tgt hf ε);;
    (*** If you want linear logic, just ensure fr0 == ε here. ***)
    Ret r
  .

(*** NOTE:
body can execute eventE events.
Notably, this implies it can also execute UB.
With this flexibility, the client code can naturally be included in our "type-checking" framework.
Also, note that body cannot execute "rE" on its own. This is intended.

NOTE: we can allow normal "callE" in the body too, but we need to ensure that it does not call "HoareFun".
If this feature is needed; we can extend it then. At the moment, I will only allow hCallE.
***)


  Definition HoareFunArg
             {X: Type}
             (P: X -> Any.t -> Any_tgt -> iProp):
    Any_tgt -> itree Es' (X * Any.t) :=
    fun varg_tgt =>
      x <- trigger (Take X);;
      '(varg_src) <- (ASSUME (P x) varg_tgt);;
      Ret (x, varg_src)
  .

  Definition HoareFunRet
             {X: Type}
             (Q: X -> Any.t -> Any_tgt -> iProp):
    X -> (Any.t) -> itree Es' Any_tgt :=
    fun x vret_src =>
      (ASSERT (Q x) vret_src)
  .

  Lemma HoareFun_parse
        {X: Type}
        (P: X -> Any.t -> Any_tgt -> iProp)
        (Q: X -> Any.t -> Any_tgt -> iProp)
        (body: Any.t -> itree Es' Any.t)
        (varg_tgt: Any_tgt)
    :
      HoareFun P Q body varg_tgt =
      '(x, varg_src) <- HoareFunArg P varg_tgt;;
      interp_Es'_tgt (body varg_src) >>= (HoareFunRet Q x).
  Proof.
    unfold HoareFun, HoareFunArg, HoareFunRet. grind.
  Qed.

  End INTERP.



  Variable md_tgt: ModL.t.
  Let ms_tgt: ModSemL.t := (ModL.get_modsem md_tgt md_tgt.(ModL.sk)).

  Variable sbtb: alist gname fspecbody.
  Let stb: alist gname fspec := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.














End CANCEL.

End PSEUDOTYPING.





Notation Es' := (condE +' Es).


Module SModSem.
Section SMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems: list (gname * (Any.t → itree Es' Any.t));
    mn: mname;
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  Definition transl (tr: string -> (Any.t → itree Es' Any.t) -> (Any.t -> itree Es Any.t))
    (mst: t -> Any.t) (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, sb) => (fn, tr fn sb)) ms.(fnsems);
    ModSem.mn := ms.(mn);
    ModSem.initial_st := mst ms;
  |}
  .

  Definition to_src (ms: t): ModSem.t := transl (fun _ => fun_to_src) initial_st ms.
  Definition to_tgt (stb: gname -> fspec) (ms: t): ModSem.t :=
    transl (fun_to_tgt stb) (fun ms => Any.pair ms.(initial_st) ms.(initial_mr)↑) ms.

  Definition main (mainbody: (Any.t) -> itree Es' Any.t): t := {|
      fnsems := [("main", mainbody)];
      mn := "Main";
      initial_mr := ε;
      initial_st := tt↑;
    |}
  .

  Definition from (ms: ModSem.t): t := {|
    fnsems := List.map (fun '(fn, f) => (fn, resum_ktr f)) ms.(ModSem.fnsems);
    mn := ms.(ModSem.mn);
    initial_mr := ε;
    initial_st := ms.(ModSem.initial_st);
  |}.

End SMODSEM.
End SModSem.



Module SMod.
Section SMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> SModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl (tr: Sk.t -> string -> (Any.t → itree Es' Any.t) -> (Any.t -> itree Es Any.t))
    (mst: SModSem.t -> Any.t) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => SModSem.transl (tr sk) mst (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  .

  Definition to_src (md: t): Mod.t := transl (fun _ _ => fun_to_src) SModSem.initial_st md.
  Definition to_tgt (stb: Sk.t -> gname -> fspec) (md: t): Mod.t :=
    transl (fun sk => fun_to_tgt (stb sk)) (fun ms => Any.pair ms.(SModSem.initial_st) ms.(SModSem.initial_mr)↑) md.


  (* Definition get_stb (mds: list t): Sk.t -> alist gname fspec := *)
  (*   fun sk => map (map_snd fsb_fspec) (flat_map (SModSem.fnsems ∘ (flip get_modsem sk)) mds). *)

  Definition get_sk (mds: list t): Sk.t :=
    Sk.sort (fold_right Sk.add Sk.unit (List.map sk mds)).

  Definition get_initial_mrs (mds: list t): Sk.t -> Σ :=
    fun sk => fold_left (⋅) (List.map (SModSem.initial_mr ∘ (flip get_modsem sk)) mds) ε.


  (* Definition transl (tr: SModSem.t -> ModSem.t) (md: t): Mod.t := {| *)
  (*   Mod.get_modsem := (SModSem.transl tr) ∘ md.(get_modsem); *)
  (*   Mod.sk := md.(sk); *)
  (* |} *)
  (* . *)

  (* Definition to_src (md: t): Mod.t := transl SModSem.to_src md. *)
  (* Definition to_mid (md: t): Mod.t := transl SModSem.to_mid md. *)
  (* Definition to_tgt (stb: list (gname * fspec)) (md: t): Mod.t := transl (SModSem.to_tgt stb) md. *)
  Lemma to_src_comm: forall sk smd,
      (SModSem.to_src) (get_modsem smd sk) = (to_src smd).(Mod.get_modsem) sk.
  Proof. refl. Qed.
  Lemma to_tgt_comm: forall sk stb smd,
      (SModSem.to_tgt (stb sk)) (get_modsem smd sk) = (to_tgt stb smd).(Mod.get_modsem) sk.
  Proof. refl. Qed.










  (* Definition l_bind A B (x: list A) (f: A -> list B): list B := List.flat_map f x. *)
  (* Definition l_ret A (a: A): list A := [a]. *)

  Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Lemma unconcat
        A (xs: list A)
    :
      List.concat (List.map (fun x => [x]) xs) = xs
  .
  Proof.
    induction xs; ii; ss. f_equal; ss.
  Qed.

  Lemma red_do_ret A B (xs: list A) (f: A -> B)
    :
      (do x <- xs; ret (f x)) = List.map f xs
  .
  Proof.
    rewrite flat_map_concat_map.
    erewrite <- List.map_map with (f:=f) (g:=ret).
    rewrite unconcat. ss.
  Qed.

  Lemma red_do_ret2 A0 A1 B (xs: list (A0 * A1)) (f: A0 -> A1 -> B)
    :
      (do '(x0, x1) <- xs; ret (f x0 x1)) = List.map (fun '(x0, x1) => f x0 x1) xs
  .
  Proof.
    induction xs; ss. rewrite IHxs. destruct a; ss.
  Qed.

  Lemma flat_map_assoc
        A B C
        (f: A -> list B)
        (g: B -> list C)
        (xs: list A)
    :
      (do y <- (do x <- xs; f x); g y) =
      (do x <- xs; do y <- (f x); g y)
  .
  Proof.
    induction xs; ii; ss.
    rewrite ! flat_map_concat_map in *. rewrite ! map_app. rewrite ! concat_app. f_equal; ss.
  Qed.













  Local Opaque Mod.add_list.

  Lemma transl_sk
        tr0 mr0 mds
    :
      <<SK: ModL.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) = fold_right Sk.add Sk.unit (List.map sk mds)>>
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. ss. r. f_equal. ss.
  Qed.

  Lemma transl_sk_stable
        tr0 tr1 mr0 mr1 mds
    :
      ModL.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) =
      ModL.sk (Mod.add_list (List.map (transl tr1 mr1) mds))
  .
  Proof. rewrite ! transl_sk. ss. Qed.

  Definition load_fnsems (sk: Sk.t) (mds: list t)
    (tr0: string -> (Any.t -> itree Es' Any.t) -> Any.t -> itree Es Any.t) :=
    do md <- mds;
    let ms := (get_modsem md sk) in
      (do '(fn, fsb) <- ms.(SModSem.fnsems);
       let fsem := tr0 fn fsb in
       ret (fn, transl_all (T:=_) ms.(SModSem.mn) ∘ fsem))
  .

  Let transl_fnsems_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSemL.fnsems (ModL.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_fnsems sk mds (tr0 sk))
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. cbn. f_equal; ss.
    rewrite ! List.map_map.

    rewrite flat_map_concat_map.
    replace
      (λ _x : string * (Any.t → itree Es' Any.t),
          let (fn, fsb) := _x in
          [(fn, transl_all (SModSem.mn (get_modsem a sk)) (T:=Any.t) ∘ tr0 sk fn fsb)])
      with
      (ret ∘ (λ _x : string * (Any.t → itree Es' Any.t),
          let (fn, fsb) := _x in
          (fn, transl_all (SModSem.mn (get_modsem a sk)) (T:=Any.t) ∘ tr0 sk fn fsb)));
       cycle 1.
    { apply func_ext. i. des_ifs. }
    erewrite <- List.map_map with (g:=ret).
    rewrite unconcat.
    apply map_ext. ii. des_ifs.
  Qed.

  Lemma transl_fnsems
        tr0 mr0 mds
    :
      (ModSemL.fnsems (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_fnsems (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds (tr0 (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds)))))
  .
  Proof.
    unfold ModL.enclose.
    rewrite transl_fnsems_aux. do 2 f_equal. rewrite transl_sk. ss.
    rewrite transl_sk. auto.
  Qed.

  (* Lemma transl_fnsems_stable *)
  (*       tr0 tr1 mr0 mr1 mds *)
  (*   : *)
  (*     List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSemL.fnsems) = *)
  (*     List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSemL.fnsems) *)
  (* . *)
  (* Proof. *)
  (*   rewrite ! transl_fnsems. *)
  (*   unfold load_fnsems. *)
  (*   rewrite <- ! red_do_ret. *)
  (*   rewrite ! flat_map_assoc. eapply flat_map_ext. i. *)
  (*   rewrite ! flat_map_assoc. eapply flat_map_ext. i. *)
  (*   des_ifs. *)
  (* Qed. *)




  Definition load_initial_mrs {A} (sk: Sk.t) (mds: list t) (mr0: SModSem.t -> A): list (string * A) :=
    do md <- mds;
    let ms := (get_modsem md sk) in
    ret (ms.(SModSem.mn), mr0 ms)
  .

  Let transl_initial_mrs_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSemL.initial_mrs (ModL.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_initial_mrs sk mds mr0)
  .
  Proof.
    induction mds; ii; ss.
    rewrite Mod.add_list_cons. cbn. f_equal; ss.
  Qed.

  Lemma transl_initial_mrs
        tr0 mr0 mds
    :
      (ModSemL.initial_mrs (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_initial_mrs (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds mr0)
  .
  Proof.
    unfold ModL.enclose.
    rewrite transl_initial_mrs_aux. do 2 f_equal. rewrite transl_sk. ss.
  Qed.

  Lemma transl_stable_mn
        tr0 tr1 mr0 mr1 mds
    :
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSemL.initial_mrs) =
      List.map fst (ModL.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSemL.initial_mrs)
  .
  Proof.
    rewrite ! transl_initial_mrs. unfold load_initial_mrs. rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i. ss.
  Qed.

  Definition main (mainbody: (Any.t) -> itree Es' Any.t): t := {|
    get_modsem := fun _ => (SModSem.main mainbody);
    sk := Sk.unit;
  |}
  .

  Definition from (md: Mod.t): t := {|
    get_modsem := SModSem.from ∘ md.(Mod.get_modsem);
    sk := md.(Mod.sk);
  |}.

End SMOD.
End SMod.















  Hint Resolve Ord.lt_le_lt Ord.le_lt_lt OrdArith.lt_add_r OrdArith.le_add_l
       OrdArith.le_add_r Ord.lt_le
       Ord.lt_S
       Ord.S_lt
       Ord.S_supremum
       Ord.S_pos
    : ord.
  Hint Resolve Ord.le_trans Ord.lt_trans: ord_trans.
  Hint Resolve OrdArith.add_base_l OrdArith.add_base_r: ord_proj.

  Global Opaque EventsL.interp_Es.






  Require Import Red.

  Ltac interp_red := erewrite interp_vis ||
                              erewrite interp_ret ||
                              erewrite interp_tau ||
                              erewrite interp_trigger ||
                              erewrite interp_bind.

  (* TODO: remove it *)
  Ltac interp_red2 := rewrite interp_vis ||
                              rewrite interp_ret ||
                              rewrite interp_tau ||
                              rewrite interp_trigger ||
                              rewrite interp_bind.

  Ltac _red_itree f :=
    match goal with
    | [ |- ?itr >>= _ = _] =>
      match itr with
      | _ >>= _ =>
        instantiate (f:=_continue); apply bind_bind; fail
      | Tau _ =>
        instantiate (f:=_break); apply bind_tau; fail
      | Ret _ =>
        instantiate (f:=_continue); apply bind_ret_l; fail
      | _ =>
        fail
      end
    | _ => fail
    end.



Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_tgt_bind
      (R S: Type)
      (s : itree _ R) (k : R -> itree _ S)
      stb
  :
    (interp_Es'_tgt stb (s >>= k))
    =
    x <- interp_Es'_tgt stb s;; interp_Es'_tgt stb (k x).
Proof.
  unfold interp_Es'_tgt in *. grind.
Qed.

Lemma interp_tgt_tau stb
      (U: Type)
      (t : itree _ U)
  :
    (interp_Es'_tgt stb (Tau t))
    =
    (Tau (interp_Es'_tgt stb t)).
Proof.
  unfold interp_Es'_tgt in *. grind.
Qed.

Lemma interp_tgt_ret stb
      (U: Type)
      (t: U)
  :
    (interp_Es'_tgt stb (Ret t))
    =
    Ret (t).
Proof.
  unfold interp_Es'_tgt in *. grind.
Qed.

Lemma interp_tgt_triggerp stb
      (R: Type)
      (i: pE R)
  :
    (interp_Es'_tgt stb (trigger i))
    =
    (handle_pE_tgt i >>= (fun r => tau;; Ret (r))).
Proof.
  unfold interp_Es'_tgt. rewrite interp_trigger. cbn. grind.
Qed.

Lemma interp_tgt_triggere stb
      (R: Type)
      (i: eventE R)
  :
    (interp_Es'_tgt stb (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret (r))).
Proof.
  unfold interp_Es'_tgt. rewrite interp_trigger. cbn. grind.
Qed.

Lemma interp_tgt_triggerc stb
      (R: Type)
      (i: condE R)
  :
    (interp_Es'_tgt stb (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret (r))).
Proof.
  unfold interp_Es'_tgt. rewrite interp_trigger. cbn. grind.
Qed.

Lemma interp_tgt_hcall stb
      (R: Type)
      (i: callE R)
  :
    (interp_Es'_tgt stb (trigger i))
    =
    (handle_callE_tgt stb i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_Es'_tgt in *. rewrite interp_trigger. cbn. auto.
Qed.

Lemma interp_tgt_triggerUB stb
      (R: Type)
  :
    (interp_Es'_tgt stb (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_Es'_tgt, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_tgt_triggerNB stb
      (R: Type)
  :
    (interp_Es'_tgt stb (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_Es'_tgt, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_tgt_unwrapU stb
      (R: Type)
      (i: option R)
  :
    (interp_Es'_tgt stb (@unwrapU _ _ _ i))
    =
    r <- (unwrapU i);; Ret (r).
Proof.
  unfold unwrapU in *. des_ifs.
  { unfold interp_Es'_tgt. grind. }
  { rewrite interp_tgt_triggerUB. grind. }
Qed.

Lemma interp_tgt_unwrapN stb
      (R: Type)
      (i: option R)
  :
    (interp_Es'_tgt stb (@unwrapN _ _ _ i))
    =
    r <- (unwrapN i);; Ret (r).
Proof.
  unfold unwrapN in *. des_ifs.
  { unfold interp_Es'_tgt. grind. }
  { rewrite interp_tgt_triggerNB. grind. }
Qed.

Lemma interp_tgt_assume stb
      P
  :
    (interp_Es'_tgt stb (assume P))
    =
    (assume P;;; tau;; Ret (tt))
.
Proof.
  unfold assume. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_guarantee stb
      P
  :
    (interp_Es'_tgt stb (guarantee P))
    =
    (guarantee P;;; tau;; Ret (tt)).
Proof.
  unfold guarantee. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_ext stb
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_Es'_tgt stb itr0)
    =
    (interp_Es'_tgt stb itr1)
.
Proof. subst; et. Qed.

Global Program Instance interp_Es'_tgt_rdb: red_database (mk_box (@interp_Es'_tgt)) :=
  mk_rdb
    0
    (mk_box interp_tgt_bind)
    (mk_box interp_tgt_tau)
    (mk_box interp_tgt_ret)
    (mk_box interp_tgt_hcall)
    (mk_box interp_tgt_triggere)
    (mk_box interp_tgt_triggerp)
    (mk_box interp_tgt_triggerc)
    (mk_box True)
    (mk_box interp_tgt_triggerUB)
    (mk_box interp_tgt_triggerNB)
    (mk_box interp_tgt_unwrapU)
    (mk_box interp_tgt_unwrapN)
    (mk_box interp_tgt_assume)
    (mk_box interp_tgt_guarantee)
    (mk_box interp_tgt_ext)
.

End AUX.



Section AUX.

Context `{Σ: GRA.t}.
Context `{eventE -< E, pE -< E, callE -< E}.

Lemma interp_condE_tgt_bind
      (R S: Type)
      (s : itree _ R) (k : R -> itree _ S)
      fr0
  :
    (interp_condE_tgt (s >>= k) fr0)
    =
    '(fr1, x) <- interp_condE_tgt s fr0;; interp_condE_tgt (k x) fr1.
Proof.
  unfold interp_condE_tgt in *. rewrite interp_state_bind. grind. des_ifs.
Qed.

Lemma interp_condE_tgt_tau fr0
      (U: Type)
      (t : itree _ U)
  :
    (interp_condE_tgt (Tau t) fr0)
    =
    (Tau (interp_condE_tgt t fr0)).
Proof.
  unfold interp_condE_tgt in *. grind.
Qed.

Lemma interp_condE_tgt_ret fr0
      (U: Type)
      (t: U)
  :
    (interp_condE_tgt (Ret t) fr0)
    =
    Ret (fr0, t).
Proof.
  unfold interp_condE_tgt in *. grind.
Qed.

Lemma interp_condE_tgt_triggerp fr0
      (R: Type)
      (i: pE R)
  :
    (interp_condE_tgt (trigger i) fr0)
    =
    x <- trigger i;; tau;; Ret (fr0, x).
Proof.
  unfold interp_condE_tgt. rewrite interp_state_trigger. cbn. unfold pure_state. grind.
Qed.

Lemma interp_condE_tgt_triggere fr0
      (R: Type)
      (i: eventE R)
  :
    (interp_condE_tgt (trigger i) fr0)
    =
    x <- trigger i;; tau;; Ret (fr0, x).
Proof.
  unfold interp_condE_tgt. rewrite interp_state_trigger. cbn. unfold pure_state. grind.
Qed.

Lemma interp_condE_tgt_triggerc fr0
      (R: Type)
      (i: condE R)
  :
    (interp_condE_tgt (trigger i) fr0)
    =
    x <- (handle_condE_tgt i fr0);; tau;; Ret x.
Proof.
  unfold interp_condE_tgt. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_condE_tgt_call fr0
      (R: Type)
      (i: callE R)
  :
    (interp_condE_tgt (trigger i) fr0)
    =
    x <- trigger i;; tau;; Ret (fr0, x).
Proof.
  unfold interp_condE_tgt in *. rewrite interp_state_trigger. cbn. unfold pure_state. grind.
Qed.

Lemma interp_condE_tgt_triggerUB fr0
      (R: Type)
  :
    (interp_condE_tgt (triggerUB) fr0)
    =
    triggerUB (A:=Σ * R).
Proof.
  unfold triggerUB. rewrite interp_condE_tgt_bind. grind.
  rewrite interp_condE_tgt_triggere. grind.
Qed.

Lemma interp_condE_tgt_triggerNB fr0
      (R: Type)
  :
    (interp_condE_tgt (triggerNB) fr0)
    =
    triggerNB (A:=Σ*R).
Proof.
  unfold triggerNB. rewrite interp_condE_tgt_bind. grind.
  rewrite interp_condE_tgt_triggere. grind.
Qed.

Lemma interp_condE_tgt_unwrapU fr0
      (R: Type)
      (i: option R)
  :
    (interp_condE_tgt (@unwrapU _ _ _ i) fr0)
    =
    r <- (unwrapU i);; Ret (fr0, r).
Proof.
  unfold unwrapU in *. des_ifs.
  { unfold interp_condE_tgt. grind. }
  { rewrite interp_condE_tgt_triggerUB. unfold triggerUB. grind. }
Qed.

Lemma interp_condE_tgt_unwrapN fr0
      (R: Type)
      (i: option R)
  :
    (interp_condE_tgt (@unwrapN _ _ _ i) fr0)
    =
    r <- (unwrapN i);; Ret (fr0, r).
Proof.
  unfold unwrapN in *. des_ifs.
  { unfold interp_condE_tgt. grind. }
  { rewrite interp_condE_tgt_triggerNB. unfold triggerNB. grind. }
Qed.

Lemma interp_condE_tgt_assume fr0
      P
  :
    (interp_condE_tgt (assume P) fr0)
    =
    (assume P;;; tau;; Ret (fr0, tt))
.
Proof.
  unfold assume. rewrite interp_condE_tgt_bind. rewrite interp_condE_tgt_triggere. grind. eapply interp_condE_tgt_ret.
Qed.

Lemma interp_condE_tgt_guarantee fr0
      P
  :
    (interp_condE_tgt (guarantee P) fr0)
    =
    (guarantee P;;; tau;; Ret (fr0, tt)).
Proof.
  unfold guarantee. rewrite interp_condE_tgt_bind. rewrite interp_condE_tgt_triggere. grind. eapply interp_condE_tgt_ret.
Qed.

Lemma interp_condE_tgt_ext fr0
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_condE_tgt itr0 fr0)
    =
    (interp_condE_tgt itr1 fr0)
.
Proof. subst; et. Qed.

Global Program Instance interp_condE_tgt_rdb: red_database (mk_box (interp_condE_tgt)) :=
  mk_rdb
    1
    (mk_box interp_condE_tgt_bind)
    (mk_box interp_condE_tgt_tau)
    (mk_box interp_condE_tgt_ret)
    (mk_box interp_condE_tgt_call)
    (mk_box interp_condE_tgt_triggere)
    (mk_box interp_condE_tgt_triggerp)
    (mk_box interp_condE_tgt_triggerc)
    (mk_box True)
    (mk_box interp_condE_tgt_triggerUB)
    (mk_box interp_condE_tgt_triggerNB)
    (mk_box interp_condE_tgt_unwrapU)
    (mk_box interp_condE_tgt_unwrapN)
    (mk_box interp_condE_tgt_assume)
    (mk_box interp_condE_tgt_guarantee)
    (mk_box interp_condE_tgt_ext)
.

End AUX.








Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_src_bind
      (R S: Type)
      (s : itree _ R) (k : R -> itree _ S)
  :
    (interp_Es'_src (s >>= k))
    =
    ((interp_Es'_src s) >>= (fun r => interp_Es'_src (k r))).
Proof.
  unfold interp_Es'_src in *. grind.
Qed.

Lemma interp_src_tau
      (U: Type)
      (t : itree _ U)
  :
    (interp_Es'_src (Tau t))
    =
    (Tau (interp_Es'_src t)).
Proof.
  unfold interp_Es'_src in *. grind.
Qed.

Lemma interp_src_ret
      (U: Type)
      (t: U)
  :
    ((interp_Es'_src (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_Es'_src in *. grind.
Qed.

Lemma interp_src_triggerp
      (R: Type)
      (i: pE R)
  :
    (interp_Es'_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_Es'_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggere
      (R: Type)
      (i: eventE R)
  :
    (interp_Es'_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_Es'_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggerc
      (R: Type)
      (i: condE R)
  :
    (interp_Es'_src (trigger i))
    =
    x <- handle_condE_src i;; tau;; Ret x.
Proof.
  unfold interp_Es'_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_call
      (R: Type)
      (i: callE R)
  :
    (interp_Es'_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_Es'_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggerUB
      (R: Type)
  :
    (interp_Es'_src (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_Es'_src, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_triggerNB
      (R: Type)
  :
    (interp_Es'_src (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_Es'_src, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_unwrapU
      (R: Type)
      (i: option R)
  :
    (interp_Es'_src (@unwrapU _ _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_Es'_src, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_src_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_src_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_src_unwrapN
      (R: Type)
      (i: option R)
  :
    (interp_Es'_src (@unwrapN _ _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_Es'_src, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_src_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_src_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_src_assume
      P
  :
    (interp_Es'_src (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_guarantee
      P
  :
    (interp_Es'_src (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_Es'_src itr0)
    =
    (interp_Es'_src itr1)
.
Proof. subst; et. Qed.

Global Program Instance interp_Es'_src_rdb: red_database (mk_box (@interp_Es'_src)) :=
  mk_rdb
    0
    (mk_box interp_src_bind)
    (mk_box interp_src_tau)
    (mk_box interp_src_ret)
    (mk_box interp_src_call)
    (mk_box interp_src_triggere)
    (mk_box interp_src_triggerp)
    (mk_box interp_src_triggerc)
    (mk_box True)
    (mk_box interp_src_triggerUB)
    (mk_box interp_src_triggerNB)
    (mk_box interp_src_unwrapU)
    (mk_box interp_src_unwrapN)
    (mk_box interp_src_assume)
    (mk_box interp_src_guarantee)
    (mk_box interp_src_ext)
.

End AUX.




(* Section AUX. *)

(* Context `{Σ: GRA.t}. *)
(* (* itree reduction *) *)
(* Lemma interp_hEs_tgt_bind *)
(*       (R S: Type) *)
(*       (s : itree _ R) (k : R -> itree _ S) *)
(*   : *)
(*     (interp_hEs_tgt (s >>= k)) *)
(*     = *)
(*     ((interp_hEs_tgt s) >>= (fun r => interp_hEs_tgt (k r))). *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_tau *)
(*       (U: Type) *)
(*       (t : itree _ U) *)
(*   : *)
(*     (interp_hEs_tgt (Tau t)) *)
(*     = *)
(*     (Tau (interp_hEs_tgt t)). *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_ret *)
(*       (U: Type) *)
(*       (t: U) *)
(*   : *)
(*     ((interp_hEs_tgt (Ret t))) *)
(*     = *)
(*     Ret t. *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_triggerp *)
(*       (R: Type) *)
(*       (i: pE R) *)
(*   : *)
(*     (interp_hEs_tgt (trigger i)) *)
(*     = *)
(*     (trigger i >>= (fun r => tau;; Ret r)). *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. *)
(*   repeat rewrite interp_trigger. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_triggere *)
(*       (R: Type) *)
(*       (i: eventE R) *)
(*   : *)
(*     (interp_hEs_tgt (trigger i)) *)
(*     = *)
(*     (trigger i >>= (fun r => tau;; Ret r)). *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. *)
(*   repeat rewrite interp_trigger. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_triggerc *)
(*       (R: Type) *)
(*       (i: condE R) *)
(*   : *)
(*     (interp_hEs_tgt (trigger i)) *)
(*     = *)
(*     (trigger i >>= (fun r => tau;; Ret r)). *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. *)
(*   repeat rewrite interp_trigger. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_call *)
(*       (R: Type) *)
(*       (i: callE R) *)
(*   : *)
(*     (interp_hEs_tgt (trigger i)) *)
(*     = *)
(*     (handle_callE_hEs i >>= (fun r => tau;; Ret r)). *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. *)
(*   repeat rewrite interp_trigger. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_hapc *)
(*       (R: Type) *)
(*       (i: hAPCE R) *)
(*   : *)
(*     (interp_hEs_tgt (trigger i)) *)
(*     = *)
(*     ((handle_hAPCE_tgt i) >>= (fun r => tau;; Ret r)). *)
(* Proof. *)
(*   unfold interp_hEs_tgt in *. *)
(*   repeat rewrite interp_trigger. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_triggerUB *)
(*       (R: Type) *)
(*   : *)
(*     (interp_hEs_tgt (triggerUB)) *)
(*     = *)
(*     triggerUB (A:=R). *)
(* Proof. *)
(*   unfold interp_hEs_tgt, triggerUB in *. rewrite unfold_interp. cbn. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_triggerNB *)
(*       (R: Type) *)
(*   : *)
(*     (interp_hEs_tgt (triggerNB)) *)
(*     = *)
(*     triggerNB (A:=R). *)
(* Proof. *)
(*   unfold interp_hEs_tgt, triggerNB in *. rewrite unfold_interp. cbn. grind. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_unwrapU *)
(*       (R: Type) *)
(*       (i: option R) *)
(*   : *)
(*     (interp_hEs_tgt (@unwrapU hEs _ _ i)) *)
(*     = *)
(*     (unwrapU i). *)
(* Proof. *)
(*   unfold interp_hEs_tgt, unwrapU in *. des_ifs. *)
(*   { etrans. *)
(*     { eapply interp_hEs_tgt_ret. } *)
(*     { grind. } *)
(*   } *)
(*   { etrans. *)
(*     { eapply interp_hEs_tgt_triggerUB. } *)
(*     { unfold triggerUB. grind. } *)
(*   } *)
(* Qed. *)

(* Lemma interp_hEs_tgt_unwrapN *)
(*       (R: Type) *)
(*       (i: option R) *)
(*   : *)
(*     (interp_hEs_tgt (@unwrapN hEs _ _ i)) *)
(*     = *)
(*     (unwrapN i). *)
(* Proof. *)
(*   unfold interp_hEs_tgt, unwrapN in *. des_ifs. *)
(*   { etrans. *)
(*     { eapply interp_hEs_tgt_ret. } *)
(*     { grind. } *)
(*   } *)
(*   { etrans. *)
(*     { eapply interp_hEs_tgt_triggerNB. } *)
(*     { unfold triggerNB. grind. } *)
(*   } *)
(* Qed. *)

(* Lemma interp_hEs_tgt_assume *)
(*       P *)
(*   : *)
(*     (interp_hEs_tgt (assume P)) *)
(*     = *)
(*     (assume P;;; tau;; Ret tt) *)
(* . *)
(* Proof. *)
(*   unfold assume. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_guarantee *)
(*       P *)
(*   : *)
(*     (interp_hEs_tgt (guarantee P)) *)
(*     = *)
(*     (guarantee P;;; tau;; Ret tt). *)
(* Proof. *)
(*   unfold guarantee. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret. *)
(* Qed. *)

(* Lemma interp_hEs_tgt_ext *)
(*       R (itr0 itr1: itree _ R) *)
(*       (EQ: itr0 = itr1) *)
(*   : *)
(*     (interp_hEs_tgt itr0) *)
(*     = *)
(*     (interp_hEs_tgt itr1) *)
(* . *)
(* Proof. subst; et. Qed. *)

(* Global Program Instance interp_hEs_tgt_rdb: red_database (mk_box (@interp_hEs_tgt)) := *)
(*   mk_rdb *)
(*     0 *)
(*     (mk_box interp_hEs_tgt_bind) *)
(*     (mk_box interp_hEs_tgt_tau) *)
(*     (mk_box interp_hEs_tgt_ret) *)
(*     (mk_box interp_hEs_tgt_call) *)
(*     (mk_box interp_hEs_tgt_triggere) *)
(*     (mk_box interp_hEs_tgt_triggerp) *)
(*     (mk_box interp_hEs_tgt_triggerc) *)
(*     (mk_box interp_hEs_tgt_hapc) *)
(*     (mk_box interp_hEs_tgt_triggerUB) *)
(*     (mk_box interp_hEs_tgt_triggerNB) *)
(*     (mk_box interp_hEs_tgt_unwrapU) *)
(*     (mk_box interp_hEs_tgt_unwrapN) *)
(*     (mk_box interp_hEs_tgt_assume) *)
(*     (mk_box interp_hEs_tgt_guarantee) *)
(*     (mk_box interp_hEs_tgt_ext) *)
(* . *)

(* End AUX. *)




(*** TODO: move to ITreeLib ***)
Lemma bind_eta E X Y itr0 itr1 (ktr: ktree E X Y): itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr. i; subst; refl. Qed.

Ltac ired_l := try (prw _red_gen 2 0).
Ltac ired_r := try (prw _red_gen 1 0).

Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).
  Ltac Esred :=
            try rewrite ! EventsL.interp_Es_pE;
            try rewrite ! EventsL.interp_Es_eventE; try rewrite ! EventsL.interp_Es_callE;
            try rewrite ! EventsL.interp_Es_triggerNB; try rewrite ! EventsL.interp_Es_triggerUB (*** igo ***).
  (*** step and some post-processing ***)
  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso

    (*** assume/guarantee ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (gstep; econs; eauto; try (by eapply OrdArith.lt_from_nat; ss);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .
  Ltac steps := repeat (mred; try _step; des_ifs_safe).
  Ltac seal_left :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_src
    end.
  Ltac seal_right :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_tgt
    end.
  Ltac unseal_left :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (@Seal.sealing _ _ ?i_src) ?i_tgt ] => unseal i_src
    end.
  Ltac unseal_right :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src (@Seal.sealing _ _ ?i_tgt) ] => unseal i_tgt
    end.
  Ltac force_l := seal_right; _step; unseal_right.
  Ltac force_r := seal_left; _step; unseal_left.
  (* Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|]. *)

  From ExtLib Require Import
       Data.Map.FMapAList.

  Hint Resolve cpn3_wcompat: paco.
  Ltac init :=
    split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
    ginit; []; unfold alist_add, alist_remove; ss;
    unfold fun_to_tgt, cfunN; ss.

  Declare Scope fspec_scope.
  Delimit Scope fspec_scope with fspec.
  Bind Scope fspec_scope with fspec.
  Notation "(≡)" := fspec_equiv : fspec_scope.
  Infix "≡" := fspec_equiv (at level 70) : fspec_scope.
  Notation "(**)" := fspec_add : fspec_scope.
  Infix "**" := fspec_add (at level 99): fspec_scope.
  Notation "(|>)" := fspec_append : fspec_scope.
  Infix "|>" := fspec_append (at level 99): fspec_scope.
  Notation "'ε'" := fspec_trivial (at level 0): fspec_scope.
  Local Open Scope fspec_scope.

  Declare Scope stb_scope.
  Delimit Scope stb_scope with stb.
  Bind Scope stb_scope with stb.
  Notation "(≡)" := stb_equiv : stb_scope.
  Infix "≡" := stb_equiv (at level 70) : stb_scope.
  Notation "(**)" := stb_add : stb_scope.
  Infix "**" := stb_add (at level 99): stb_scope.
  Notation "(|>)" := stb_append : stb_scope.
  Infix "|>" := stb_append (at level 99): stb_scope.
  Notation "'ε'" := stb_unit (at level 0): stb_scope.
  Local Open Scope stb_scope.
