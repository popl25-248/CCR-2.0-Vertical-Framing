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
Require Import Mem1 Invariant.

Set Implicit Arguments.


(* Instance MapRA0: URA.t := Excl.t unit. *)
Instance MapRA1: URA.t := URA.prod (Excl.t unit) (Auth.t (Z ==> (Excl.t Z)))%ra.

Definition map_points_to_r (k: Z) (v: Z): @URA.car MapRA1 :=
  (Excl.unit, Auth.white ((fun n => if Z.eq_dec n k then Excl.just v else Excl.unit): @URA.car (Z ==> (Excl.t Z))%ra)).

Definition map_points_to `{@GRA.inG MapRA1 Σ} (k: Z) (v: Z): iProp :=
  OwnM (map_points_to_r k v).

Definition pending0 `{@GRA.inG MapRA1 Σ}: iProp :=
  OwnM ((Excl.just tt, ε): MapRA1).

(* Definition pending1 `{@GRA.inG MapRA1 Σ}: iProp := *)
(*   OwnM (Excl.just tt, URA.unit: @URA.car (Auth.t (Z ==> (Excl.t Z)))%ra). *)

(* Definition pending `{@GRA.inG MapRA0 Σ} `{@GRA.inG MapRA1 Σ}: iProp := *)
(*   pending0 ** pending1. *)

Fixpoint initial_points_tos `{@GRA.inG MapRA1 Σ} (sz: nat): iProp :=
  match sz with
  | 0 => True%I
  | S sz' => initial_points_tos sz' ** map_points_to sz' 0
  end.

Section SPECS.
  Context `{@GRA.inG MapRA1 Σ}.

  Definition init_specM: fspec :=
    (mk_simple (fun (_: unit) =>
                  ((fun varg => (∃ (sz :nat), (⌜varg = ([Vint sz]: list val)↑⌝)
                                  ** (⌜(8 * (Z.of_nat sz) < modulus_64%Z)%Z⌝)
                                  ** pending0)%I),
                    (fun vret => True%I)))).
  Definition init_specS: fspec :=
    (mk_simple (fun (sz: nat) =>
                  ((fun varg => (⌜varg = ([Vint sz]: list val)↑⌝)
                                  ** (⌜(8 * (Z.of_nat sz) < modulus_64%Z)%Z⌝)),
                    (fun vret => ⌜vret = Vundef↑⌝ ** initial_points_tos sz)))).
  Definition init_spec: fspec :=
    (mk_simple (fun (sz: nat) =>
                  ((fun varg => (⌜varg = ([Vint sz]: list val)↑⌝)
                                  ** (⌜(8 * (Z.of_nat sz) < modulus_64%Z)%Z⌝)
                                  ** pending0),
                    (fun vret => ⌜vret = Vundef↑⌝ ** initial_points_tos sz)))).

  Definition get_specM: fspec := (fspec_trivial).
  Definition get_specS: fspec :=
      (mk_simple (fun '(k, v) =>
                    (
                      (fun varg => (⌜varg = ([Vint k])↑⌝)
                                     ** (map_points_to k v)),
                      (fun vret => ⌜vret = (Vint v)↑⌝ ** map_points_to k v)))).
  Definition get_spec: fspec := get_specS.

  Definition set_specM: fspec := (fspec_trivial).
  Definition set_specS: fspec :=
      (mk_simple (fun '(k, w, v) =>
                    (
                      (fun varg => (⌜varg = ([Vint k; Vint v])↑⌝)
                                     ** (map_points_to k w)),
                      (fun vret => ⌜vret = Vundef↑⌝ ** map_points_to k v)))).
  Definition set_spec: fspec := set_specS.

  Definition MapStb: alist gname fspec :=
    Seal.sealing "stb" [("init", init_spec); ("get", get_spec); ("set", set_spec)].

  Definition MapStbM: alist gname fspec :=
    Seal.sealing "stb" [("init", init_specM); ("get", get_specM); ("set", set_specM)].

  Definition Conds :=
    fun str =>
      match alist_find str ([("init", init_specM); ("set", set_specM); ("get", get_specM)])
      with
      | Some res => res
      | _ => ε%fspec
      end.

  Definition CondsB :=
    fun str =>
      match alist_find str ([("init", init_specS); ("set", set_specS); ("get", get_specS)])
      with
      | Some res => res
      | _ => ε%fspec
      end.

  Definition CondsC :=
    fun str =>
      match alist_find str ([("init", init_spec); ("set", set_spec); ("get", get_spec)])
      with
      | Some res => res
      | _ => ε%fspec
      end.

  Theorem Conds_app: ((Conds |> CondsB) ≡ CondsC)%stb.
  Proof.
    ii.
    unfold CondsC. ss. des_ifs; ss; unfold Conds, stb_append, CondsB; ss; des_ifs.
    - rr. ss. exists (fun '(_, a) => a). exists (fun a => (tt, a)).
      esplits; ss.
      { extensionality x. des_ifs. ss. des_u; ss. }
      { i. des_ifs. des_u.
        iSplit.
        - iIntros; iDes; subst; iFrame; ss.
        - iIntros; iDes; subst. iDestruct "H" as "%A". iFrame; ss. iSplits; ss.
      }
      { i. des_ifs. des_u.
        iSplit.
        - iIntros; iDes; subst. iDestruct "H" as "%A". iFrame; ss.
        - iIntros; iDes; subst; iFrame; ss. iSplits; ss.
      }
    - unfold set_specM. rewrite <- fspec_append_unit_l. refl.
    - unfold get_specM. rewrite <- fspec_append_unit_l. refl.
    - rewrite <- fspec_append_unit_l. refl.
  Qed.
End SPECS.
Global Hint Unfold MapStb MapStbM: stb.



Definition set `{Dec K} V (k: K) (v: V) (f: K -> V): K -> V := fun k0 => if dec k k0 then v else f k0.



Section PROOF.
  Context `{Σ: GRA.t}.

  Lemma Own_unit
    :
      bi_entails True%I (Own ε)
  .
  Proof.
    red. uipropall. ii. rr. esplits; et. rewrite URA.unit_idl. refl.
  Qed.

  Context `{@GRA.inG M Σ}.

  Lemma embed_unit
    :
      (GRA.embed ε) = ε
  .
  Proof.
    unfold GRA.embed.
    Local Transparent GRA.to_URA. unfold GRA.to_URA. Local Opaque GRA.to_URA.
    Local Transparent URA.unit. unfold URA.unit. Local Opaque URA.unit.
    cbn.
    apply func_ext_dep. i.
    dependent destruction H. ss. rewrite inG_prf. cbn. des_ifs.
  Qed.

End PROOF.

Section PROOF.
  Context `{@GRA.inG M Σ}.

  Lemma OwnM_unit
    :
      bi_entails True%I (OwnM ε)
  .
  Proof.
    unfold OwnM. r. uipropall. ii. rr. esplits; et. rewrite embed_unit. rewrite URA.unit_idl. refl.
  Qed.
End PROOF.


Ltac get_fresh_string :=
  match goal with
  | |- context["A"] =>
    match goal with
    | |- context["A0"] =>
      match goal with
      | |- context["A1"] =>
        match goal with
        | |- context["A2"] =>
          match goal with
          | |- context["A3"] =>
            match goal with
            | |- context["A4"] =>
              match goal with
              | |- context["A5"] => fail 5
              | _ => constr:("A5")
              end
            | _ => constr:("A4")
            end
          | _ => constr:("A3")
          end
        | _ => constr:("A2")
        end
      | _ => constr:("A1")
      end
    | _ => constr:("A0")
    end
  | _ => constr:("A")
  end
.
Ltac iDes :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ _ (INamed ?namm) ?ip] =>
           match ip with
           | @bi_or _ _ _ =>
             let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ "|" +:+ namm +:+ "]")) in
             iDestruct namm as pat
           | @bi_pure _ _ => iDestruct namm as "%"
           | @iNW _ ?newnamm _ => iEval (unfold iNW) in namm; iRename namm into newnamm
           | @bi_sep _ _ _ =>
             let f := get_fresh_string in
             let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ f +:+ "]")) in
             iDestruct namm as pat
           | @bi_exist _ _ (fun x => _) =>
             let x := fresh x in
             iDestruct namm as (x) namm
           end
         end
.
Ltac iCombineAll :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ (@environments.Esnoc _ _ (INamed ?nam1) _) (INamed ?nam2) _] =>
           iCombine nam1 nam2 as nam1
         end
.
Ltac xtra := iCombineAll; iAssumption.

(*** TODO: MOVE TO ImpPrelude ***)
Definition add_ofs (ptr: val) (d: Z): val :=
  match ptr with
  | Vptr b ofs => Vptr b (ofs + d)
  | _ => Vundef
  end
.

Lemma scale_int_8 n: scale_int (8 * n) = Some n.
Proof.
  unfold scale_int. des_ifs.
  - rewrite Z.mul_comm. rewrite Z.div_mul; ss.
  - contradict n0. eapply Z.divide_factor_l.
Qed.
Notation syscallU name vs := (z <- trigger (Syscall name vs↑ top1);; `z: Z <- z↓?;; Ret z).

Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
Notation pput p0 := (trigger (PPut p0↑)) (only parsing).

Fixpoint set_nth A (n:nat) (l:list A) (new:A) {struct l} : option (list A) :=
  match n, l with
  | O, x :: l' => Some (new :: l')
  | O, other => None
  | S m, [] => None
  | S m, x :: t => option_map (cons x) (set_nth m t new)
  end.

Section INLINE.
  Context `{Σ: GRA.t}.
  (*** Just a simple unfolding of HoareFun; we can actually use HoareFun here. ***)
  Definition specbody (fs: fspec) (arg: Any.t): itree Es' Any.t :=
    x <- trigger (Take fs.(meta));;
    trigger (Cassume (fs.(precond) x arg arg));;;
    r <- trigger (Choose _);;
    trigger (Cassert (fs.(postcond) x r r));;;
    (* r <- r↓?;; *)
    Ret r
  .

  (* Definition inlined_specbody (f: Any.t -> itree Es' Any.t): Any.t -> itree Es' Any.t := *)
  (*   fun x => *)
  (*     trigger (Cassert (fspec_trivial.(precond) tt x x));;; *)
  (*     r <- f x;; *)
  (*     trigger (Cassume (fspec_trivial.(postcond) tt r r));;; *)
  (*     Ret r *)
  (* . *)
  Definition inlined_specbody (f: Any.t -> itree Es' Any.t): Any.t -> itree Es' Any.t :=
    f
  .
End INLINE.

Section MEMEXTRA.
  Context `{@GRA.inG memRA Σ}.
  Definition calloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (fun varg => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z⌝: iProp)%I),
                    (fun vret => (∃ b, (⌜vret = (Vptr b 0)↑⌝)
                                         ** OwnM ((b, 0%Z) |-> (List.repeat (Vint 0) sz))): iProp)%I
    ))).

  Definition MemStb: list (gname * fspec).
    apply [("calloc", calloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec) ; ("cmp", cmp_spec)].
  Defined.

  Definition MemConds: gname -> fspec :=
    fun gn => match (alist_find gn MemStb) with
              | Some res => res
              | None => ε%fspec
              end
  .

  Definition mem_fnsems: list (string * (Any.t → itree Es' Any.t)) :=
    [("calloc", specbody calloc_spec);
     ("free", specbody free_spec);
     ("load", specbody load_spec);
     ("store", specbody store_spec)].

  Definition initial_mem_mr := initial_mem_mr (fun _ => true) Sk.unit.
End MEMEXTRA.
