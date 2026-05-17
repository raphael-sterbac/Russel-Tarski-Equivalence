From Coq.ssr Require Import ssreflect.
From Coq.micromega Require Import Lia.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import RussellTarskiEquivalence.core.
Require Import RussellTarskiEquivalence.unscoped.
Require Import RussellTarskiEquivalence.Autosubst.


Set Primitive Projections.

(* ----- Contexts ----- *)

Definition ctx := list ty.

Notation "'ε'" := (@nil ty).
Notation " Γ ,, A " := (@cons ty A Γ) (at level 20, A at next level).

Arguments funcomp {X Y Z}%_type_scope (g f)%_function_scope.

Notation "f >> g" := (funcomp g f) (at level 50) : function_scope.

Notation "s .: sigma" := (scons s sigma) (at level 55, sigma at next level, right associativity).

Notation "s ⟨ xi1 ⟩" := (ren1 xi1 s) (at level 7, left associativity, format "s ⟨ xi1 ⟩").
(* Notation "⟨ xi ⟩" := (ren1 xi) (at level 1, left associativity, format "⟨ xi ⟩") : function_scope. *)

Notation "s [ sigma ]" := (subst1 sigma s) (at level 7, left associativity, format "s '/' [ sigma ]").

Notation "s [ t ]⇑" := (subst_term (scons t (shift >> var_term)) s) (at level 7, left associativity, format "s '/' [ t ]⇑") .

Notation "s '..'" := (scons s ids) (at level 1, format "s ..").

Notation "↑" := (shift).
Notation "⇑" := (up_ren shift).

(* --- Substitution lemmas --- *)

Lemma subst_up_var_0_ty : forall (B : ty),
  B⟨⇑⟩[(var_term 0) ..] = B.
Proof.
  intros B. asimpl.
  apply idSubst_ty.
  intros [|x]; reflexivity.
Qed.

Lemma subst_up_var_0_russ : forall (B : russ_term),
  B⟨⇑⟩[(r_var_term 0) ..] = B.
Proof.
  intros B. asimpl.
  apply idSubst_russ_term.
  intros [|x]; reflexivity.
Qed.

(* ----- Shortands for products and sum types ----- *)

Inductive prod (A B : Type) : Type := | pair : A -> B -> prod A B.

Notation "x × y" := (prod x y) (at level 80, right associativity).

Inductive sigT {A : Type} (P : A -> Type) : Type :=
| existT (projT1 : A) (projT2 : P projT1) : sigT P.

Definition projT1 {A P} (x : @sigT A P) : A := let '(existT _ a _) := x in a.
Definition projT2 {A P} (x : @sigT A P) : P (projT1 x) := let '(existT _ _ p) := x in p.

Inductive sum (A : Type) (B : Type) : Type :=
| inj1 (a : A) : sum A B | inj2 (b:B) : sum A B.

Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
(at level 200, x binder, right associativity,
format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
: type_scope.
