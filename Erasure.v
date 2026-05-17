From Coq Require Import ssreflect Lia Program.Equality PeanoNat Lists.List Arith.
Require Import RussellTarskiEquivalence.core.
Require Import RussellTarskiEquivalence.unscoped.
Require Import RussellTarskiEquivalence.Autosubst.
Require Import RussellTarskiEquivalence.Syntax.
Require Import RussellTarskiEquivalence.Typing.
Require Import RussellTarskiEquivalence.Utils.

(*  Erasure function *)
Fixpoint erase_term (t: term) : russ_term :=
    match t with
        | var_term n => r_var_term n 
        | Lambda A B b => r_Lambda (erase_ty A) (erase_ty B) (erase_term b)
        | App A B c a => r_App (erase_ty A) (erase_ty B) (erase_term c) (erase_term a)
        | cU n m => r_U n
        | cProd l a b => r_Prod (erase_term a) (erase_term b)
        | cLift n m t => (erase_term t)
    end
with erase_ty (A: ty): russ_term :=
    match A with
        | Prod A B => r_Prod (erase_ty A) (erase_ty B)
        | U n => r_U n
        | Decode n t => (erase_term t)
    end.

Fixpoint erase_context (Γ : ctx): russ_ctx := 
    match Γ with
    | nil => nil
    | cons a Γ' => cons (erase_ty a) (erase_context Γ')
    end.

(* ----- Erasure of substitutions lemmas ----- *)

Scheme ty_rect_mut_erase := Induction for ty Sort Type
with term_rect_mut_erase := Induction for term Sort Type.
Combined Scheme mut_ind_ty_term_erase from ty_rect_mut_erase, term_rect_mut_erase.

Lemma erase_ren_mutual :
  (forall A xi, (erase_ty A)⟨xi⟩ = erase_ty A⟨xi⟩) *
  (forall t xi, (erase_term t)⟨xi⟩ = erase_term t⟨xi⟩).
Proof.
  apply mut_ind_ty_term_erase; intros; cbn.
  - f_equal.
    + exact (H xi).
    + exact (H0 (upRen_term_term xi)).
  - exact (H xi).
  - reflexivity.
  - reflexivity.
  - f_equal.
    + exact (H xi).
    + exact (H0 (upRen_term_term xi)).
    + exact (H1 (upRen_term_term xi)).
  - f_equal.
    + exact (H xi).
    + exact (H0 (upRen_term_term xi)).
    + exact (H1 xi).
    + exact (H2 xi).
  - f_equal.
    + exact (H xi).
    + exact (H0 (upRen_term_term xi)).
  - reflexivity.
  - exact (H xi).
Qed.

Lemma defeq_erase_weak_ty : forall {A}, (erase_ty A)⟨↑⟩ = erase_ty A⟨↑⟩.
Proof. intros. apply (fst erase_ren_mutual). Qed.

Lemma defeq_erase_weak_ty_up : forall {A}, (erase_ty A)⟨⇑⟩ = erase_ty A⟨⇑⟩.
Proof. intros. apply (fst erase_ren_mutual). Qed.

Lemma defeq_erase_weak_term : forall {t}, (erase_term t)⟨↑⟩ = erase_term t⟨↑⟩.
Proof. intros. apply (snd erase_ren_mutual). Qed.


Lemma up_erase_term_pointwise sigma x :
  up_russ_term_russ_term (sigma >> erase_term) x = erase_term (up_term_term sigma x).
Proof.
  destruct x as [|n].
  - reflexivity.
  - cbn. apply (snd erase_ren_mutual).
Qed.

Lemma erase_subst_mutual :
  (forall A sigma, (erase_ty A)[sigma >> erase_term] = erase_ty A[sigma]) *
  (forall t sigma, (erase_term t)[sigma >> erase_term] = erase_term t[sigma]).
Proof.
  apply mut_ind_ty_term_erase; intros; 
    unfold subst1, Subst_ty, Subst_term, Subst_russ_term in *; cbn.
  - f_equal.
    + exact (H sigma).
    + rewrite <- (H0 (up_term_term sigma)).
      apply ext_russ_term. apply up_erase_term_pointwise.
  - exact (H sigma).
  - reflexivity.
  - reflexivity.
  - f_equal.
    + exact (H sigma).
    + rewrite <- (H0 (up_term_term sigma)).
      apply ext_russ_term. apply up_erase_term_pointwise.
    + rewrite <- (H1 (up_term_term sigma)).
      apply ext_russ_term. apply up_erase_term_pointwise.
  - f_equal.
    + exact (H sigma).
    + rewrite <- (H0 (up_term_term sigma)).
      apply ext_russ_term. apply up_erase_term_pointwise.
    + exact (H1 sigma).
    + exact (H2 sigma).
  - f_equal.
    + exact (H sigma).
    + rewrite <- (H0 (up_term_term sigma)).
      apply ext_russ_term. apply up_erase_term_pointwise.
  - reflexivity.
  - exact (H sigma).
Qed.

Lemma defeq_erase_subst_ty : forall {a A}, (erase_ty A)[(erase_term a) ..] = erase_ty A[a..].
Proof. 
  intros a A. 
  rewrite <- (fst erase_subst_mutual A (a..)).
  apply ext_russ_term.
  intros [|x]; reflexivity.
Qed.

Lemma defeq_erase_subst_term : forall {a t}, (erase_term t)[(erase_term a) ..] = erase_term t[a..].
Proof. 
  intros a t.
  rewrite <- (snd erase_subst_mutual t (a..)).
  apply ext_russ_term.
  intros [|x]; reflexivity.
Qed.

(* Correction of erasure  *)

Scheme wf_ctx_rect := Induction for WfContextDecl Sort Type
  with wf_ty_rect := Induction for WfTypeDecl Sort Type
  with typing_rect := Induction for TypingDecl Sort Type
  with conv_ty_rect := Induction for ConvTypeDecl Sort Type
  with conv_term_rect := Induction for ConvTermDecl Sort Type.

Combined Scheme mut_ind_erasure_rect from 
  wf_ctx_rect, wf_ty_rect, typing_rect, conv_ty_rect, conv_term_rect.

Theorem erasure_correction_mutual :
  (forall (Γ : ctx) (H : [ |- Γ ]), [ |-r erase_context Γ]) *
  ((forall (Γ : ctx) (A : ty) (H : [Γ |- A]), [(erase_context Γ) |-r (erase_ty A)]) *
  ((forall (Γ : ctx) (a : term) (A : ty) (H : [Γ |- a : A]), [(erase_context Γ) |-r (erase_term a) : (erase_ty A)]) *
  ((forall (Γ : ctx) (A B : ty) (H : [Γ |- A = B]), [(erase_context Γ) |-r (erase_ty A) = (erase_ty B)]) *
  (forall (Γ : ctx) (a b : term) (A : ty) (H : [Γ |- a = b : A]), [(erase_context Γ) |-r (erase_term a) = (erase_term b) : (erase_ty A)])))).
Proof.
  apply mut_ind_erasure_rect.

  (* WfContextDecl *)
  - simpl. constructor.
  - simpl. intros. apply r_concons; assumption.

  (* WfTypeDecl *)
  - intros. simpl. constructor. assumption.
  - intros. simpl. apply product_wf_ty; assumption.
  - intros. simpl. eapply r_wfTypeUniv. simpl in H. exact H.

  (* TypingDecl *)
  - intros. simpl. eapply r_wfTermConv. apply r_wfVar0. assumption. rewrite <- defeq_erase_weak_ty. apply r_TypeRefl.
    eapply r_weak_lemma. auto.
  - intros. simpl. eapply r_wfTermConv. eapply r_wfVarN. assumption. simpl in H0. exact H0. rewrite <- defeq_erase_weak_ty. apply r_TypeRefl.
    eapply r_weak_lemma. auto.
  - intros. simpl. constructor; assumption.
  - intros. simpl. constructor. assumption. assumption.
  - intros. simpl. destruct (Nat.eq_dec m l) as [H_eq | H_neq].
    + subst. auto.
    + assert (H_lt : m < l). lia. apply r_wfTermCumul with (1:=H_lt). assumption.  
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_wfTermConv. apply r_wfTermApp. assumption. assumption. rewrite <- defeq_erase_subst_ty. apply r_TypeRefl.
    eapply r_substitution_lemma. apply r_wftype_typing_inv in H. destruct H.
    simpl in r0. apply r_prod_ty_inv in r0. destruct r0. exact r1. exact H0.
  - intros. simpl. eapply r_wfTermConv. exact H. assumption.

  (* -ConvTypeDecl*)
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_TypeUnivConv. exact H.
  - intros. simpl. eapply r_TypeUnivConv. apply r_TermRefl. eapply r_wfTermUniv. assumption. exact l.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. simpl in H. exact H.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. eapply r_wfTermProd. simpl in H. exact H. simpl in H0. exact H0.
  - intros. simpl. apply r_TypeRefl. assumption.
  - intros. simpl. eapply r_TypeTrans; eauto.
  - intros. simpl. apply r_TypeSym. assumption.

  (* ConvTermDecl *)
  - intros. simpl. eapply r_ConvConv. rewrite <- defeq_erase_subst_term. eapply r_TermBRed. auto. simpl in H0; auto. auto. rewrite <- defeq_erase_subst_ty. apply r_TypeRefl.
    eapply r_substitution_lemma. apply r_wftype_typing_inv in H0. destruct H0. simpl in r0. exact r0. exact H1.
  - intros. simpl. apply r_TermPiCong.  simpl in H; exact H.  simpl in H0; exact H0. simpl in H1; exact H1.
  - intros. simpl. eapply r_ConvConv. apply r_TermAppCong; assumption. rewrite <- defeq_erase_subst_ty. apply r_TypeRefl.
    eapply r_substitution_lemma. apply r_type_defeq_inv in H0. destruct H0 as [? []].
    simpl in r0. exact r0. apply r_typing_defeq_inv in H2. destruct H2 as [? []]. auto. 
  - intros. simpl. apply r_TermLambdaCong; assumption. 
  - intros. simpl. destruct (Nat.eq_dec p n) as [H_eq | H_neq].
    + subst. apply r_TermPiCong. auto. apply r_TermRefl. auto. apply r_TermRefl. auto.
    + assert (H_lt : p < n). lia. eapply r_TermUnivCumul. instantiate (1:=p). apply r_TermRefl. apply r_wfTermProd. all: auto.
  - intros. simpl. apply r_TermRefl. apply r_wfTermUniv. auto. lia. 
  - intros. simpl. apply r_TermRefl. destruct (Nat.eq_dec n l) as [H_eq | H_neq].
    + subst. auto.
    + assert (H_lt: n < l). lia. eapply r_wfTermCumul. exact H_lt. auto.
  - intros. simpl. destruct (Nat.eq_dec n p) as [H_eq | H_neq].
    + subst. auto. 
    + eapply r_TermUnivCumul. simpl in H. exact H. lia.
  - intros. simpl. apply r_TermRefl. auto.
  - intros. simpl. 
    rewrite <- defeq_erase_weak_term.
    rewrite <- defeq_erase_weak_ty. 
    rewrite <- defeq_erase_weak_ty_up.
    apply r_TermFunEta. assumption.
  - intros. simpl. apply r_TermRefl. assumption.
  - intros. simpl. eapply r_ConvConv; eauto.
  - intros. simpl. apply r_TermSym; assumption.
  - intros. simpl. eapply r_TermTrans; eauto.
Qed.

Definition ctx_formation_to_russ {Γ} (H : [ |- Γ ]) := 
  (fst erasure_correction_mutual) Γ H.

Definition erasure_correction_wf_ty {Γ A} (H : [Γ |- A]) := 
  (fst (snd erasure_correction_mutual)) Γ A H.

Definition erasure_correction_typing {Γ a A} (H : [Γ |- a : A]) := 
  (fst (snd (snd erasure_correction_mutual))) Γ a A H.

Definition erasure_correction_conversion {Γ A B} (H : [Γ |- A = B]) := 
  (fst (snd (snd (snd erasure_correction_mutual)))) Γ A B H.

Definition erasure_correction_conv_typing {Γ a b A} (H : [Γ |- a = b : A]) := 
  (snd (snd (snd (snd erasure_correction_mutual)))) Γ a b A H.

