Require Import RussellTarskiEquivalence.core.
Require Import RussellTarskiEquivalence.unscoped.

Require Import Setoid Morphisms Relation_Definitions.
Module Core.

Definition lvl := nat.

Inductive russ_term : Type :=
  | r_var_term : nat -> russ_term
  | r_Prod : russ_term -> russ_term -> russ_term
  | r_U : lvl -> russ_term
  | r_Lambda : russ_term -> russ_term -> russ_term -> russ_term
  | r_App : russ_term -> russ_term -> russ_term -> russ_term -> russ_term.

Lemma congr_r_Prod {s0 : russ_term} {s1 : russ_term} {t0 : russ_term}
  {t1 : russ_term} (H0 : s0 = t0) (H1 : s1 = t1) :
  r_Prod s0 s1 = r_Prod t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => r_Prod x s1) H0))
         (ap (fun x => r_Prod t0 x) H1)).
Qed.

Lemma congr_r_U {s0 : lvl} {t0 : lvl} (H0 : s0 = t0) : r_U s0 = r_U t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => r_U x) H0)).
Qed.

Lemma congr_r_Lambda {s0 : russ_term} {s1 : russ_term} {s2 : russ_term}
  {t0 : russ_term} {t1 : russ_term} {t2 : russ_term} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) : r_Lambda s0 s1 s2 = r_Lambda t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => r_Lambda x s1 s2) H0))
            (ap (fun x => r_Lambda t0 x s2) H1))
         (ap (fun x => r_Lambda t0 t1 x) H2)).
Qed.

Lemma congr_r_App {s0 : russ_term} {s1 : russ_term} {s2 : russ_term}
  {s3 : russ_term} {t0 : russ_term} {t1 : russ_term} {t2 : russ_term}
  {t3 : russ_term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2)
  (H3 : s3 = t3) : r_App s0 s1 s2 s3 = r_App t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => r_App x s1 s2 s3) H0))
               (ap (fun x => r_App t0 x s2 s3) H1))
            (ap (fun x => r_App t0 t1 x s3) H2))
         (ap (fun x => r_App t0 t1 t2 x) H3)).
Qed.

Lemma upRen_russ_term_russ_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_russ_term (xi_russ_term : nat -> nat) (s : russ_term) {struct s}
   : russ_term :=
  match s with
  | r_var_term s0 => r_var_term (xi_russ_term s0)
  | r_Prod s0 s1 =>
      r_Prod (ren_russ_term xi_russ_term s0)
        (ren_russ_term (upRen_russ_term_russ_term xi_russ_term) s1)
  | r_U s0 => r_U s0
  | r_Lambda s0 s1 s2 =>
      r_Lambda (ren_russ_term xi_russ_term s0)
        (ren_russ_term (upRen_russ_term_russ_term xi_russ_term) s1)
        (ren_russ_term (upRen_russ_term_russ_term xi_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      r_App (ren_russ_term xi_russ_term s0)
        (ren_russ_term (upRen_russ_term_russ_term xi_russ_term) s1)
        (ren_russ_term xi_russ_term s2) (ren_russ_term xi_russ_term s3)
  end.

Lemma up_russ_term_russ_term (sigma : nat -> russ_term) : nat -> russ_term.
Proof.
exact (scons (r_var_term var_zero) (funcomp (ren_russ_term shift) sigma)).
Defined.

Fixpoint subst_russ_term (sigma_russ_term : nat -> russ_term) (s : russ_term)
{struct s} : russ_term :=
  match s with
  | r_var_term s0 => sigma_russ_term s0
  | r_Prod s0 s1 =>
      r_Prod (subst_russ_term sigma_russ_term s0)
        (subst_russ_term (up_russ_term_russ_term sigma_russ_term) s1)
  | r_U s0 => r_U s0
  | r_Lambda s0 s1 s2 =>
      r_Lambda (subst_russ_term sigma_russ_term s0)
        (subst_russ_term (up_russ_term_russ_term sigma_russ_term) s1)
        (subst_russ_term (up_russ_term_russ_term sigma_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      r_App (subst_russ_term sigma_russ_term s0)
        (subst_russ_term (up_russ_term_russ_term sigma_russ_term) s1)
        (subst_russ_term sigma_russ_term s2)
        (subst_russ_term sigma_russ_term s3)
  end.

Lemma upId_russ_term_russ_term (sigma : nat -> russ_term)
  (Eq : forall x, sigma x = r_var_term x) :
  forall x, up_russ_term_russ_term sigma x = r_var_term x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_russ_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_russ_term (sigma_russ_term : nat -> russ_term)
(Eq_russ_term : forall x, sigma_russ_term x = r_var_term x) (s : russ_term)
{struct s} : subst_russ_term sigma_russ_term s = s :=
  match s with
  | r_var_term s0 => Eq_russ_term s0
  | r_Prod s0 s1 =>
      congr_r_Prod (idSubst_russ_term sigma_russ_term Eq_russ_term s0)
        (idSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upId_russ_term_russ_term _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda (idSubst_russ_term sigma_russ_term Eq_russ_term s0)
        (idSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upId_russ_term_russ_term _ Eq_russ_term) s1)
        (idSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upId_russ_term_russ_term _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App (idSubst_russ_term sigma_russ_term Eq_russ_term s0)
        (idSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upId_russ_term_russ_term _ Eq_russ_term) s1)
        (idSubst_russ_term sigma_russ_term Eq_russ_term s2)
        (idSubst_russ_term sigma_russ_term Eq_russ_term s3)
  end.

Lemma upExtRen_russ_term_russ_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_russ_term_russ_term xi x = upRen_russ_term_russ_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_russ_term (xi_russ_term : nat -> nat)
(zeta_russ_term : nat -> nat)
(Eq_russ_term : forall x, xi_russ_term x = zeta_russ_term x) (s : russ_term)
{struct s} : ren_russ_term xi_russ_term s = ren_russ_term zeta_russ_term s :=
  match s with
  | r_var_term s0 => ap (r_var_term) (Eq_russ_term s0)
  | r_Prod s0 s1 =>
      congr_r_Prod
        (extRen_russ_term xi_russ_term zeta_russ_term Eq_russ_term s0)
        (extRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upExtRen_russ_term_russ_term _ _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda
        (extRen_russ_term xi_russ_term zeta_russ_term Eq_russ_term s0)
        (extRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upExtRen_russ_term_russ_term _ _ Eq_russ_term) s1)
        (extRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upExtRen_russ_term_russ_term _ _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App
        (extRen_russ_term xi_russ_term zeta_russ_term Eq_russ_term s0)
        (extRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upExtRen_russ_term_russ_term _ _ Eq_russ_term) s1)
        (extRen_russ_term xi_russ_term zeta_russ_term Eq_russ_term s2)
        (extRen_russ_term xi_russ_term zeta_russ_term Eq_russ_term s3)
  end.

Lemma upExt_russ_term_russ_term (sigma : nat -> russ_term)
  (tau : nat -> russ_term) (Eq : forall x, sigma x = tau x) :
  forall x, up_russ_term_russ_term sigma x = up_russ_term_russ_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_russ_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_russ_term (sigma_russ_term : nat -> russ_term)
(tau_russ_term : nat -> russ_term)
(Eq_russ_term : forall x, sigma_russ_term x = tau_russ_term x)
(s : russ_term) {struct s} :
subst_russ_term sigma_russ_term s = subst_russ_term tau_russ_term s :=
  match s with
  | r_var_term s0 => Eq_russ_term s0
  | r_Prod s0 s1 =>
      congr_r_Prod
        (ext_russ_term sigma_russ_term tau_russ_term Eq_russ_term s0)
        (ext_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (upExt_russ_term_russ_term _ _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda
        (ext_russ_term sigma_russ_term tau_russ_term Eq_russ_term s0)
        (ext_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (upExt_russ_term_russ_term _ _ Eq_russ_term) s1)
        (ext_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (upExt_russ_term_russ_term _ _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App
        (ext_russ_term sigma_russ_term tau_russ_term Eq_russ_term s0)
        (ext_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (upExt_russ_term_russ_term _ _ Eq_russ_term) s1)
        (ext_russ_term sigma_russ_term tau_russ_term Eq_russ_term s2)
        (ext_russ_term sigma_russ_term tau_russ_term Eq_russ_term s3)
  end.
  

Lemma up_ren_ren_russ_term_russ_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_russ_term_russ_term zeta) (upRen_russ_term_russ_term xi) x =
  upRen_russ_term_russ_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_russ_term (xi_russ_term : nat -> nat)
(zeta_russ_term : nat -> nat) (rho_russ_term : nat -> nat)
(Eq_russ_term : forall x,
                funcomp zeta_russ_term xi_russ_term x = rho_russ_term x)
(s : russ_term) {struct s} :
ren_russ_term zeta_russ_term (ren_russ_term xi_russ_term s) =
ren_russ_term rho_russ_term s :=
  match s with
  | r_var_term s0 => ap (r_var_term) (Eq_russ_term s0)
  | r_Prod s0 s1 =>
      congr_r_Prod
        (compRenRen_russ_term xi_russ_term zeta_russ_term rho_russ_term
           Eq_russ_term s0)
        (compRenRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upRen_russ_term_russ_term rho_russ_term)
           (up_ren_ren _ _ _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda
        (compRenRen_russ_term xi_russ_term zeta_russ_term rho_russ_term
           Eq_russ_term s0)
        (compRenRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upRen_russ_term_russ_term rho_russ_term)
           (up_ren_ren _ _ _ Eq_russ_term) s1)
        (compRenRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upRen_russ_term_russ_term rho_russ_term)
           (up_ren_ren _ _ _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App
        (compRenRen_russ_term xi_russ_term zeta_russ_term rho_russ_term
           Eq_russ_term s0)
        (compRenRen_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (upRen_russ_term_russ_term rho_russ_term)
           (up_ren_ren _ _ _ Eq_russ_term) s1)
        (compRenRen_russ_term xi_russ_term zeta_russ_term rho_russ_term
           Eq_russ_term s2)
        (compRenRen_russ_term xi_russ_term zeta_russ_term rho_russ_term
           Eq_russ_term s3)
  end.

Lemma up_ren_subst_russ_term_russ_term (xi : nat -> nat)
  (tau : nat -> russ_term) (theta : nat -> russ_term)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_russ_term_russ_term tau) (upRen_russ_term_russ_term xi) x =
  up_russ_term_russ_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_russ_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_russ_term (xi_russ_term : nat -> nat)
(tau_russ_term : nat -> russ_term) (theta_russ_term : nat -> russ_term)
(Eq_russ_term : forall x,
                funcomp tau_russ_term xi_russ_term x = theta_russ_term x)
(s : russ_term) {struct s} :
subst_russ_term tau_russ_term (ren_russ_term xi_russ_term s) =
subst_russ_term theta_russ_term s :=
  match s with
  | r_var_term s0 => Eq_russ_term s0
  | r_Prod s0 s1 =>
      congr_r_Prod
        (compRenSubst_russ_term xi_russ_term tau_russ_term theta_russ_term
           Eq_russ_term s0)
        (compRenSubst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_ren_subst_russ_term_russ_term _ _ _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda
        (compRenSubst_russ_term xi_russ_term tau_russ_term theta_russ_term
           Eq_russ_term s0)
        (compRenSubst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_ren_subst_russ_term_russ_term _ _ _ Eq_russ_term) s1)
        (compRenSubst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_ren_subst_russ_term_russ_term _ _ _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App
        (compRenSubst_russ_term xi_russ_term tau_russ_term theta_russ_term
           Eq_russ_term s0)
        (compRenSubst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_ren_subst_russ_term_russ_term _ _ _ Eq_russ_term) s1)
        (compRenSubst_russ_term xi_russ_term tau_russ_term theta_russ_term
           Eq_russ_term s2)
        (compRenSubst_russ_term xi_russ_term tau_russ_term theta_russ_term
           Eq_russ_term s3)
  end.

Lemma up_subst_ren_russ_term_russ_term (sigma : nat -> russ_term)
  (zeta_russ_term : nat -> nat) (theta : nat -> russ_term)
  (Eq : forall x, funcomp (ren_russ_term zeta_russ_term) sigma x = theta x) :
  forall x,
  funcomp (ren_russ_term (upRen_russ_term_russ_term zeta_russ_term))
    (up_russ_term_russ_term sigma) x = up_russ_term_russ_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_russ_term shift
                (upRen_russ_term_russ_term zeta_russ_term)
                (funcomp shift zeta_russ_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_russ_term zeta_russ_term shift
                      (funcomp shift zeta_russ_term) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_russ_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_russ_term (sigma_russ_term : nat -> russ_term)
(zeta_russ_term : nat -> nat) (theta_russ_term : nat -> russ_term)
(Eq_russ_term : forall x,
                funcomp (ren_russ_term zeta_russ_term) sigma_russ_term x =
                theta_russ_term x) (s : russ_term) {struct s} :
ren_russ_term zeta_russ_term (subst_russ_term sigma_russ_term s) =
subst_russ_term theta_russ_term s :=
  match s with
  | r_var_term s0 => Eq_russ_term s0
  | r_Prod s0 s1 =>
      congr_r_Prod
        (compSubstRen_russ_term sigma_russ_term zeta_russ_term
           theta_russ_term Eq_russ_term s0)
        (compSubstRen_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_ren_russ_term_russ_term _ _ _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda
        (compSubstRen_russ_term sigma_russ_term zeta_russ_term
           theta_russ_term Eq_russ_term s0)
        (compSubstRen_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_ren_russ_term_russ_term _ _ _ Eq_russ_term) s1)
        (compSubstRen_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_ren_russ_term_russ_term _ _ _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App
        (compSubstRen_russ_term sigma_russ_term zeta_russ_term
           theta_russ_term Eq_russ_term s0)
        (compSubstRen_russ_term (up_russ_term_russ_term sigma_russ_term)
           (upRen_russ_term_russ_term zeta_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_ren_russ_term_russ_term _ _ _ Eq_russ_term) s1)
        (compSubstRen_russ_term sigma_russ_term zeta_russ_term
           theta_russ_term Eq_russ_term s2)
        (compSubstRen_russ_term sigma_russ_term zeta_russ_term
           theta_russ_term Eq_russ_term s3)
  end.

Lemma up_subst_subst_russ_term_russ_term (sigma : nat -> russ_term)
  (tau_russ_term : nat -> russ_term) (theta : nat -> russ_term)
  (Eq : forall x, funcomp (subst_russ_term tau_russ_term) sigma x = theta x)
  :
  forall x,
  funcomp (subst_russ_term (up_russ_term_russ_term tau_russ_term))
    (up_russ_term_russ_term sigma) x = up_russ_term_russ_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_russ_term shift
                (up_russ_term_russ_term tau_russ_term)
                (funcomp (up_russ_term_russ_term tau_russ_term) shift)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_russ_term tau_russ_term shift
                      (funcomp (ren_russ_term shift) tau_russ_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_russ_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_russ_term (sigma_russ_term : nat -> russ_term)
(tau_russ_term : nat -> russ_term) (theta_russ_term : nat -> russ_term)
(Eq_russ_term : forall x,
                funcomp (subst_russ_term tau_russ_term) sigma_russ_term x =
                theta_russ_term x) (s : russ_term) {struct s} :
subst_russ_term tau_russ_term (subst_russ_term sigma_russ_term s) =
subst_russ_term theta_russ_term s :=
  match s with
  | r_var_term s0 => Eq_russ_term s0
  | r_Prod s0 s1 =>
      congr_r_Prod
        (compSubstSubst_russ_term sigma_russ_term tau_russ_term
           theta_russ_term Eq_russ_term s0)
        (compSubstSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_subst_russ_term_russ_term _ _ _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda
        (compSubstSubst_russ_term sigma_russ_term tau_russ_term
           theta_russ_term Eq_russ_term s0)
        (compSubstSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_subst_russ_term_russ_term _ _ _ Eq_russ_term) s1)
        (compSubstSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_subst_russ_term_russ_term _ _ _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App
        (compSubstSubst_russ_term sigma_russ_term tau_russ_term
           theta_russ_term Eq_russ_term s0)
        (compSubstSubst_russ_term (up_russ_term_russ_term sigma_russ_term)
           (up_russ_term_russ_term tau_russ_term)
           (up_russ_term_russ_term theta_russ_term)
           (up_subst_subst_russ_term_russ_term _ _ _ Eq_russ_term) s1)
        (compSubstSubst_russ_term sigma_russ_term tau_russ_term
           theta_russ_term Eq_russ_term s2)
        (compSubstSubst_russ_term sigma_russ_term tau_russ_term
           theta_russ_term Eq_russ_term s3)
  end.

Lemma renRen_russ_term (xi_russ_term : nat -> nat)
  (zeta_russ_term : nat -> nat) (s : russ_term) :
  ren_russ_term zeta_russ_term (ren_russ_term xi_russ_term s) =
  ren_russ_term (funcomp zeta_russ_term xi_russ_term) s.
Proof.
exact (compRenRen_russ_term xi_russ_term zeta_russ_term _ (fun n => eq_refl)
         s).
Qed.

Lemma renRen'_russ_term_pointwise (xi_russ_term : nat -> nat)
  (zeta_russ_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_russ_term zeta_russ_term) (ren_russ_term xi_russ_term))
    (ren_russ_term (funcomp zeta_russ_term xi_russ_term)).
Proof.
exact (fun s =>
       compRenRen_russ_term xi_russ_term zeta_russ_term _ (fun n => eq_refl)
         s).
Qed.

Lemma renSubst_russ_term (xi_russ_term : nat -> nat)
  (tau_russ_term : nat -> russ_term) (s : russ_term) :
  subst_russ_term tau_russ_term (ren_russ_term xi_russ_term s) =
  subst_russ_term (funcomp tau_russ_term xi_russ_term) s.
Proof.
exact (compRenSubst_russ_term xi_russ_term tau_russ_term _ (fun n => eq_refl)
         s).
Qed.

Lemma renSubst_russ_term_pointwise (xi_russ_term : nat -> nat)
  (tau_russ_term : nat -> russ_term) :
  pointwise_relation _ eq
    (funcomp (subst_russ_term tau_russ_term) (ren_russ_term xi_russ_term))
    (subst_russ_term (funcomp tau_russ_term xi_russ_term)).
Proof.
exact (fun s =>
       compRenSubst_russ_term xi_russ_term tau_russ_term _ (fun n => eq_refl)
         s).
Qed.

Lemma substRen_russ_term (sigma_russ_term : nat -> russ_term)
  (zeta_russ_term : nat -> nat) (s : russ_term) :
  ren_russ_term zeta_russ_term (subst_russ_term sigma_russ_term s) =
  subst_russ_term (funcomp (ren_russ_term zeta_russ_term) sigma_russ_term) s.
Proof.
exact (compSubstRen_russ_term sigma_russ_term zeta_russ_term _
         (fun n => eq_refl) s).
Qed.

Lemma substRen_russ_term_pointwise (sigma_russ_term : nat -> russ_term)
  (zeta_russ_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_russ_term zeta_russ_term) (subst_russ_term sigma_russ_term))
    (subst_russ_term (funcomp (ren_russ_term zeta_russ_term) sigma_russ_term)).
Proof.
exact (fun s =>
       compSubstRen_russ_term sigma_russ_term zeta_russ_term _
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_russ_term (sigma_russ_term : nat -> russ_term)
  (tau_russ_term : nat -> russ_term) (s : russ_term) :
  subst_russ_term tau_russ_term (subst_russ_term sigma_russ_term s) =
  subst_russ_term (funcomp (subst_russ_term tau_russ_term) sigma_russ_term) s.
Proof.
exact (compSubstSubst_russ_term sigma_russ_term tau_russ_term _
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_russ_term_pointwise (sigma_russ_term : nat -> russ_term)
  (tau_russ_term : nat -> russ_term) :
  pointwise_relation _ eq
    (funcomp (subst_russ_term tau_russ_term)
       (subst_russ_term sigma_russ_term))
    (subst_russ_term
       (funcomp (subst_russ_term tau_russ_term) sigma_russ_term)).
Proof.
exact (fun s =>
       compSubstSubst_russ_term sigma_russ_term tau_russ_term _
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_russ_term_russ_term (xi : nat -> nat)
  (sigma : nat -> russ_term)
  (Eq : forall x, funcomp (r_var_term) xi x = sigma x) :
  forall x,
  funcomp (r_var_term) (upRen_russ_term_russ_term xi) x =
  up_russ_term_russ_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_russ_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_russ_term (xi_russ_term : nat -> nat)
(sigma_russ_term : nat -> russ_term)
(Eq_russ_term : forall x,
                funcomp (r_var_term) xi_russ_term x = sigma_russ_term x)
(s : russ_term) {struct s} :
ren_russ_term xi_russ_term s = subst_russ_term sigma_russ_term s :=
  match s with
  | r_var_term s0 => Eq_russ_term s0
  | r_Prod s0 s1 =>
      congr_r_Prod
        (rinst_inst_russ_term xi_russ_term sigma_russ_term Eq_russ_term s0)
        (rinst_inst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term sigma_russ_term)
           (rinstInst_up_russ_term_russ_term _ _ Eq_russ_term) s1)
  | r_U s0 => congr_r_U (eq_refl s0)
  | r_Lambda s0 s1 s2 =>
      congr_r_Lambda
        (rinst_inst_russ_term xi_russ_term sigma_russ_term Eq_russ_term s0)
        (rinst_inst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term sigma_russ_term)
           (rinstInst_up_russ_term_russ_term _ _ Eq_russ_term) s1)
        (rinst_inst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term sigma_russ_term)
           (rinstInst_up_russ_term_russ_term _ _ Eq_russ_term) s2)
  | r_App s0 s1 s2 s3 =>
      congr_r_App
        (rinst_inst_russ_term xi_russ_term sigma_russ_term Eq_russ_term s0)
        (rinst_inst_russ_term (upRen_russ_term_russ_term xi_russ_term)
           (up_russ_term_russ_term sigma_russ_term)
           (rinstInst_up_russ_term_russ_term _ _ Eq_russ_term) s1)
        (rinst_inst_russ_term xi_russ_term sigma_russ_term Eq_russ_term s2)
        (rinst_inst_russ_term xi_russ_term sigma_russ_term Eq_russ_term s3)
  end.

Lemma rinstInst'_russ_term (xi_russ_term : nat -> nat) (s : russ_term) :
  ren_russ_term xi_russ_term s =
  subst_russ_term (funcomp (r_var_term) xi_russ_term) s.
Proof.
exact (rinst_inst_russ_term xi_russ_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_russ_term_pointwise (xi_russ_term : nat -> nat) :
  pointwise_relation _ eq (ren_russ_term xi_russ_term)
    (subst_russ_term (funcomp (r_var_term) xi_russ_term)).
Proof.
exact (fun s => rinst_inst_russ_term xi_russ_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_russ_term (s : russ_term) : subst_russ_term (r_var_term) s = s.
Proof.
exact (idSubst_russ_term (r_var_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_russ_term_pointwise :
  pointwise_relation _ eq (subst_russ_term (r_var_term)) id.
Proof.
exact (fun s => idSubst_russ_term (r_var_term) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_russ_term (s : russ_term) : ren_russ_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_russ_term s)
         (rinstInst'_russ_term id s)).
Qed.

Lemma rinstId'_russ_term_pointwise :
  pointwise_relation _ eq (@ren_russ_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_russ_term s)
         (rinstInst'_russ_term id s)).
Qed.

Lemma varL'_russ_term (sigma_russ_term : nat -> russ_term) (x : nat) :
  subst_russ_term sigma_russ_term (r_var_term x) = sigma_russ_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_russ_term_pointwise (sigma_russ_term : nat -> russ_term) :
  pointwise_relation _ eq
    (funcomp (subst_russ_term sigma_russ_term) (r_var_term)) sigma_russ_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_russ_term (xi_russ_term : nat -> nat) (x : nat) :
  ren_russ_term xi_russ_term (r_var_term x) = r_var_term (xi_russ_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_russ_term_pointwise (xi_russ_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_russ_term xi_russ_term) (r_var_term))
    (funcomp (r_var_term) xi_russ_term).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive ty : Type :=
  | Prod : ty -> ty -> ty
  | Decode : lvl -> term -> ty
  | U : lvl -> ty
with term : Type :=
  | var_term : nat -> term
  | Lambda : ty -> ty -> term -> term
  | App : ty -> ty -> term -> term -> term
  | cProd : lvl -> term -> term -> term
  | cU : lvl -> lvl -> term
  | cLift : lvl -> lvl -> term -> term.

Lemma congr_Prod {s0 : ty} {s1 : ty} {t0 : ty} {t1 : ty} (H0 : s0 = t0)
  (H1 : s1 = t1) : Prod s0 s1 = Prod t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Prod x s1) H0))
         (ap (fun x => Prod t0 x) H1)).
Qed.

Lemma congr_Decode {s0 : lvl} {s1 : term} {t0 : lvl} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : Decode s0 s1 = Decode t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Decode x s1) H0))
         (ap (fun x => Decode t0 x) H1)).
Qed.

Lemma congr_U {s0 : lvl} {t0 : lvl} (H0 : s0 = t0) : U s0 = U t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => U x) H0)).
Qed.

Lemma congr_Lambda {s0 : ty} {s1 : ty} {s2 : term} {t0 : ty} {t1 : ty}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  Lambda s0 s1 s2 = Lambda t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => Lambda x s1 s2) H0))
            (ap (fun x => Lambda t0 x s2) H1))
         (ap (fun x => Lambda t0 t1 x) H2)).
Qed.

Lemma congr_App {s0 : ty} {s1 : ty} {s2 : term} {s3 : term} {t0 : ty}
  {t1 : ty} {t2 : term} {t3 : term} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) (H3 : s3 = t3) : App s0 s1 s2 s3 = App t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans (eq_trans eq_refl (ap (fun x => App x s1 s2 s3) H0))
               (ap (fun x => App t0 x s2 s3) H1))
            (ap (fun x => App t0 t1 x s3) H2))
         (ap (fun x => App t0 t1 t2 x) H3)).
Qed.

Lemma congr_cProd {s0 : lvl} {s1 : term} {s2 : term} {t0 : lvl} {t1 : term}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cProd s0 s1 s2 = cProd t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cProd x s1 s2) H0))
            (ap (fun x => cProd t0 x s2) H1))
         (ap (fun x => cProd t0 t1 x) H2)).
Qed.

Lemma congr_cU {s0 : lvl} {s1 : lvl} {t0 : lvl} {t1 : lvl} (H0 : s0 = t0)
  (H1 : s1 = t1) : cU s0 s1 = cU t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => cU x s1) H0))
         (ap (fun x => cU t0 x) H1)).
Qed.

Lemma congr_cLift {s0 : lvl} {s1 : lvl} {s2 : term} {t0 : lvl} {t1 : lvl}
  {t2 : term} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cLift s0 s1 s2 = cLift t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cLift x s1 s2) H0))
            (ap (fun x => cLift t0 x s2) H1))
         (ap (fun x => cLift t0 t1 x) H2)).
Qed.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_ty (xi_term : nat -> nat) (s : ty) {struct s} : ty :=
  match s with
  | Prod s0 s1 =>
      Prod (ren_ty xi_term s0) (ren_ty (upRen_term_term xi_term) s1)
  | Decode s0 s1 => Decode s0 (ren_term xi_term s1)
  | U s0 => U s0
  end
with ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | var_term s0 => var_term (xi_term s0)
  | Lambda s0 s1 s2 =>
      Lambda (ren_ty xi_term s0) (ren_ty (upRen_term_term xi_term) s1)
        (ren_term (upRen_term_term xi_term) s2)
  | App s0 s1 s2 s3 =>
      App (ren_ty xi_term s0) (ren_ty (upRen_term_term xi_term) s1)
        (ren_term xi_term s2) (ren_term xi_term s3)
  | cProd s0 s1 s2 =>
      cProd s0 (ren_term xi_term s1) (ren_term (upRen_term_term xi_term) s2)
  | cU s0 s1 => cU s0 s1
  | cLift s0 s1 s2 => cLift s0 s1 (ren_term xi_term s2)
  end.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (var_term var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Fixpoint subst_ty (sigma_term : nat -> term) (s : ty) {struct s} : ty :=
  match s with
  | Prod s0 s1 =>
      Prod (subst_ty sigma_term s0) (subst_ty (up_term_term sigma_term) s1)
  | Decode s0 s1 => Decode s0 (subst_term sigma_term s1)
  | U s0 => U s0
  end
with subst_term (sigma_term : nat -> term) (s : term) {struct s} : term :=
  match s with
  | var_term s0 => sigma_term s0
  | Lambda s0 s1 s2 =>
      Lambda (subst_ty sigma_term s0) (subst_ty (up_term_term sigma_term) s1)
        (subst_term (up_term_term sigma_term) s2)
  | App s0 s1 s2 s3 =>
      App (subst_ty sigma_term s0) (subst_ty (up_term_term sigma_term) s1)
        (subst_term sigma_term s2) (subst_term sigma_term s3)
  | cProd s0 s1 s2 =>
      cProd s0 (subst_term sigma_term s1)
        (subst_term (up_term_term sigma_term) s2)
  | cU s0 s1 => cU s0 s1
  | cLift s0 s1 s2 => cLift s0 s1 (subst_term sigma_term s2)
  end.

Lemma upId_term_term (sigma : nat -> term)
  (Eq : forall x, sigma x = var_term x) :
  forall x, up_term_term sigma x = var_term x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_ty (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = var_term x) (s : ty) {struct s} :
subst_ty sigma_term s = s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod (idSubst_ty sigma_term Eq_term s0)
        (idSubst_ty (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with idSubst_term (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = var_term x) (s : term) {struct s} :
subst_term sigma_term s = s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda (idSubst_ty sigma_term Eq_term s0)
        (idSubst_ty (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (idSubst_ty sigma_term Eq_term s0)
        (idSubst_ty (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
        (idSubst_term sigma_term Eq_term s2)
        (idSubst_term sigma_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0) (idSubst_term sigma_term Eq_term s1)
        (idSubst_term (up_term_term sigma_term) (upId_term_term _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (idSubst_term sigma_term Eq_term s2)
  end.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_ty (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : ty) {struct s} :
ren_ty xi_term s = ren_ty zeta_term s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod (extRen_ty xi_term zeta_term Eq_term s0)
        (extRen_ty (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with extRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | var_term s0 => ap (var_term) (Eq_term s0)
  | Lambda s0 s1 s2 =>
      congr_Lambda (extRen_ty xi_term zeta_term Eq_term s0)
        (extRen_ty (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (extRen_ty xi_term zeta_term Eq_term s0)
        (extRen_ty (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
        (extRen_term xi_term zeta_term Eq_term s2)
        (extRen_term xi_term zeta_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0) (extRen_term xi_term zeta_term Eq_term s1)
        (extRen_term (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (extRen_term xi_term zeta_term Eq_term s2)
  end.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_ty (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : ty) {struct s} :
subst_ty sigma_term s = subst_ty tau_term s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod (ext_ty sigma_term tau_term Eq_term s0)
        (ext_ty (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with ext_term (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda (ext_ty sigma_term tau_term Eq_term s0)
        (ext_ty (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (ext_ty sigma_term tau_term Eq_term s0)
        (ext_ty (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
        (ext_term sigma_term tau_term Eq_term s2)
        (ext_term sigma_term tau_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0) (ext_term sigma_term tau_term Eq_term s1)
        (ext_term (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (ext_term sigma_term tau_term Eq_term s2)
  end.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_ty (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : ty)
{struct s} : ren_ty zeta_term (ren_ty xi_term s) = ren_ty rho_term s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod (compRenRen_ty xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_ty (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upRen_term_term rho_term) (up_ren_ren _ _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compRenRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} : ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | var_term s0 => ap (var_term) (Eq_term s0)
  | Lambda s0 s1 s2 =>
      congr_Lambda (compRenRen_ty xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_ty (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upRen_term_term rho_term) (up_ren_ren _ _ _ Eq_term) s1)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (compRenRen_ty xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_ty (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upRen_term_term rho_term) (up_ren_ren _ _ _ Eq_term) s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
        (compRenRen_term (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s2)
  end.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_ty (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : ty)
{struct s} : subst_ty tau_term (ren_ty xi_term s) = subst_ty theta_term s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod (compRenSubst_ty xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_ty (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compRenSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda (compRenSubst_ty xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_ty (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s2)
  | App s0 s1 s2 s3 =>
      congr_App (compRenSubst_ty xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_ty (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1) (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
        (compRenSubst_term (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s2)
  end.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_term : nat -> nat)
  (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_ty (sigma_term : nat -> term) (zeta_term : nat -> nat)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : ty) {struct s} :
ren_ty zeta_term (subst_ty sigma_term s) = subst_ty theta_term s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod (compSubstRen_ty sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_ty (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compSubstRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (compSubstRen_ty sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_ty (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (compSubstRen_ty sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_ty (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
        (compSubstRen_term (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s2)
  end.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_term : nat -> term)
  (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_ty (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : ty) {struct s} :
subst_ty tau_term (subst_ty sigma_term s) = subst_ty theta_term s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod
        (compSubstSubst_ty sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_ty (up_term_term sigma_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_subst_subst_term_term _ _ _ Eq_term)
           s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with compSubstSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda
        (compSubstSubst_ty sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_ty (up_term_term sigma_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_subst_subst_term_term _ _ _ Eq_term)
           s1)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (compSubstSubst_ty sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_ty (up_term_term sigma_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_subst_subst_term_term _ _ _ Eq_term)
           s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
        (compSubstSubst_term (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s2)
  end.

Lemma renRen_ty (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : ty) :
  ren_ty zeta_term (ren_ty xi_term s) = ren_ty (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_ty xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_ty_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty zeta_term) (ren_ty xi_term))
    (ren_ty (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_ty xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : term)
  :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty (xi_term : nat -> nat) (tau_term : nat -> term) (s : ty) :
  subst_ty tau_term (ren_ty xi_term s) =
  subst_ty (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_ty xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty_pointwise (xi_term : nat -> nat) (tau_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_ty tau_term) (ren_ty xi_term))
    (subst_ty (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_ty xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ty (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : ty) :
  ren_ty zeta_term (subst_ty sigma_term s) =
  subst_ty (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_ty sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ty_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ty zeta_term) (subst_ty sigma_term))
    (subst_ty (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_ty sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : ty) :
  subst_ty tau_term (subst_ty sigma_term s) =
  subst_ty (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_ty sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_ty tau_term) (subst_ty sigma_term))
    (subst_ty (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s => compSubstSubst_ty sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (var_term) xi x = sigma x) :
  forall x, funcomp (var_term) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_ty (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (var_term) xi_term x = sigma_term x) (s : ty)
{struct s} : ren_ty xi_term s = subst_ty sigma_term s :=
  match s with
  | Prod s0 s1 =>
      congr_Prod (rinst_inst_ty xi_term sigma_term Eq_term s0)
        (rinst_inst_ty (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | Decode s0 s1 =>
      congr_Decode (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  | U s0 => congr_U (eq_refl s0)
  end
with rinst_inst_term (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (var_term) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_term s = subst_term sigma_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | Lambda s0 s1 s2 =>
      congr_Lambda (rinst_inst_ty xi_term sigma_term Eq_term s0)
        (rinst_inst_ty (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s2)
  | App s0 s1 s2 s3 =>
      congr_App (rinst_inst_ty xi_term sigma_term Eq_term s0)
        (rinst_inst_ty (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
        (rinst_inst_term xi_term sigma_term Eq_term s3)
  | cProd s0 s1 s2 =>
      congr_cProd (eq_refl s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
        (rinst_inst_term (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s2)
  | cU s0 s1 => congr_cU (eq_refl s0) (eq_refl s1)
  | cLift s0 s1 s2 =>
      congr_cLift (eq_refl s0) (eq_refl s1)
        (rinst_inst_term xi_term sigma_term Eq_term s2)
  end.

Lemma rinstInst'_ty (xi_term : nat -> nat) (s : ty) :
  ren_ty xi_term s = subst_ty (funcomp (var_term) xi_term) s.
Proof.
exact (rinst_inst_ty xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_ty_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_ty xi_term)
    (subst_ty (funcomp (var_term) xi_term)).
Proof.
exact (fun s => rinst_inst_ty xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term (xi_term : nat -> nat) (s : term) :
  ren_term xi_term s = subst_term (funcomp (var_term) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (var_term) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ty (s : ty) : subst_ty (var_term) s = s.
Proof.
exact (idSubst_ty (var_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_ty_pointwise : pointwise_relation _ eq (subst_ty (var_term)) id.
Proof.
exact (fun s => idSubst_ty (var_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (var_term) s = s.
Proof.
exact (idSubst_term (var_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise :
  pointwise_relation _ eq (subst_term (var_term)) id.
Proof.
exact (fun s => idSubst_term (var_term) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_ty (s : ty) : ren_ty id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id s)).
Qed.

Lemma rinstId'_ty_pointwise : pointwise_relation _ eq (@ren_ty id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id s)).
Qed.

Lemma rinstId'_term (s : term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (var_term x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (var_term))
    sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_term : nat -> nat) (x : nat) :
  ren_term xi_term (var_term x) = var_term (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (var_term))
    (funcomp (var_term) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_term X Y :=
    up_term : X -> Y.

Class Up_ty X Y :=
    up_ty : X -> Y.

Class Up_russ_term X Y :=
    up_russ_term : X -> Y.

#[global] Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global] Instance Subst_ty : (Subst1 _ _ _) := @subst_ty.

#[global] Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global] Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global] Instance Ren_ty : (Ren1 _ _ _) := @ren_ty.

#[global] Instance VarInstance_term : (Var _ _) := @var_term.

#[global]
Instance Subst_russ_term : (Subst1 _ _ _) := @subst_russ_term.

#[global]
Instance Up_russ_term_russ_term : (Up_russ_term _ _) :=
 @up_russ_term_russ_term.

#[global] Instance Ren_russ_term : (Ren1 _ _ _) := @ren_russ_term.

#[global]
Instance VarInstance_russ_term : (Var _ _) := @r_var_term.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "s [ sigma_term ]" := (subst_ty sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ty" := up_ty (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_term ⟩" := (ren_ty xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_term ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var_term x) ( at level 5, format "x __term")  :
subst_scope.

Notation "s [ sigma_russ_term ]" := (subst_russ_term sigma_russ_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__russ_term" := up_russ_term (only printing)  : subst_scope.

Notation "↑__russ_term" := up_russ_term_russ_term (only printing)  :
subst_scope.

Notation "s ⟨ xi_russ_term ⟩" := (ren_russ_term xi_russ_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := r_var_term ( at level 1, only printing)  : subst_scope.

Notation "x '__russ_term'" := (@ids _ _ VarInstance_russ_term x)
( at level 5, format "x __russ_term", only printing)  : subst_scope.

Notation "x '__russ_term'" := (r_var_term x)
( at level 5, format "x __russ_term")  : subst_scope.

#[global]
Instance subst_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global]
Instance subst_ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ty)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_ty f_term s = subst_ty g_term t')
         (ext_ty f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ty)).
Proof.
exact (fun f_term g_term Eq_term s => ext_ty f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_ty_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_ty)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_ty f_term s = ren_ty g_term t')
         (extRen_ty f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_ty_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_ty)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_ty f_term g_term Eq_term s).
Qed.

#[global]
Instance subst_russ_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_russ_term)).
Proof.
exact (fun f_russ_term g_russ_term Eq_russ_term s t Eq_st =>
       eq_ind s
         (fun t' =>
          subst_russ_term f_russ_term s = subst_russ_term g_russ_term t')
         (ext_russ_term f_russ_term g_russ_term Eq_russ_term s) t Eq_st).
Qed.

#[global]
Instance subst_russ_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_russ_term)).
Proof.
exact (fun f_russ_term g_russ_term Eq_russ_term s =>
       ext_russ_term f_russ_term g_russ_term Eq_russ_term s).
Qed.

#[global]
Instance ren_russ_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_russ_term)).
Proof.
exact (fun f_russ_term g_russ_term Eq_russ_term s t Eq_st =>
       eq_ind s
         (fun t' =>
          ren_russ_term f_russ_term s = ren_russ_term g_russ_term t')
         (extRen_russ_term f_russ_term g_russ_term Eq_russ_term s) t Eq_st).
Qed.

#[global]
Instance ren_russ_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_russ_term)).
Proof.
exact (fun f_russ_term g_russ_term Eq_russ_term s =>
       extRen_russ_term f_russ_term g_russ_term Eq_russ_term s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_russ_term, Var, ids, Ren_russ_term,
                      Ren1, ren1, Up_russ_term_russ_term, Up_russ_term,
                      up_russ_term, Subst_russ_term, Subst1, subst1,
                      VarInstance_term, Var, ids, Ren_ty, Ren1, ren1,
                      Ren_term, Ren1, ren1, Up_term_term, Up_term, up_term,
                      Subst_ty, Subst1, subst1, Subst_term, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_russ_term, Var,
                                            ids, Ren_russ_term, Ren1, ren1,
                                            Up_russ_term_russ_term,
                                            Up_russ_term, up_russ_term,
                                            Subst_russ_term, Subst1, subst1,
                                            VarInstance_term, Var, ids,
                                            Ren_ty, Ren1, ren1, Ren_term,
                                            Ren1, ren1, Up_term_term,
                                            Up_term, up_term, Subst_ty,
                                            Subst1, subst1, Subst_term,
                                            Subst1, subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substSubst_ty_pointwise
                 | progress setoid_rewrite substSubst_ty
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite substRen_ty_pointwise
                 | progress setoid_rewrite substRen_ty
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renSubst_ty_pointwise
                 | progress setoid_rewrite renSubst_ty
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite renRen'_ty_pointwise
                 | progress setoid_rewrite renRen_ty
                 | progress setoid_rewrite substSubst_russ_term_pointwise
                 | progress setoid_rewrite substSubst_russ_term
                 | progress setoid_rewrite substRen_russ_term_pointwise
                 | progress setoid_rewrite substRen_russ_term
                 | progress setoid_rewrite renSubst_russ_term_pointwise
                 | progress setoid_rewrite renSubst_russ_term
                 | progress setoid_rewrite renRen'_russ_term_pointwise
                 | progress setoid_rewrite renRen_russ_term
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite rinstId'_ty_pointwise
                 | progress setoid_rewrite rinstId'_ty
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress setoid_rewrite instId'_ty_pointwise
                 | progress setoid_rewrite instId'_ty
                 | progress setoid_rewrite varLRen'_russ_term_pointwise
                 | progress setoid_rewrite varLRen'_russ_term
                 | progress setoid_rewrite varL'_russ_term_pointwise
                 | progress setoid_rewrite varL'_russ_term
                 | progress setoid_rewrite rinstId'_russ_term_pointwise
                 | progress setoid_rewrite rinstId'_russ_term
                 | progress setoid_rewrite instId'_russ_term_pointwise
                 | progress setoid_rewrite instId'_russ_term
                 | progress
                    unfold up_term_term, upRen_term_term,
                     up_russ_term_russ_term, upRen_russ_term_russ_term,
                     up_ren
                 | progress
                    cbn[subst_term subst_ty ren_term ren_ty subst_russ_term
                       ren_russ_term]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_russ_term, Var, ids, Ren_russ_term, Ren1,
                  ren1, Up_russ_term_russ_term, Up_russ_term, up_russ_term,
                  Subst_russ_term, Subst1, subst1, VarInstance_term, Var,
                  ids, Ren_ty, Ren1, ren1, Ren_term, Ren1, ren1,
                  Up_term_term, Up_term, up_term, Subst_ty, Subst1, subst1,
                  Subst_term, Subst1, subst1 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term;
                  try setoid_rewrite rinstInst'_ty_pointwise;
                  try setoid_rewrite rinstInst'_ty;
                  try setoid_rewrite rinstInst'_russ_term_pointwise;
                  try setoid_rewrite rinstInst'_russ_term.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term;
                  try setoid_rewrite_left rinstInst'_ty_pointwise;
                  try setoid_rewrite_left rinstInst'_ty;
                  try setoid_rewrite_left rinstInst'_russ_term_pointwise;
                  try setoid_rewrite_left rinstInst'_russ_term.

End Core.

Module Extra.

Import Core.

#[global] Hint Opaque subst_term: rewrite.

#[global] Hint Opaque subst_ty: rewrite.

#[global] Hint Opaque ren_term: rewrite.

#[global] Hint Opaque ren_ty: rewrite.

#[global] Hint Opaque subst_russ_term: rewrite.

#[global]
Hint Opaque ren_russ_term: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

