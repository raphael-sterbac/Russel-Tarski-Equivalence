From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
Require Import Stdlib.Program.Equality.
Require Import PeanoNat.
Require Import Stdlib.Lists.List.

Set Primitive Projections.

Definition lvl := nat.

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

Inductive russ_term : Type :=
    | r_var_term : nat -> russ_term
    | r_Prod : russ_term -> russ_term -> russ_term
    | r_U : lvl -> russ_term
    | r_Lambda : russ_term -> russ_term -> russ_term -> russ_term
    | r_App : russ_term -> russ_term -> russ_term -> russ_term -> russ_term.


(* ----- Substitutions ----- *)
Axiom subst_ty : term -> ty -> ty.
Axiom weak_ty : ty -> ty.

Axiom subst_term : term -> term -> term.
Axiom weak_term : term -> term.

Axiom r_subst_term : russ_term -> russ_term -> russ_term.
Axiom r_weak_term : russ_term -> russ_term.

(* ----- Contexts ----- *)

Definition ctx := list ty.

Notation "'ε'" := (@nil ty).
Notation " Γ ,, A " := (@cons ty A Γ) (at level 20, A at next level).

(* ----- Rules ----- *)

Reserved Notation "[ |- Γ ]"  (at level 0, Γ at level 50).
Reserved Notation "[ Γ |- t : A ]" (at level 0, Γ, t, A at level 50).
Reserved Notation "[ Γ |- A = B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |- t = u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |- A ]"  (at level 0, Γ, A at level 50).

Inductive WfContextDecl : ctx -> Type :=
    | connil : [ |- ε ]
    | concons {Γ A} : 
        [ |- Γ ] -> 
        [ Γ |- A ] -> 
        [ |-  Γ ,, A]
(* Type well-formation *)
with WfTypeDecl  : ctx -> ty -> Type :=
    | wfTypeU {Γ n} : 
        [ |- Γ ] -> 
        [ Γ |- U n ] 
    | wfTypeProd {Γ} {A B} : 
        [ Γ |- A ] -> 
        [Γ ,, A |- B ] -> 
        [ Γ |- Prod A B ]
    | wfTypeDecode {Γ}  {a n} :
        [Γ |- a : U n] ->
        [Γ |- Decode n a]
(** **** Typing *)
with TypingDecl : ctx -> term -> ty -> Type :=
     | wfVar0 {Γ} {A} :
        [ Γ |- A ] ->
        [ Γ,, A|- var_term 0 : (weak_ty A) ]
    | wfVarN {Γ} {n A B} :
        [Γ |- A] ->
        [Γ |- var_term n : B] ->
        [Γ ,, A |- (var_term (n+1)) : (weak_ty B)]
    
    (* | weakening_var {Γ A B n} : [Γ |- var_term n : A] -> [Γ |- B] -> [Γ ,, B |- var_term n : A] *)
    | wfTermcProd {Γ} {a b l} :
        [Γ |- a : U l] ->
        [Γ |- Decode l a] ->
        [Γ ,, Decode l a |- b : U l] ->
        [Γ |- cProd l a b : U l]
    | wfTermcUniv {Γ} (l : lvl) (m:lvl) :
        [   |- Γ] ->
        (m<l) ->
        [Γ |- cU m l : U l] 
    | wfTermcLift {Γ} {l m a} :
        [Γ |- a : U m] ->
        (m<l) ->
        [Γ |- cLift m l a : U l]
    | wfTermLambda {Γ} {A B t} :
        [ Γ |- A ] ->        
        [ Γ ,, A |- t : B ] -> 
        [ Γ |- Lambda A B t : Prod A B]
    | wfTermApp {Γ} {f a A B} :
        [ Γ |- f : Prod A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- App A B f a : subst_ty a B ]
    | wfTermConv {Γ} {t A B} :
        [ Γ |- t : A ] -> 
        [ Γ |- A = B ] -> 
        [ Γ |- t : B ]
(* Conversion of types *)
with ConvTypeDecl : ctx -> ty -> ty  -> Type :=  
    | TypePiCong {Γ} {A B C D} :
        [ Γ |- A] ->
        [ Γ |- A = B] ->
        [ Γ ,, A |- C = D] ->
        [ Γ |- Prod A C = Prod B D]
    | TypeDecodeCong {Γ n a b} :
        [Γ |- a = b : U n] ->
        [Γ |- Decode n a = Decode n b]
    | TypeDecodeConv {Γ} (n: lvl) (m:lvl) :
        [  |- Γ ] ->
        (n< m) ->
        [Γ |- U n = Decode m (cU n m)]
    | TypeDecodeLiftConv {Γ} (n: lvl) (m:lvl) (u:term) :
        [Γ |- u: U m] ->
        (m < n) ->
        [Γ |- Decode m u = Decode n (cLift m n u)]
    | TypeDecodeProdConv {Γ a b n}:
        [Γ |- a: U n] ->
        [Γ,, Decode n a |- b :U n ] ->
        [Γ |- Decode n (cProd n a b) = Prod (Decode n a) (Decode n b)]
    | TypeRefl {Γ} {A} : 
        [ Γ |- A ] ->
        [ Γ |- A = A]
    | TypeTrans {Γ} {A B C} :
        [ Γ |- A = B] ->
        [ Γ |- B = C] ->
        [ Γ |- A = C]
    | TypeSym {Γ} {A B} :
        [ Γ |- A = B ] ->
        [ Γ |- B = A ]
(* Conversion of terms *)
with ConvTermDecl : ctx -> term -> term -> ty -> Type :=
    | TermBRed {Γ} {a t A B} :
            [ Γ |- A ] ->
            [ Γ ,, A |- t : B ] ->
            [ Γ |- a : A ] ->
            [ Γ |- App A B (Lambda A B t) a = (subst_term a t) : subst_ty a B ]
    | TermPiCong {Γ} {A B C D n} :
        [ Γ |- A : U n] ->
        [ Γ |- A = B : U n ] ->
        [ Γ ,, Decode n A |- C = D : U n ] ->
        [ Γ |- cProd n A C = cProd n B D : U n ]
    | TermAppCong {Γ} {a b f g A B A' B'} :
        [ Γ |- A = A'] ->
        [ Γ,,A |- B = B'] ->
        [ Γ |- f = g : Prod A B ] ->
        [ Γ |- a = b : A ] ->
        [ Γ |- App A B f a = App A' B' g b : subst_ty a B ]
    | TermLambdaCong {Γ} {t u A A' B' B} :
        [ Γ |- A ] ->
        [ Γ |- A = A' ] ->
        [ Γ,,A |- B = B' ] ->
        [ Γ,, A |- t = u : B ] ->
        [ Γ |- Lambda A B t = Lambda A' B' u : Prod A B ]
    | TermLiftingProdConv {Γ a b n p}:
        [Γ |- a: U p] ->
        [Γ,, Decode p a |- b : U p ] ->
        (p < n) ->
        [Γ |- cLift p n (cProd p a b) = cProd n (cLift p n a) (cLift p n b) : U n]
    | TermLiftingUnivConv {Γ p n m}:
        [   |- Γ] ->
        m < n ->
        n < p ->
        [Γ |- cLift n p (cU m n) =  cU m p : U p]
    | TermLiftingCumul {Γ a n l p}:
        [Γ |- a : U n] ->
        (n < p) ->
        (p < l) ->
        [Γ |- cLift p l (cLift n p a) = cLift n l a : U l]
    | TermLiftingCong {Γ a b n p}:
        [Γ |- a = b: U n] ->
        (n < p) ->
        [Γ |- cLift n p a = cLift n p b : U p]
    | TermFunEta {Γ} {f A B} :
        [ Γ |- f : Prod A B ] ->
        [ Γ |- Lambda A B (App (weak_ty A) (weak_ty B) (weak_term f) (var_term 0)) = f : Prod A B ]
    | TermRefl {Γ} {t A} :
        [ Γ |- t : A ] -> 
        [ Γ |- t = t : A ]
    | TermConv {Γ} {t t' A B} :
        [ Γ |- t = t': A ] ->
        [ Γ |- A = B ] ->
        [ Γ |- t = t': B ]
    | TermSym {Γ} {t t' A} :
        [ Γ |- t = t' : A ] ->
        [ Γ |- t' = t : A ]
    | TermTrans {Γ} {t t' t'' A} :
        [ Γ |- t = t' : A ] ->
        [ Γ |- t' = t'' : A ] ->
        [ Γ |- t = t'' : A ]
    
where "[ Γ |- T ]" := (WfTypeDecl Γ T)
and   "[ Γ |- t : T ]" := (TypingDecl Γ t T)
and   "[ Γ |- A = B ]" := (ConvTypeDecl Γ A B)
and   "[ Γ |- t = t' : T ]" := (ConvTermDecl Γ t t' T)
and   "[ |- Γ ]" := (WfContextDecl Γ).

(* ----- Russel Universes ----- *)

Definition russ_ctx := list russ_term.

Notation "'εr'" := (@nil russ_term).
Notation " Γ ,,r A " := (@cons russ_term A Γ) (at level 20, A at next level). 

Reserved Notation "[ |-r Γ ]"  (at level 0, Γ at level 50).
Reserved Notation "[ Γ |-r t : A ]" (at level 0, Γ, t, A at level 50).
Reserved Notation "[ Γ |-r A = B ]" (at level 0, Γ, A, B at level 50).
Reserved Notation "[ Γ |-r t = u : A ]" (at level 0, Γ, t, u, A at level 50).
Reserved Notation "[ Γ |-r A ]"  (at level 0, Γ, A at level 50).

Inductive Russ_WfContextDecl : russ_ctx -> Type :=
    | r_connil : [ |-r εr ]
    | r_concons {Γ A} : 
        [ |-r Γ ] -> 
        [ Γ |-r A ] -> 
        [ |-r Γ ,,r A]
(* Type well-formation *)
with Russ_WfTypeDecl  : russ_ctx -> russ_term -> Type :=
    | r_wfTypeU {Γ n} : 
        [ |-r Γ ] -> 
        [ Γ |-r r_U n ] 
    | r_wfTypeUniv {Γ n} {a} :
        [ Γ |-r a : r_U n]
        -> [ Γ |-r a ] 
(** **** Typing *)
with russ_termpingDecl : russ_ctx -> russ_term -> russ_term -> Type :=
    | r_wfVar0 {Γ} {A} :
        [ Γ |-r A ] ->
        [ Γ,,r A |-r r_var_term 0 : (r_weak_term A) ]
    | r_wfVarN {Γ} {n A B} :
        [Γ |-r A] ->
        [Γ |-r r_var_term n : B] ->
        [Γ ,,r A |-r (r_var_term (n+1)) : (r_weak_term B)]

    (* | r_weakening_var {Γ A B n} : [Γ |- var_term n : A] -> [Γ |- B] -> [Γ ,, B |- var_term n : A] *)
    | r_wfTermLambda {Γ} {A B t} :
        [ Γ |-r A ] ->        
        [ Γ ,,r A |-r t : B ] -> 
        [ Γ |-r r_Lambda A B t : r_Prod A B]
    | r_wfTermApp {Γ} {f a A B} :
        [ Γ |-r f : r_Prod A B ] -> 
        [ Γ |-r a : A ] -> 
        [ Γ |-r r_App A B f a : r_subst_term a B ]
    | r_wfTermConv {Γ} {t A B} :
        [ Γ |-r t : A ] -> 
        [ Γ |-r A = B ] -> 
        [ Γ |-r t : B ]
    | r_wfTermProd {Γ n} {A B} : 
        [ Γ |-r A : r_U n] -> 
        [Γ ,,r A |-r B : r_U n] -> 
        [ Γ |-r r_Prod A B : r_U n]
    | r_wfTermUniv {Γ n m} :
        [ |-r Γ ] -> 
        (n<m) ->
        [ Γ |-r r_U n : r_U m ] 
    | r_wfTermCumul {Γ A n m}:
        (n < m) ->
        [Γ |-r A : r_U n] ->
        [Γ |-r A : r_U m]
    | r_TermConv {Γ t A B} :
        [Γ |-r t : A] ->
        [Γ |-r A = B] ->
        [Γ |-r t: B] 
(* Conversion of types *)
with Russ_ConvTypeDecl : russ_ctx -> russ_term -> russ_term  -> Type :=  
    | r_TypePiCong {Γ} {A B C D} :
        [ Γ |-r A] ->
        [ Γ |-r A = B] ->
        [ Γ ,,r A |-r C = D] ->
        [ Γ |-r r_Prod A C = r_Prod B D]
    | r_TypeRefl {Γ} {A} : 
        [ Γ |-r A ] ->
        [ Γ |-r A = A]
    | r_TypeSym {Γ} {A B} :
        [ Γ |-r A = B] ->
        [ Γ |-r B = A]
    | r_TypeTrans {Γ} {A B C} :
        [ Γ |-r A = B] ->
        [ Γ |-r B = C] ->
        [ Γ |-r A = C]
    | r_TypeUnivConv {Γ} {A B n} :
        [ Γ |-r  A = B : r_U n] ->
        [Γ |-r A = B]
(* Conversion of terms *)
with Russ_ConvTermDecl : russ_ctx -> russ_term -> russ_term -> russ_term -> Type :=
    | r_TermBRed {Γ} {a t A B} :
            [ Γ |-r A ] ->
            [ Γ ,,r A |-r t : B ] ->
            [ Γ |-r a : A ] ->
            [ Γ |-r r_App A B (r_Lambda A B t) a = r_subst_term a t : r_subst_term a B ]
    | r_TermAppCong {Γ} {a b f g A B A' B'} :
        [ Γ |-r A = A'] ->
        [ Γ,,r A |-r B = B'] ->
        [ Γ |-r f = g : r_Prod A B ] ->
        [ Γ |-r a = b : A] ->
        [ Γ |-r r_App A B f a = r_App A' B' g b : r_subst_term a B ]
    | r_TermLambdaCong {Γ}  {t u A A' B' B} :
        [ Γ |-r A ] ->
        [ Γ |-r A = A' ] ->
        [ Γ,,r A |-r B = B' ] ->
        [ Γ,,r A |-r t = u : B ] ->
        [ Γ |-r r_Lambda A B t = r_Lambda A' B' u : r_Prod A B ]
    | r_TermFunEta {Γ} {f A B} :
        [ Γ |-r f : r_Prod A B ] ->
        [ Γ |-r r_Lambda A B (r_App A B (r_weak_term f) (r_var_term 0)) = f : r_Prod A B ]
    | r_TermRefl {Γ} {t A} :
        [ Γ |-r t : A ] -> 
        [ Γ |-r t = t : A ]
    | r_ConvConv {Γ} {t t' A B} :
        [ Γ |-r t = t': A ] ->
        [ Γ |-r A = B ] ->
        [ Γ |-r t = t': B ]
    | r_TermSym {Γ} {t t' A} :
        [ Γ |-r t = t' : A ] ->
        [ Γ |-r t' = t : A ]
    | r_TermTrans {Γ} {t t' t'' A} :
        [ Γ |-r t = t' : A ] ->
        [ Γ |-r t' = t'' : A ] ->
        [ Γ |-r t = t'' : A ]
    | r_TermUnivConv {Γ} {A B n} :
        [ Γ |-r  A = B ] ->
        [ Γ |-r A = B : r_U n]
    | r_TermUnivCumul {Γ} {A B p n} :
        [ Γ |-r  A = B : r_U p ] ->
        p < n ->
        [ Γ |-r A = B : r_U n]
    
where "[ Γ |-r T ]" := (Russ_WfTypeDecl Γ T)
and   "[ Γ |-r t : T ]" := (russ_termpingDecl Γ t T)
and   "[ Γ |-r A = B ]" := (Russ_ConvTypeDecl Γ A B)
and   "[ Γ |-r t = t' : T ]" := (Russ_ConvTermDecl Γ t t' T)
and   "[ |-r Γ ]" := (Russ_WfContextDecl Γ).


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


(* ----- Axiomms ---- *)

Axiom substitution_lemma :
    forall {Γ A B a},
    [ Γ ,, A |- B ] ->
    [ Γ |- a : A ] ->
    [ Γ |- subst_ty a B ].

Axiom substitution_lemma_term: forall {Γ A B a t},
    [ Γ ,, A |- t: B ] ->
    [ Γ |- a : A ] ->
    [ Γ |- subst_term a t : subst_ty a B].

Axiom subst_cong: forall {Γ A B B' a a'},
    [ Γ ,, A |- B = B' ] ->
    [ Γ |- a = a' : A ] ->
    [ Γ |- subst_ty a B  = subst_ty a' B' ].

Axiom weak_lemma: forall {Γ A B},
    [ Γ |- A] ->
    [ Γ,,A |- weak_ty B ].

Axiom weak_cong: forall {Γ A B C},
    [Γ |- A = B] ->
    [Γ,, C |- weak_ty A = weak_ty B].

Axiom weak_term_lemma: forall {Γ a A B},
    [Γ |- a : A] ->
    [Γ,, B |- weak_term a : weak_ty A].

Axiom subst_var_0: forall {A},
    subst_ty (var_term 0) (weak_ty A) = A.

Axiom weak_ty_prod: forall {A B},
     Prod (weak_ty A) (weak_ty B) = weak_ty (Prod A B).

Axiom PiInj: forall {Γ A B A' B'},
    [Γ |- Prod A B = Prod A' B'] ->
    [Γ |- A = A'] × [Γ |- B = B'].

Axiom UInj: forall {Γ k l},
    [Γ |- U k = U l] ->
    k = l.

Axiom cohesion_prod_univ: forall {Γ t A B n},
    [Γ |- t : Prod A B] ->
    [Γ |- t : U n] ->
    False.

Axiom cohesion_weak_univ: forall {Γ t A n},
    [Γ |- t : weak_ty A] ->
    [Γ |- t : U n] ->
    False.

Axiom subject_red: forall {Γ a b A},
    [Γ |- a : A] ->
    [Γ |- a = b : A] ->
    [Γ |- b : A].


(* ----- Essential lemmas -----*)


Lemma inv_wfcontext_wftype Γ A:
    [Γ |- A] -> [Γ |- A] × [ |- Γ]
with  inv_wfcontext_typing Γ a A:
    [Γ |- a: A] -> [Γ |- a: A] × [ |- Γ].
Proof.
    + intros.
        constructor.
        auto.
        induction H.
        ++ auto.
        ++ auto.
        ++ apply inv_wfcontext_typing in t. destruct t. auto.
    + intros. constructor. auto. induction H.
        all : try(auto).
        ++ constructor. apply inv_wfcontext_wftype in w; destruct w. auto. auto.
        ++ constructor. auto. auto.
        ++ inversion IHTypingDecl. auto.
Qed. 


Definition subst_context (A B : ty) (Γ : ctx) (Δ : ctx) : ctx :=
  Δ ++ (B :: Γ).

Lemma context_conversion_ctx :
  (forall Γ, [ |- Γ ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ |- subst_context A B Γ' Δ ])
with context_conversion_ty :
  (forall Γ T, [ Γ |- T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- T ])
with context_conversion_term :
  (forall Γ t T, [ Γ |- t : T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- t : T ])
with context_conversion_ty_eq :
  (forall Γ T1 T2, [ Γ |- T1 = T2 ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- T1 = T2 ])
with context_conversion_term_eq :
  (forall Γ t1 t2 T, [ Γ |- t1 = t2 : T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |- A = B] -> [ subst_context A B Γ' Δ |- t1 = t2 : T ])
with type_defeq_inv Γ A B:
    [Γ |- A = B] ->
    [Γ |- A = B] × [Γ |- A] × [Γ |- B]
with typing_defeq_inv Γ a b A:
    [Γ |- a = b : A] ->
    [Γ |- a = b : A] × [Γ |- a : A] × [Γ |- b : A]
with wftype_typing_inv Γ a A:
    [Γ |- a : A] ->
    [Γ |- a : A] × [Γ |- A]
with wftype_hypothesis_inv Γ A B:
    [Γ,,A |- B] ->
    [Γ |- A] × [Γ,,A |- B]
with typing_hypothesis_inv Γ A b B:
    [Γ,,A |- b: B] ->
    [ |- Γ ] × [Γ |- A] × [Γ,,A |- b: B]
with conv_hypothesis_wftype {Γ C}:
    forall  A B,
    [Γ,,A |- C] ->
    [Γ |- A = B] ->
    [Γ,,B |- C]
with conv_hypothesis_typing {Γ C}:
    forall  A B a,
    [Γ,,A |- a : C] ->
    [Γ |- A = B] ->
    [Γ,,B |- a : C]
with  conv_hypothesis_type_eq {Γ A B C1 C2}:
    [Γ,,A |- C1 = C2] ->
    [Γ |- A = B] ->
    [Γ,,B |- C1 = C2]
with conv_hypothesis_term_eq {Γ A B a b C}:
    [Γ,,A |- a = b : C] ->
    [Γ |- A = B] ->
    [Γ,,B |- a = b : C].
Proof.

(* 1. context_conversion_ctx *)
- intros Γ H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv.
    + (* Nil *) destruct Δ0; inversion Heq.
    + (* Cons *) destruct Δ0.
      * (* On est au point d'insertion : Γ = A :: Γ' *)
        simpl in Heq. injection Heq. intros HeqG HeqA. subst.
        simpl. apply concons.
        ** auto.
        ** (* Ici on utilise le fait que B est bien formé dans Γ', ce qui vient de Hconv *)
           apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]].
           (* HwfB est [Γ' |- B]. Or IH donne [ |- subst... nil ] = [ |- Γ' ]. C'est trivial. *)
           auto.
      * (* On est après le point d'insertion : Γ = T :: Δ ++ ... *)
        simpl in Heq. injection Heq. intros. subst.
        simpl. apply concons.
        ** apply IHWfContextDecl with (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.
        ** apply context_conversion_ty with (Γ := (Δ0 ++ Γ'0,, A0)) (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.

(* 2. context_conversion_ty *)
  - intros Γ T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* U *) apply wfTypeU. eapply context_conversion_ctx; eauto.
    + (* Prod *) apply wfTypeProd.
      * eapply IHWfTypeDecl1; eauto.
      * eapply IHWfTypeDecl2 with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* Decode *) apply wfTypeDecode. eapply context_conversion_term; eauto.

  (* 3. context_conversion_term *)
  - intros Γ t T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* wfVar0 *)
      rename A into T_declared.
      (* Cas critique : Var 0 *)
      destruct Δ0.
      * (* Var 0 pointe sur A (le type remplacé) *)
        simpl. injection Heq. intros. subst.
        (* On doit prouver [B :: Γ' |- var 0 : weak B] *)
        (* On sait [A :: Γ' |- var 0 : weak A] *)
        eapply wfTermConv. instantiate (1 := weak_ty B0).
        ** apply wfVar0. apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
        ** (* Il faut prouver weak A = weak B *)
           apply TypeSym. (* On veut weak A0 = weak B0 à partir de Hconv: A0 = B0 *)
           apply weak_cong. (* Utilisation du lemme d'affaiblissement correct *)
           exact Hconv.
      * (* Var 0 pointe sur un type de Δ *)
        simpl. injection Heq. intros. subst.
        apply wfVar0.
        eapply context_conversion_ty; eauto.

    + (* wfVarN *)
        rename A into T_head.
        destruct Δ0.
        * (* Cas où Δ est vide : on remplace la tête A par B *)
            simpl. injection Heq. intros. subst.
            apply wfVarN.
            ** (* Sous-but 1 : B0 est bien formé dans Γ'0 *)
            apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
            ** (* Sous-but 2 : var n est bien typée dans Γ'0 *)
            (* C'est ici la correction : on utilise directement l'hypothèse H *)
            (* Car Γ'0 ne change pas, seule la tête A0 change en B0 *)
            exact H. (* Note: Vérifiez si votre hypothèse s'appelle H, H0 ou t0 selon vos intros *)
            
        * (* Cas où on est encore dans Δ *)
            simpl. injection Heq. intros. subst.
            apply wfVarN.
            ** eapply context_conversion_ty; eauto.
            ** eapply IHTypingDecl with (Δ := Δ0); auto.

    + (* cProd *) apply wfTermcProd.
      * eapply IHTypingDecl1; eauto.
      * eauto.
      * eapply IHTypingDecl2 with (Δ := Δ0 ,, Decode l a); eauto. simpl. reflexivity.
    + (* cUniv *) apply wfTermcUniv; auto. eapply context_conversion_ctx; eauto.
    + (* cLift *) apply wfTermcLift; auto.
    + (* Lambda *) apply wfTermLambda.
      * eapply context_conversion_ty; eauto.
      * eapply IHTypingDecl with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* App *) eapply wfTermApp.
      * eapply IHTypingDecl1; eauto.
      * eapply IHTypingDecl2; eauto.
    + (* Conv *) eapply wfTermConv.
      * eapply IHTypingDecl; eauto.
      * eapply context_conversion_ty_eq; eauto.

  (* 4. context_conversion_ty_eq *)
  - intros Γ T1 T2 H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* PiCong *) apply TypePiCong.
      * eapply context_conversion_ty; eauto.
      * eapply IHConvTypeDecl1; eauto.
      * eapply IHConvTypeDecl2 with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* DecodeCong *) apply TypeDecodeCong. eapply context_conversion_term_eq; eauto.
    + (* DecodeConv *) apply TypeDecodeConv. eapply context_conversion_ctx; eauto. auto.
    + (* DecodeLift *) apply TypeDecodeLiftConv; auto. eapply context_conversion_term; eauto.
    + (* DecodeProd *) apply TypeDecodeProdConv.
       * eapply context_conversion_term; eauto.
       * eapply context_conversion_term with (Δ := Δ0 ,, Decode n a); eauto. simpl. reflexivity.
    + (* Refl *) apply TypeRefl. eapply context_conversion_ty; eauto.
    + (* Trans *) eapply TypeTrans; eauto.
    + (* Sym *) apply TypeSym; eauto.

  (* 5. context_conversion_term_eq *)
  - intros Γ t1 t2 T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* BRed *) eapply TermBRed.
      * eapply context_conversion_ty; eauto.
      * eapply context_conversion_term with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
      * eapply context_conversion_term; eauto.
    + (* PiCong *) apply TermPiCong.
      * eapply context_conversion_term; eauto.
      * specialize (IHConvTermDecl1 Γ'0 A0 B0 Δ0 eq_refl Hconv). auto. 
      * specialize (IHConvTermDecl2 Γ'0 A0 B0 (Δ0,, Decode n A) eq_refl Hconv). auto.
    + (* AppCong *) eapply TermAppCong.
    
      * eapply context_conversion_ty_eq; eauto.
      * eapply context_conversion_ty_eq with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
      * eapply IHConvTermDecl1; eauto.
      * eapply IHConvTermDecl2; eauto.
    + (* LambdaCong *) apply TermLambdaCong.
       * eapply context_conversion_ty; eauto.
       * eapply context_conversion_ty_eq; eauto.
       * eapply context_conversion_ty_eq with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
       * eapply IHConvTermDecl with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* LiftingProd *) apply TermLiftingProdConv; auto.
       * eapply context_conversion_term; eauto.
       * eapply context_conversion_term with (Δ := Δ0 ,, Decode p a); eauto. simpl. reflexivity.
    + (* LiftingUniv *) apply TermLiftingUnivConv; auto. eapply context_conversion_ctx; eauto.
    + (* LiftingCumul *) apply TermLiftingCumul; auto. eapply context_conversion_term; eauto.
    + (* LiftingCong *) apply TermLiftingCong; auto.
    + (* FunEta *) apply TermFunEta. eapply context_conversion_term; eauto.
    + (* Refl *) apply TermRefl. eapply context_conversion_term; eauto.
    + (* Conv *) eapply TermConv.
       * eapply IHConvTermDecl; eauto.
       * eapply context_conversion_ty_eq; eauto.
    + (* Sym *) apply TermSym; eauto.
    + (* Trans *) eapply TermTrans; eauto.

  (* 6. type_defeq_inv *)
  - intros. split.
    + auto.
    +
      * (* Preuve que A est bien formé *)
        induction H.
        ** destruct IHConvTypeDecl1. destruct IHConvTypeDecl2. constructor. constructor. auto.
             auto. constructor. auto. apply conv_hypothesis_wftype with (A:=A). auto. auto.
        ** constructor. apply wfTypeDecode. apply typing_defeq_inv in c. destruct c as [_ [? ?]].
             auto. apply wfTypeDecode. apply typing_defeq_inv in c. destruct c as [_ [? ?]]. auto. 
        ** constructor. apply wfTypeU. eauto. apply wfTypeDecode. apply wfTermcUniv. auto. auto.
        ** constructor. apply wfTypeDecode. eauto. apply wfTypeDecode. eauto. apply wfTermcLift. auto. auto. 
        ** constructor. apply wfTypeDecode. apply wfTermcProd; auto. apply wfTypeDecode. auto. constructor.
             eapply typing_hypothesis_inv in t0. destruct t0 as [? []]. auto. apply wfTypeDecode in t0. auto.
        ** constructor. auto. auto.
        ** destruct IHConvTypeDecl1. destruct IHConvTypeDecl2. constructor. auto. auto.
        ** destruct IHConvTypeDecl. constructor. auto. auto.

  (* 7. typing_defeq_inv *)
  - intros. split.
    + auto.
    + split.
      * (* Preuve que 'a' est bien typé *)
        induction H.
        ** apply wfTermApp. apply wfTermLambda; auto. auto.
        ** apply wfTermcProd. auto. apply wfTypeDecode. auto. auto.
        ** apply wfTermApp. auto. auto.
        ** apply wfTermLambda. auto. auto.
        ** apply wfTermcLift. apply wfTermcProd. auto. auto. apply typing_hypothesis_inv in t0.
             destruct t0 as [? []]. auto. auto. auto. 
        ** apply wfTermcLift. apply wfTermcUniv. auto. auto. auto.
        ** apply wfTermcLift. apply wfTermcLift. auto. auto. auto.
        ** apply wfTermcLift. auto. auto.
        ** apply wftype_typing_inv in t. destruct t. inversion w. apply wfTermLambda.
               *** auto. 
               *** eapply wfTermConv.
                    **** eapply wfTermApp.
                          ***** rewrite weak_ty_prod. apply weak_term_lemma. auto.
                          ***** apply wfVar0. auto. 
                    (* 2. On prouve la conversion entre subst_ty (var 0) B et B *)
                    **** rewrite subst_var_0. apply TypeRefl. auto.
            
        ** auto.
        ** eapply wfTermConv. instantiate (1 := A). apply IHConvTermDecl. auto.
        ** eapply subject_red. instantiate (1:=t). auto. auto.
        ** apply IHConvTermDecl1.
      * (* Preuve que 'b' est bien typé *)
        induction H.
        ** (* BRed: subst_term a t *)
           eapply substitution_lemma_term. eauto. auto.
        ** (* PiCong *)
           apply wfTermcProd.
           *** auto.
           ***  apply wfTypeDecode. auto.
           ***  eapply conv_hypothesis_typing. instantiate (1:=Decode n A).
           auto. apply TypeDecodeCong. auto.
        ** (* AppCong *)
           eapply wfTermConv. instantiate (1 := subst_ty b B').
           *** apply type_defeq_inv in c. destruct c as [? []]. apply wfTermApp. eapply wfTermConv.
                instantiate (1:= Prod A B). auto. constructor. 
                auto. auto. auto. eapply wfTermConv. instantiate (1:= A). auto. auto.
           *** eapply subst_cong. instantiate (1:=A). auto. auto using TypeSym. auto using TermSym.
        ** (* LambdaCong *)
           eapply wfTermConv. instantiate (1:=Prod A' B'). apply wfTermLambda.
           *** apply type_defeq_inv in c. destruct c as [? []]. auto.
           *** eapply conv_hypothesis_typing. instantiate (1:=A). eapply wfTermConv. instantiate (1:= B). all: auto.
           *** apply TypePiCong. apply type_defeq_inv in c. destruct c as [? []]. auto. auto using TypeSym.
                eapply conv_hypothesis_type_eq. instantiate (1:= A). auto using TypeSym. auto.
        ** (* LiftingProd *)
           apply wfTermcProd.
           *** apply wfTermcLift. auto. auto.
           *** apply wfTypeDecode. apply wfTermcLift. auto. auto.
           *** constructor. eapply conv_hypothesis_typing. instantiate (1:= Decode p a). auto.
                eapply TypeDecodeLiftConv. all: auto.
        ** (* LiftingUniv *)
           apply wfTermcUniv. auto. lia.
        ** (* LiftingCumul *)
           apply wfTermcLift. auto. lia.
        ** (* LiftingCong *)
           apply wfTermcLift. auto. auto.
        ** (* FunEta *)
           auto.
        ** auto.
        ** eapply wfTermConv. instantiate (1:=A). auto. auto.
        ** eapply subject_red. instantiate (1:=t'). all: auto using TermSym.
        ** auto.

(* 8. wftype_typing_inv *)
  - intros. split.
    + exact H.
    + induction H.
      * (* wfVar0 *)
        apply weak_lemma. assumption.
      * (* wfVarN *)
        apply weak_lemma. assumption.
      * (* cProd *)
        apply wfTypeU. apply inv_wfcontext_wftype in IHTypingDecl1. destruct IHTypingDecl1. auto.
      * (* cUniv *)
        apply wfTypeU. assumption.
      * (* cLift *)
        apply wfTypeU. apply inv_wfcontext_wftype in IHTypingDecl. destruct IHTypingDecl. auto.
      * (* Lambda *)
        apply wfTypeProd.
        ** assumption.
        ** assumption.
      * (* App *)
        inversion IHTypingDecl1. subst.
        (* On a [Γ |- Prod A B], on inverse pour obtenir [Γ,, A |- B] *)
        eapply substitution_lemma.
        ** exact H5. (* [Γ,, A |- B] *)
        ** exact H0. (* [Γ |- a : A] *)
      * (* Conv *)
        apply type_defeq_inv in c. destruct c as [_ [_ HwfB]].
        exact HwfB.

(* 9. wftype_hypothesis_inv *)
  - intros. 
    (* Il est crucial de garder l'égalité du contexte pour l'induction *)
    remember (Γ ,, A) as Γ' in H.
    dependent induction H; intros; subst; try discriminate.
    
    (* Cas Cons : inversion de l'égalité Γ,, A = Γ0,, A0 *)
    + inversion w; subst. constructor; auto. constructor. auto.
    
    (* Cas Prod *)
    + (* H : [Γ,, A |- A0] *)
      (* H0 : [Γ,, A,, A0 |- B0] *)
      split.
      * (* Utilisation de l'hypothèse d'induction sur la gauche du produit *)
        (* IHWfTypeDecl1 prouve que si [Γ,, A |- A0], alors le contexte sous-jacent (Γ) valide A *)
        eapply IHWfTypeDecl1; reflexivity.
      * (* Reconstruction de la preuve originale *)
        apply wfTypeProd.
        ** auto.
        ** assumption.

    (* Cas Decode *)
    + split.
      * (* Induction sur le terme 'a' *)
        eapply typing_hypothesis_inv in t. destruct t as [? []]. auto.
      * apply wfTypeDecode. assumption. 

  (* 10. typing_hypothesis_inv *)
  - intros. split.
    + apply inv_wfcontext_typing in H. inversion H. inversion H1. auto.
    + split.
      * (* Preuve de [Γ |- A] *)
        inversion H; subst.
        ** (* wfVar0 *)  assumption.
        ** (* wfVarN *)  assumption.
        ** (* cProd *) apply inv_wfcontext_typing in H. inversion H. inversion H4. auto.
        ** (* cUniv *) inversion H0; subst; assumption.
        ** (* cLift *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* Lambda *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* App *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* Conv *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
      * (* Preuve de [Γ,, A |- b : B] *)
        exact H.

  (* 11. conv_hypothesis_wftype *)
  - intros A B Hwf Hconv.
    eapply context_conversion_ty with (Δ := ε).
    + simpl. exact Hwf.
    + reflexivity.
    + exact Hconv.

  (* 12. conv_hypothesis_typing *)
  - intros A B a Htyp Hconv.
    eapply context_conversion_term with (Δ := ε).
    + simpl. exact Htyp.
    + reflexivity.
    + exact Hconv.

  (* 13. conv_hypothesis_type_eq *)
  - intros Heq Hconv.
    eapply context_conversion_ty_eq with (Δ := ε).
    + simpl. exact Heq.
    + reflexivity.
    + exact Hconv.

  (* 14. conv_hypothesis_term_eq *)
  - intros  Heq Hconv.
    eapply context_conversion_term_eq with (Δ := ε).
    + simpl. exact Heq.
    + reflexivity.
    + exact Hconv.
Qed.       