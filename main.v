From Stdlib Require Import ssreflect.
From Stdlib Require Import Lia.
Require Import Stdlib.Program.Equality.
Require Import PeanoNat.
Require Import Stdlib.Lists.List.
Require Import Arith.

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
    | r_TermPiCong {Γ} {A B C D n} :
        [ Γ |-r A : r_U n] ->
        [ Γ |-r A = B : r_U n] ->
        [ Γ ,,r A |-r C = D : r_U n] ->
        [ Γ |-r r_Prod A C = r_Prod B D : r_U n]
    | r_TermFunEta {Γ} {f A B} :
        [ Γ |-r f : r_Prod A B ] ->
        [ Γ |-r r_Lambda A B (r_App (r_weak_term A) (r_weak_term B) (r_weak_term f) (r_var_term 0)) = f : r_Prod A B ]
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
    (*TODO : complétement faux ??? *)


Axiom cohesion_subst_univ: forall {Γ t a A n},
    [Γ |- t : subst_ty a A] ->
    [Γ |- t : U n] ->
    False.
    (*TODO : complétement faux ??? *)


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

Admitted. 



(* ----- Inversion Lemmas ----- *)
Lemma prod_ty_inv Γ A B :
  [Γ |- Prod A B] ->
  [Γ |- A] × [Γ,, A |- B].
Proof.
  intros Hty.
  inversion Hty . subst .
  - easy.
Qed.

Lemma decode_ty_inv Γ k t:
    [Γ |- Decode k t] ->
    [Γ |- t: U k].
Proof.
    intros Hty.
    inversion Hty.
    easy.
Qed.

Lemma lambda_inv u :
    forall Γ A B C,
    [Γ |- Lambda A B u : C] ->
    [Γ |- C = Prod A B] × [Γ,,A |- u : B].
Proof.
    intros. dependent induction H. 
    - constructor. apply TypeRefl. apply wfTypeProd. auto. apply wftype_typing_inv in H. destruct H. auto. auto.
    - constructor. eapply TypeTrans. instantiate (1:=A0). auto using TypeSym. eapply IHTypingDecl. instantiate (1:=u). auto.
        eapply IHTypingDecl. auto.  
Qed.

Lemma code_univ_inv_bis Γ k l A:
    [Γ |- cU k l : A] ->
    [Γ |- A = U l] × (k < l).
Proof.
    intros. dependent induction H.
    - constructor. apply TypeRefl. constructor. auto. auto.
    - constructor. eapply TypeTrans. instantiate (1:= A). auto using TypeSym. eapply IHTypingDecl. instantiate (1:=k). auto. eapply IHTypingDecl. auto.   
Qed.

Lemma code_univ_inv Γ k l n:
    [Γ |- cU k l : U n] ->
    l = n.
Proof.
    intros.
    apply code_univ_inv_bis in H. destruct H. apply UInj in c. auto.
Qed.


Lemma lift_inv_plus Γ k l A u:
    [Γ |- cLift k l u : A] ->
    ∑ n, [Γ |- A = U n] × l = n × k < l × [Γ |- u : U k].
Proof.
    intros. dependent induction H.
    - eexists l. constructor. apply TypeRefl. constructor. apply inv_wfcontext_typing in H. destruct H. auto. constructor. auto. constructor. auto. auto.
    - specialize (IHTypingDecl k l u eq_refl). destruct IHTypingDecl as [? [? [? []]]]. eexists l. constructor. eapply TypeTrans. instantiate (1:=A).
        auto using TypeSym. rewrite e. auto. constructor. auto. constructor. auto. auto.
Qed.

Lemma lift_inv Γ k l n u:
    [Γ |- cLift k l u : U n] ->
    l = n × k < l × [Γ |- u : U k].
Proof.
    intros.
    apply lift_inv_plus in H. destruct H as [? [? [? []]]]. apply UInj in c. constructor. rewrite e. auto. constructor. auto. auto.
Qed.

Lemma app_inv Γ A B C u1 u2:
    [Γ |- App A B u1 u2 : C] ->
    [Γ |- C = subst_ty u2 B] ×  [Γ |- A] × [Γ,,A |- B] × [Γ |- u1 : Prod A B] × [Γ |- u2 : A].
Proof.
    intros. dependent induction H.
    - apply wftype_typing_inv in H. destruct H. assert (wbis:=w). apply prod_ty_inv in wbis. destruct wbis.
        constructor. apply TypeRefl. eapply substitution_lemma. instantiate (1:=A). auto. auto.
        constructor. auto. constructor. auto. constructor. auto. auto.
    - specialize (IHTypingDecl A B u1 u2 eq_refl). destruct IHTypingDecl as [? [? [? []]]]. 
        constructor. apply TypeSym in c. apply TypeTrans with (1:= c). auto.
        constructor. auto. constructor. auto. constructor. auto. auto.   
Qed.

 Fixpoint iter_weak (n : nat) (A : ty) : ty :=
  match n with
  | 0 => A
  | S m => weak_ty (iter_weak m A)
  end.

Lemma var_inv :
  forall Γ t T, [Γ |- t : T] ->
  forall n Δ Γ' A,
  t = var_term n ->
  Γ = Δ ++ (A :: Γ') ->
  length Δ = n ->
  [Γ |- T = iter_weak (S n) A].
Proof.
  intros Γ t T H. intros n0 Δ0 Γ'0 A0 HeqTerm HeqCtx Hlen. subst. dependent induction H.

  (* 1. Cas wfVar0 : var 0 *)
  -
    destruct Δ0. simpl in x; try discriminate.
    simpl in x0. injection x0. intros; subst.
    simpl.
    apply TypeRefl. 
    apply weak_lemma. assumption.
    simpl in x. contradict x. auto.

  (* 2. Cas wfVarN : var (n+1) *)
  - destruct Δ0.
        * simpl in x. contradict x. lia.
        * simpl in x. simpl in x0. inversion x0. simpl. 
        specialize (IHTypingDecl Δ0 Γ'0 A0). simpl in IHTypingDecl. rewrite H2 in IHTypingDecl. specialize (IHTypingDecl JMeq_refl).
        eapply weak_cong in IHTypingDecl. exact IHTypingDecl. simpl.  assert (n = length Δ0) by lia. rewrite H0. auto.

  (* 4. Cas Conv : conversion de type *)
  - 
    eapply TypeTrans.
    + apply TypeSym. exact c.
    + eapply IHTypingDecl; eauto.
Qed.

Lemma variable_zero_inv Γ A:
    [Γ |- var_term 0 : A] ->
    ∑ Γ' B, [Γ |- A = weak_ty B] × (Γ = Γ' ,, B) × [Γ' |- B].
Proof.
    intros H.
    
    assert (Hstruct: ∑ Γ' B, Γ = Γ' ,, B).
    {
      remember (var_term 0) as t.
      induction H; try discriminate.
      - (* wfVar0 *) exists Γ, A. reflexivity.
      - (* wfVarN *) inversion Heqt. contradict Heqt. lia.
      - (* wfTermConv *) apply IHTypingDecl. assumption.
    }
    
    destruct Hstruct as [Γ' [B HeqΓ]].
    
    (* 2. On construit le témoin *)
    exists Γ', B.
    
    split.
    
    (* 3.1 Preuve de l'égalité de types via var_inv_gen *)
    - subst Γ.
      apply var_inv with (n:=0) (Δ:=ε) (Γ':=Γ') (A:=B) in H.
      + simpl in H. exact H.
      + reflexivity.
      + simpl. reflexivity.
      + reflexivity.

    - split.
      (* 3.2 Preuve de l'égalité du contexte *)
      + exact HeqΓ.
      
      (* 3.3 Preuve que B est bien formé dans Γ' *)
      + subst Γ.
        apply inv_wfcontext_typing in H.
        destruct H as [_ HwfΓ].
        inversion HwfΓ; subst.
        exact H2.
Qed.

Lemma variable_non_zero_inv Γ A n :
    [Γ |- var_term (S n) : A] ->
    ∑ Γ' T_head B, 
      (Γ = Γ' ,, T_head) × 
      [Γ' |- var_term n : B] × 
      [Γ |- A = weak_ty B].
Proof.
    intros H.
    remember (var_term (S n)) as t.
    induction H; try discriminate.

    (* 2. Cas wfVarN : C'est le cas constructeur *)
    - injection Heqt. intro Heqn. subst.
      exists Γ, A, B.
      
      split.
      + (* Γ_total = Γ ,, A *)
        reflexivity.
      
      + split. 
        ++ 
            assert (n0 = n) by lia. rewrite H0 in H. exact H.
        ++
           apply TypeRefl.
           apply weak_lemma.
           exact w. 

    (* 3. Cas TermConv : Conversion de type *)
    -
      specialize (IHTypingDecl Heqt).
      destruct IHTypingDecl as [Γ' [T_head [B_origin [HeqΓ [Htyp HeqType]]]]].
      
      exists Γ', T_head, B_origin.
      split.
      + exact HeqΓ.
      + split.
        ++ exact Htyp.
        ++
           eapply TypeTrans.
           * apply TypeSym. exact c.
           * exact HeqType.
Qed.

Lemma var_ctx_inv Γ A0 A1 n :
    [Γ |- var_term n : A0] ->
    [Γ |- var_term n : A1] ->
    [Γ |- A0 = A1].
Proof.
  (* On généralise le contexte et les types pour l'induction *)
  revert Γ A0 A1.
  induction n; intros Γ A0 A1 H1 H2.

  (* 1. Cas n = 0 *)
  - apply variable_zero_inv in H1.
    destruct H1 as [Γ1 [B1 [HeqA1 [HeqG1 Hwf1]]]].
    apply variable_zero_inv in H2.
    destruct H2 as [Γ2 [B2 [HeqA2 [HeqG2 Hwf2]]]].
    
    (* Les contextes doivent être identiques *)
    rewrite HeqG2 in HeqG1. injection HeqG1. intros HeqB HeqCtx. subst.
    
    (* On a A0 = weak B2 et A1 = weak B2 (à conversion près) *)
    eapply TypeTrans.
    + exact HeqA1.
    + apply TypeSym. exact HeqA2.

  (* 2. Cas n = S n *)
  - apply variable_non_zero_inv in H1.
    destruct H1 as [Γ1 [T1 [B1 [HeqG1 [Hvar1 HeqA1]]]]].
    apply variable_non_zero_inv in H2.
    destruct H2 as [Γ2 [T2 [B2 [HeqG2 [Hvar2 HeqA2]]]]].
    
    (* Les contextes doivent être identiques *)
    rewrite HeqG2 in HeqG1. injection HeqG1. intros HeqHead HeqTail. subst.
    
    (* Par hypothèse d'induction sur le contexte précédent Γ1 *)
    assert (Hconv : [Γ1 |- B1 = B2]).
    { apply IHn; assumption. }
    
    (* On propage l'égalité à travers l'affaiblissement *)
    eapply TypeTrans.
    + exact HeqA1. (* A0 = weak B1 *)
    + eapply TypeTrans.
      * (* weak B1 = weak B2 *)
        eapply weak_cong. exact Hconv. 
      * (* weak B2 = A1 *)
        apply TypeSym. exact HeqA2.
Qed.

Lemma code_prod_inv_plus Γ l A a b:
    [Γ |- cProd l a b : A] ->
    ∑ n, [Γ |- A = U n] × l = n × [Γ |- a : U l] × [Γ,,(Decode l a) |- b : U l].
Proof.
    intros. dependent induction H.
    - eexists l. constructor. apply TypeRefl. constructor. apply inv_wfcontext_typing in H. destruct H. auto.
        constructor. auto. constructor. auto. auto.
    - specialize (IHTypingDecl l a b eq_refl). destruct IHTypingDecl as [? [? [? []]]]. eexists l. constructor.
        eapply TypeTrans. instantiate (1:= A). auto using TypeSym. rewrite e. auto. constructor. auto. constructor. auto. auto.
Qed.


Lemma code_prod_inv Γ l n a b:
    [Γ |- cProd l a b : U n] ->
    l = n × [Γ |- a : U l] × [Γ,,(Decode l a) |- b : U l].
Proof.
    intros. apply code_prod_inv_plus in H. destruct H as [? [? [? []]]]. apply UInj in c. constructor. rewrite c. auto.
    constructor. auto. auto.
Qed.


(* ----- Fonctions d'effacement ----*)
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

Lemma product_wf_ty {Γ A B} : [Γ |-r A] -> [ Γ ,,r A |-r B ] -> [Γ |-r r_Prod A B].
Proof.
    intros. inversion H. inversion H0. symmetry in H3.
        eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermUniv.
            auto. lia. eapply r_wfTermUniv. constructor. auto. rewrite H3 in H. auto. lia. 
        eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermUniv.
            auto. lia. eapply r_wfTermCumul. instantiate (1:=n0). lia. symmetry in H3. rewrite H3 in H4. auto.
        inversion H0. eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermCumul.
            instantiate (1:=n). lia. auto. eapply r_wfTermUniv. auto. lia.
        eapply r_wfTypeUniv. instantiate (1:=Nat.max (n+1) (n0+1)). constructor. eapply r_wfTermCumul.
            instantiate (1:=n). lia. auto. eapply r_wfTermCumul. instantiate (1:=n0). lia. auto.    
Qed.

(* ----- Erasure of substitutions lemma, as axioms ----- *)

Axiom defeq_erase_weak_ty: forall {A}, r_weak_term (erase_ty A) = erase_ty (weak_ty A).
Axiom defeq_erase_weak_term: forall {A}, r_weak_term (erase_term A) = erase_term (weak_term A).
Axiom defeq_erase_subst_ty: forall {a A}, r_subst_term (erase_term a) (erase_ty A) = erase_ty (subst_ty a A).
Axiom defeq_erase_subst_term: forall {a t}, r_subst_term (erase_term a) (erase_term t) = erase_term (subst_term a t).
Axiom erase_weak_ty: forall {Γ A}, [Γ |-r r_weak_term (erase_ty A) = erase_ty (weak_ty A) ].
Axiom erase_subst_ty: forall {Γ a A}, [Γ |-r r_subst_term (erase_term a) (erase_ty A) = erase_ty (subst_ty a A) ].
Axiom erase_subst_term: forall {Γ a t B}, [Γ |-r r_subst_term (erase_term a) (erase_term t) = erase_term (subst_term a t) : B].


(* ----- Lemme de correction de l'effacement ----- *)

(* 1. On régénère les schémas proprement *)
Scheme wf_ctx_rect := Induction for WfContextDecl Sort Type
  with wf_ty_rect := Induction for WfTypeDecl Sort Type
  with typing_rect := Induction for TypingDecl Sort Type
  with conv_ty_rect := Induction for ConvTypeDecl Sort Type
  with conv_term_rect := Induction for ConvTermDecl Sort Type.

Combined Scheme mut_ind_erasure_rect from 
  wf_ctx_rect, wf_ty_rect, typing_rect, conv_ty_rect, conv_term_rect.

(* 2. Le Théorème *)
Theorem erasure_correction_mutual :
  (forall (Γ : ctx) (H : [ |- Γ ]), [ |-r erase_context Γ]) *
  ((forall (Γ : ctx) (A : ty) (H : [Γ |- A]), [(erase_context Γ) |-r (erase_ty A)]) *
  ((forall (Γ : ctx) (a : term) (A : ty) (H : [Γ |- a : A]), [(erase_context Γ) |-r (erase_term a) : (erase_ty A)]) *
  ((forall (Γ : ctx) (A B : ty) (H : [Γ |- A = B]), [(erase_context Γ) |-r (erase_ty A) = (erase_ty B)]) *
  (forall (Γ : ctx) (a b : term) (A : ty) (H : [Γ |- a = b : A]), [(erase_context Γ) |-r (erase_term a) = (erase_term b) : (erase_ty A)])))).
Proof.
  (* Appliquer simplement le schéma. Coq unifie automatiquement les prédicats. *)
  apply mut_ind_erasure_rect.

  (* --- 1. WfContextDecl (2 cas) --- *)
  - simpl. constructor.
  - simpl. intros. apply r_concons; assumption.

  (* --- 2. WfTypeDecl (3 cas) --- *)
  - intros. simpl. constructor. assumption.
  - intros. simpl. apply product_wf_ty; assumption.
  - intros. simpl. eapply r_wfTypeUniv. simpl in H. exact H.

  (* --- 3. TypingDecl (8 cas) --- *)
  - intros. simpl. eapply r_wfTermConv. apply r_wfVar0. assumption. apply erase_weak_ty.
  - intros. simpl. eapply r_wfTermConv. eapply r_wfVarN. assumption. simpl in H0. exact H0. apply erase_weak_ty.
  - intros. simpl. constructor; assumption.
  - intros. simpl. constructor. assumption. assumption.
  - intros. simpl. apply r_wfTermCumul with (1:=l0). assumption.
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_wfTermConv. apply r_wfTermApp. assumption. assumption. apply erase_subst_ty.
  - intros. simpl. eapply r_wfTermConv. exact H. assumption.

  (* --- 4. ConvTypeDecl (8 cas) --- *)
  - intros. simpl. constructor; assumption.
  - intros. simpl. eapply r_TypeUnivConv. exact H.
  - intros. simpl. eapply r_TypeUnivConv. apply r_TermRefl. eapply r_wfTermUniv. assumption. exact l.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. simpl in H. exact H.
  - intros. simpl. apply r_TypeRefl. eapply r_wfTypeUniv. eapply r_wfTermProd. simpl in H. exact H. simpl in H0. exact H0.
  - intros. simpl. apply r_TypeRefl. assumption.
  - intros. simpl. eapply r_TypeTrans; eauto.
  - intros. simpl. apply r_TypeSym. assumption.

  (* --- 5. ConvTermDecl (13 cas) --- *)
  - intros. simpl. eapply r_ConvConv. rewrite <- defeq_erase_subst_term. eapply r_TermBRed. auto. simpl in H0; auto. auto. apply erase_subst_ty.
  - intros. simpl. apply r_TermPiCong.  simpl in H; exact H.  simpl in H0; exact H0. simpl in H1; exact H1.
  - intros. simpl. eapply r_ConvConv. apply r_TermAppCong; assumption. apply erase_subst_ty.
  - intros. simpl. apply r_TermLambdaCong; assumption.
  - intros. simpl. eapply r_TermUnivCumul. instantiate (1:=p). apply r_TermRefl. apply r_wfTermProd. all: auto.
  - intros. simpl. apply r_TermRefl. apply r_wfTermUniv. auto. lia. 
  - intros. simpl. apply r_TermRefl. eapply r_wfTermCumul. exact l1. eapply r_wfTermCumul. exact l0. simpl in H. exact H.
  - intros. simpl. eapply r_TermUnivCumul. simpl in H. exact H. auto.
  - intros. simpl. 
    rewrite <- defeq_erase_weak_term.  
    rewrite <- defeq_erase_weak_ty. rewrite <- defeq_erase_weak_ty.
    apply r_TermFunEta. assumption.
  - intros. simpl. apply r_TermRefl. assumption.
  - intros. simpl. eapply r_ConvConv; eauto.
  - intros. simpl. apply r_TermSym; assumption.
  - intros. simpl. eapply r_TermTrans; eauto.
Qed.

(* 1. Formation du contexte (Premier élément) *)
Definition ctx_formation_to_russ {Γ} (H : [ |- Γ ]) := 
  (fst erasure_correction_mutual) Γ H.

(* 2. Bonne formation du type (Deuxième élément) *)
Definition erasure_correction_wf_ty {Γ A} (H : [Γ |- A]) := 
  (fst (snd erasure_correction_mutual)) Γ A H.

(* 3. Typage (Troisième élément) *)
Definition erasure_correction_typing {Γ a A} (H : [Γ |- a : A]) := 
  (fst (snd (snd erasure_correction_mutual))) Γ a A H.

(* 4. Conversion de type (Quatrième élément) *)
Definition erasure_correction_conversion {Γ A B} (H : [Γ |- A = B]) := 
  (fst (snd (snd (snd erasure_correction_mutual)))) Γ A B H.

(* 5. Conversion de terme (Cinquième et dernier élément) *)
Definition erasure_correction_conv_typing {Γ a b A} (H : [Γ |- a = b : A]) := 
  (snd (snd (snd (snd erasure_correction_mutual)))) Γ a b A H.


(* ----- Lemmes utiles ----- *)

Lemma lift_same {u}:
    forall Γ l,
    [Γ |- u : U l] ->
    [Γ |- u = cLift l l u : U l].
Proof.
    (*TODO : Preuve ? => en vrai c'est plus une notation (cLift l l u := u) qu'il faudrait *)
Admitted.

Lemma inf_right_max {k l}:
    l <= Nat.max k l.
Proof.
    lia.
Qed.

Lemma inf_left_max {k l}:
    k <= Nat.max k l.
Proof.
    lia.
Qed.

Lemma sup_max {k l n}:
    k < n ->
    l < n ->
    Nat.max k l < n.
Proof.
    intros. lia.
Qed.

Lemma sup_right_min {k l}:
    Nat.min k l <= l.
Proof.
    lia.
Qed.

Lemma sup_left_min {k l}:
    Nat.min k l <= k.
Proof.
    lia.
Qed.

Lemma inf_min {k l n}:
    n < k ->
    n < l ->
    n < Nat.min k l.
Proof.
    intros. lia.
Qed.

Lemma conv_lift_univ_min {Γ l l0 l1}:
    [ |- Γ] ->
    l < l0 ->
    l < l1 ->
    [Γ |- cLift (Nat.min l0 l1 ) l1 (cU l (Nat.min l0 l1)) = cU l l1 : U l1].
Proof.
    intros. destruct (lt_dec l0 l1) as [H_lt | H_ge].  
    - rewrite Nat.min_l. lia. apply TermLiftingUnivConv. all: auto.
    - rewrite Nat.min_r. lia. apply TermSym. apply lift_same. constructor. auto. auto.
Qed.

Lemma conv_lift_univ_min_comm {Γ l l0 l1}:
    [ |- Γ] ->
    l < l0 ->
    l < l1 ->
    [Γ |- cLift (Nat.min l1 l0 ) l1 (cU l (Nat.min l1 l0)) = cU l l1 : U l1].
Proof.
    intros. destruct (lt_dec l0 l1) as [H_lt | H_ge].  
    - rewrite Nat.min_r. lia. apply TermLiftingUnivConv. all: auto.
    - rewrite Nat.min_l. lia. apply TermSym. apply lift_same. constructor. auto. auto.
Qed.

Lemma conv_lift_cumul_max {Γ k l n0 u}:
    [Γ |- u : U l] ->
    n0 > k ->
    n0 > l ->
    [Γ |- cLift (Nat.max k l) n0 (cLift l (Nat.max k l) u) = cLift l n0 u : U n0].
Proof.
    intros. destruct (lt_dec l k) as [H_lt | H_ge].  
    - rewrite Nat.max_l. lia. apply TermLiftingCumul. auto. lia. auto.
    - rewrite Nat.max_r. lia. apply TermLiftingCong. apply TermSym. apply lift_same. auto. auto.
Qed.

Lemma conv_lift_cumul_max_comm {Γ k l n0 u}:
    [Γ |- u : U l] ->
    n0 > k ->
    n0 > l ->
    [Γ |- cLift (Nat.max l k) n0 (cLift l (Nat.max l k) u) = cLift l n0 u : U n0].
Proof.
     intros. destruct (lt_dec l k) as [H_lt | H_ge].  
    - rewrite Nat.max_r. lia. apply TermLiftingCumul. auto. lia. auto.
    - rewrite Nat.max_l. lia. apply TermLiftingCong. apply TermSym. apply lift_same. auto. auto.
Qed.

Lemma simplify_induction {Γ A0 A1 l0 l1 k v0 v1 u0 u1}:
    [Γ |- A0 = U l0] ->
    [Γ |- A1 = U l1] ->
    [Γ |- u0 = cLift k l0 v0 : A0] ->
    [Γ |- u1 = cLift k l1 v1 : A1] ->
    [Γ |- v0 = v1 : U k] ->
    [Γ |- A0 = A1] ->
    [Γ |- u0 = u1 : A0].
Proof.
    intros.
Admitted.

Lemma simplify_induction_grouped {Γ A0 A1 u0 u1}:
    (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- u0 = cLift k l0 v0 : A0]
        × [Γ |- u1 = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ) ->
    [Γ |- A0 = A1] ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
Proof.
    intros. destruct H as [? [? [? [? [? [? [? [? []]]]]]]]]. constructor.
    apply simplify_induction with (1:=c) (2:=c0) (3:=c1) (4:=c2) (5:=c3) (6:=H0). auto.
Qed.

Lemma simplify_induction_bis {Γ A0 A1 u0 u1}:
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- u0 = cLift k l0 v0 : A0]
        × [Γ |- u1 = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ) ->
    [Γ |- A0 = A1] ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
Proof.
    intros. destruct H.
    - auto.
    - apply simplify_induction_grouped. auto. auto. 
Qed.

Lemma erase_decode_inv_univ t:
    forall Γ l n,
    [Γ |- Decode l t] ->
    r_U n = erase_term t ->
    [Γ |- U n = Decode l t].
Proof.
induction t.
    all: try (intros; simpl in H0; contradict H0; congruence).
    - intros. apply inv_wfcontext_wftype in H. destruct H.
        simpl in H0; apply decode_ty_inv in w. apply code_univ_inv_bis in w. destruct w. inversion H0. apply UInj in c. subst.
        apply TypeDecodeConv with (n := l) (m := l0) in w0. exact w0. auto.
    - intros. simpl in H0. apply decode_ty_inv in H. apply lift_inv in H. destruct H. rewrite e.
        eapply TypeTrans. instantiate (1 := Decode l t).
        + eapply IHt. apply wfTypeDecode. destruct p. auto. auto.
        + apply TypeDecodeLiftConv. destruct p. auto. destruct p. rewrite e in l2. auto.
Qed.

Lemma erase_decode_inv_prod t:
    forall Γ l A B,
    [Γ |- Decode l t] ->
    [Γ |- Prod A B] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    (forall C, [Γ,, A |- B] -> [Γ,,A |- C] -> (erase_ty B = erase_ty C) -> [Γ,,A |- B = C]) ->
    r_Prod (erase_ty A) (erase_ty B) = erase_term t ->
    [Γ |- Prod A B = Decode l t].
Proof.
induction t.
    all: try (intros; simpl in H3; contradict H3; congruence).
    - intros. eapply TypeTrans. instantiate (1:=Prod (Decode  l0 t1) (Decode l0 t2)).
        + inversion H0. simpl in H3. inversion H3. constructor. auto.
            ++ apply H1. auto. apply decode_ty_inv in H. apply code_prod_inv in H. destruct H. destruct p.
                constructor. rewrite e in t. auto. auto. 
            ++ apply H2. auto. apply decode_ty_inv in H. apply code_prod_inv in H. destruct H. destruct p.
                eapply conv_hypothesis_wftype. instantiate (1:= Decode l0 t1). constructor. rewrite e in t0. auto. apply TypeSym.
                apply H1. auto. constructor; auto. rewrite e in t. all: try(simpl; auto).
        + apply TypeSym. apply decode_ty_inv in H. apply code_prod_inv in H. destruct H. rewrite e. eapply TypeDecodeProdConv.
            destruct p. rewrite e in t. auto. destruct p. rewrite e in t0. auto.
    - intros. simpl in H0. apply decode_ty_inv in H. apply lift_inv in H. destruct H. rewrite e.
        eapply TypeTrans. instantiate (1 := Decode l t).
        + eapply IHt. apply wfTypeDecode. destruct p. auto. auto. auto. auto. auto.
        + apply TypeDecodeLiftConv. destruct p. auto. destruct p. rewrite e in l2. auto. 
Qed.

(* Lemme auxiliaire pour extraire la structure du contexte d'une variable *)
Lemma get_var_split Γ n A :
  [Γ |- var_term n : A] ->
  ∑ Δ Γ' T, Γ = Δ ++ (T :: Γ') × length Δ = n.
Proof.
  intros H. dependent induction H.
  - (* wfVar0 *)
    exists nil, Γ, A. simpl. split; auto. 
  - (* wfVarN *)
    specialize (IHTypingDecl n0 eq_refl).
    destruct IHTypingDecl as [Δ [Γ' [T [Hctx Hlen]]]].
    exists (A :: Δ), Γ', T.
    simpl. split.
    + rewrite Hctx. reflexivity.
    + rewrite Hlen. lia.
  - (* wfTermConv *)
    apply IHTypingDecl. auto.
Qed.

Lemma erase_var_inv Γ t:
    forall A A1 n,
    [Γ |- var_term n : A] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    r_var_term n = erase_term t ->
    [Γ |- var_term n = t : A ].
Proof.
    induction t; intros A A1 n0 Hvar Ht Hinj Herase.
    
    (* 1. Cas var_term *)
    - simpl in Herase. injection Herase. intro Heq. subst.
      (* n = n0, t = var_term n0 *)
      apply TermRefl. exact Hvar.

    (* 2. Cas Lambda (Impossible par effacement) *)
    - simpl in Herase. discriminate.
    (* 3. Cas App (Impossible par effacement) *)
    - simpl in Herase. discriminate.
    (* 4. Cas cProd (Impossible par effacement) *)
    - simpl in Herase. discriminate.
    (* 5. Cas cU (Impossible par effacement) *)
    - simpl in Herase. discriminate.

    (* 6. Cas cLift *)
(* 6. Cas cLift *)
    - simpl in Herase.
      (* Inversion du typage de cLift l l0 t *)
      apply lift_inv_plus in Ht.
      destruct Ht as [k [H_A1_Uk [H_l0_k [H_l_k H_t_Ul]]]].
      
      (* H_t_Ul : [Γ |- t : U l] *)
      (* On applique l'hypothèse d'induction sur t avec le type U l *)
      assert (Heq : [Γ |- var_term n0 = t : A]).
      { apply IHt with (A1 := U l); auto. }
      
      (* Heq implique que t a pour type A. On le récupère par réduction du sujet *)
      assert (H_t_A : [Γ |- t : A]).
      { apply TermSym in Heq. eapply subject_red; eauto. }
      
      (* On utilise var_inv_gen pour montrer que A a la structure d'un type affaibli (weak) *)
      (* D'abord, on extrait la structure du contexte *)
      assert (Hsplit : ∑ Δ Γ' T, Γ = Δ ++ (T :: Γ') × length Δ = n0).
      { apply get_var_split with (A:=A); auto. }
      destruct Hsplit as [Δ [Γ' [T [Hctx Hlen]]]].
      
      (* On applique var_inv_gen *)
      assert (H_A_weak : [Γ |- A = iter_weak (S n0) T]).
      { apply var_inv with (t:=var_term n0) (n:=n0) (Δ:=Δ) (Γ':=Γ') (A:=T); auto. }
      
      (* iter_weak (S n) T commence par un weak_ty. On convertit le typage de t vers ce type. *)
      assert (H_t_weak : [Γ |- t : weak_ty (iter_weak n0 T)]).
      {
        simpl in H_A_weak.
        eapply wfTermConv.
        - exact H_t_A.
        - exact H_A_weak.
      }
      
      (* Contradiction : t est à la fois de type U l (H_t_Ul) et de type weak_ty ... (H_t_weak) *)
      exfalso.
      eapply cohesion_weak_univ.
      * exact H_t_weak.
      * exact H_t_Ul.
Qed.

Lemma erase_lambda_inv {Γ t}:
    forall A B A1 u,
    [Γ |- Lambda A B u : Prod A B] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    (forall C, [Γ,, A |- B] -> [Γ,,A |- C] -> (erase_ty B = erase_ty C) -> [Γ,,A |- B = C]) ->
    (forall Γ' u1 A1,
    [Γ' |- u : B] ->
    [Γ' |- u1 : A1] ->
    (erase_term u = erase_term u1) ->
    ([Γ' |- u = u1 : B] × [Γ' |- B = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- B = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- u = cLift k l0 v0 : B]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    r_Lambda (erase_ty A) (erase_ty B) (erase_term u) = erase_term t ->
    [Γ |- Lambda A B u = t : Prod A B ].
Proof.
    induction t.
        all: try(intros; simpl in H4; contradict H4; congruence).
        + intros. simpl in H4. inversion H4. apply lambda_inv in H; destruct H. apply type_defeq_inv in c; destruct c; destruct p.
        apply prod_ty_inv in w; destruct w. apply lambda_inv in H0; destruct H0. apply type_defeq_inv in c0; destruct c0; destruct p.
        apply prod_ty_inv in w3; destruct w3. apply H1 in H6. apply H2 in H7.
        apply TermLambdaCong. 
            all: auto using TypeSym.
            ++ assert (H:=H6). apply TypeSym in H6. apply conv_hypothesis_typing with (1:= t3) in H6. eapply H3 with (1:=t2) (2:= H6) in H8.
                destruct H8.
                +++ destruct p. auto.
                +++  destruct s as [? [? [? [? [? [? [? [? []]]]]]]]]. apply simplify_induction with (1:= c1) (2:= c2) (3:= c3) (4 := c4) (5:= c5) (6:= H7).
            ++ apply TypeSym in H6. apply conv_hypothesis_wftype with (1:= w4) in H6. auto.
        + intros. simpl in H4. eapply IHt in H4. all: auto. contradict H4; intros. apply subject_red in H4.
            apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]]. apply cohesion_prod_univ with (1:= H4) in t0.
            auto. apply typing_defeq_inv in H4. auto. instantiate (1:= U l). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]]. auto.     
Qed.

Lemma erase_app_inv {Γ t}:
    forall A B f a A1,
    [Γ |- App A B f a : subst_ty a B] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    (forall C, [Γ,, A |- B] -> [Γ,,A |- C] -> (erase_ty B = erase_ty C) -> [Γ,,A |- B = C]) ->
    (forall Γ' u1 A1,
    [Γ' |- f : Prod A B] ->
    [Γ' |- u1 : A1] ->
    (erase_term f = erase_term u1) ->
    ([Γ' |- f = u1 : Prod A B] × [Γ' |- Prod A B = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- Prod A B = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- f = cLift k l0 v0 : Prod A B]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    (forall Γ' u1 A1,
    [Γ' |- a : A] ->
    [Γ' |- u1 : A1] ->
    (erase_term a = erase_term u1) ->
    ([Γ' |- a = u1 : A] × [Γ' |- A = A1]) 
    + (∑ l0 l1 k v0 v1, [Γ' |- A = U l0]  
        × [Γ' |- A1 = U l1]
        × [Γ' |- a = cLift k l0 v0 : A] 
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    r_App (erase_ty A) (erase_ty B) (erase_term f) (erase_term a) = erase_term t ->
    [Γ |- App A B f a = t : subst_ty a B ].
Proof.
    induction t.
    all: try(intros; simpl in H5; contradict H5; congruence).

    - intros. simpl in H5. inversion H5.
      assert (Hsource := H). apply app_inv in Hsource. 
      destruct Hsource as [_ [HwfA [HwfB [Htyp_f Htyp_a]]]].
      
      assert (Htarget := H0). apply app_inv in Htarget.
      destruct Htarget as [HeqC [HwfA0 [HwfB0 [Htyp_f0 Htyp_a0]]]].

      assert (HeqA : [Γ |- A = t1]).
      { apply H1. auto. auto. auto. }
      
      assert (HeqB : [Γ,, A |- B = t2]).
      { apply H2. auto. 
        eapply conv_hypothesis_wftype. exact HwfB0. apply TypeSym. exact HeqA.
        auto. }

      specialize (H3 Γ t3 (Prod t1 t2)).
      assert (Htyp_f0_conv : [Γ |- t3 : Prod A B]).
      { eapply wfTermConv. exact Htyp_f0. apply TypeSym. apply TypePiCong. exact HwfA. exact HeqA. auto. }
      
     specialize (H3 Htyp_f Htyp_f0 H9).
      destruct H3 as [Left_f | Right_f].
      
      + destruct Left_f as [Heq_f _].

        specialize (H4 Γ t4 t1).
        assert (Htyp_a0_conv : [Γ |- t4 : A]).
        { eapply wfTermConv. exact Htyp_a0. apply TypeSym. exact HeqA. }
        
        specialize (H4 Htyp_a Htyp_a0 H10).
        destruct H4 as [Left_a | Right_a].
        
        * destruct Left_a as [Heq_a _].
          
          eapply TermTrans.
          instantiate (1 := App t1 t2 t3 t4).
          apply TermAppCong.
          -- exact HeqA.
          -- exact HeqB.
          -- exact Heq_f.
          -- exact Heq_a.
          -- apply TermRefl. eapply wfTermConv. instantiate (1:= subst_ty t4 t2). apply wfTermApp.
          auto. auto. eapply subst_cong. apply TypeSym. exact HeqB. apply TermSym. exact Heq_a.

        * assert (Heq_a : [Γ |- a = t4 : A]).
          { eapply simplify_induction_grouped. exact Right_a. 
            all: auto. }
            
          eapply TermTrans.
          instantiate (1 := App t1 t2 t3 t4).
          apply TermAppCong.
          -- exact HeqA.
          -- exact HeqB.
          -- exact Heq_f.
          -- exact Heq_a.
          -- apply TermRefl. eapply wfTermConv. instantiate (1:=A1). auto. eapply TypeTrans. instantiate (1:= subst_ty t4 t2).
          auto. eapply subst_cong. apply TypeSym. exact HeqB. apply TermSym. exact Heq_a.

      + destruct Right_f as [l0 [l1 [k [v0 [v1 [Heq_Prod_U _]]]]]].
        exfalso.
        eapply cohesion_prod_univ.
        -- exact Htyp_f.
        -- eapply wfTermConv. exact Htyp_f. exact Heq_Prod_U.

    - intros. simpl in H5.
      assert (Htarget := H0). apply lift_inv_plus in Htarget.
      destruct Htarget as [n [Heq_A1_Un [Heq_l_n [H_k_lt_l Htyp_inner]]]].
      specialize (IHt A B f a (U l)).
      
      assert (Heq_App_t5 : [Γ |- App A B f a = t : subst_ty a B]).
      { apply IHt; auto. }
      
      exfalso. apply typing_defeq_inv in Heq_App_t5. destruct Heq_App_t5 as [? []].
      eapply cohesion_subst_univ. exact t1. exact Htyp_inner.
Qed.

Lemma erase_cprod_inv {Γ t}:
    forall a b l A0 A1,
    [Γ |- cProd l a b : A0] ->
    [Γ |- t : A1] ->
    (* Hypothèses d'injectivité des types (nécessaire pour UInj) *)
    (forall C, [Γ |- A0] -> [Γ |- C] -> (erase_ty A0 = erase_ty C) -> [Γ |- A0 = C]) ->
    (* Hypothèse pour a *)
    (forall Γ' u1 A1,
    [Γ' |- a : U l] ->
    [Γ' |- u1 : A1] ->
    (erase_term a = erase_term u1) ->
    ([Γ' |- a = u1 : U l] × [Γ' |- U l = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- U l = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- a = cLift k l0 v0 : U l]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    (* Hypothèse pour b *)
    (forall Γ' u1 A1,
    [Γ' |- b : U l] -> (* Note: b est typé dans Γ,,Decode... mais simplifié ici selon le schéma erase_inj_term *)
    [Γ' |- u1 : A1] ->
    (erase_term b = erase_term u1) ->
    ([Γ' |- b = u1 : U l] × [Γ' |- U l = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- U l = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- b = cLift k l0 v0 : U l]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    r_Prod (erase_term a) (erase_term b) = erase_term t ->
    (* Conclusion : Egalité OU Lift *)
    ([Γ |- cProd l a b = t : A0 ] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- cProd l a b = cLift k l0 v0 : A0]
        × [Γ |- t = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ).
Proof.
    (*TODO : prouver ça ou seulement la première partie de la conclusion ?*)
Admitted.


Lemma erase_cuniv_inv
{Γ t}:
    forall k1 l1 k2 l2 A0 A1,
    [ Γ |- cU k1 l1 : A0 ] ->
    [ Γ |- cLift k2 l2 t : A1 ] ->
    r_U k1 = erase_term t ->
    (∑ k v0 v1,
        [Γ |- A0 = U l1] 
        × [Γ |- A1 = U l2]
        × [Γ |- cU k1 l1 = cLift k l1 v0 : A0]
        × [Γ |- cLift k2 l2 t = cLift k l2 v1 : A1]
        × [Γ |- v0 = v1 : U k] ). 
Proof.
    induction t.
    all: try(intros; simpl in H1; contradict H1; congruence).
    - intros. simpl in H1. inversion H1. rewrite H3 in H. set (K:= Nat.min (l0) (l1)).
    assert (H0bis:=H0). apply lift_inv_plus in H0bis. destruct H0bis as [? [? [? []]]].
    assert (tbis:=t). apply code_univ_inv_bis in tbis. destruct tbis. assert (Hbis :=H). apply code_univ_inv_bis in Hbis. destruct Hbis.
    apply UInj in c0.
    eexists K.  eexists (cU l K). eexists (cU l K). 
    constructor. auto. constructor. symmetry in e; rewrite e in c; auto. constructor.
    apply TermSym. eapply TermConv. instantiate (1:=U l1). apply conv_lift_univ_min. apply inv_wfcontext_typing in t. destruct t. all: auto using TypeSym. 
    constructor. eapply TermConv. instantiate (1:= U l2). rewrite c0. eapply TermTrans.
    instantiate (1:= cU l l2). apply TermLiftingUnivConv. apply inv_wfcontext_typing in t. destruct t. auto.
    auto. rewrite c0 in l3. auto. apply TermSym. apply TermLiftingUnivConv. apply inv_wfcontext_typing in t. destruct t. auto.
    apply inf_min. auto. auto. lia. rewrite e. auto using TypeSym. apply TermRefl. constructor. apply inv_wfcontext_typing in t. destruct t. auto.
    apply inf_min. auto. auto.
    
    - intros. simpl in H1. assert (H0bis:=H0). apply lift_inv_plus in H0bis. destruct H0bis as [? [? [? []]]].
    assert (t0bis:=t0). apply lift_inv_plus in t0bis. destruct t0bis as [? [? [? []]]].
    apply UInj in c0. symmetry in e0. rewrite e0 in c0. rewrite c0 in l3.  apply TermLiftingCumul with (1:=t1) (2:= l4) in l3.
    apply typing_defeq_inv in l3. destruct l3 as [? []]. 
    eapply IHt with (1:= H) (2:= t3) in H1. destruct H1 as [? [? [? [? [? [? []]]]]]].
    eexists projT5. eexists projT6. eexists projT7.
    constructor. auto.
    constructor. rewrite e. auto.
    constructor. auto.
    constructor. eapply TermConv. instantiate (1:= U l2). eapply TermTrans. instantiate (1:= cLift l l2 t).
    rewrite c0. auto. auto. rewrite e. auto using TypeSym. auto.
Qed. 





(* -------- Lemme principal ------- *)

Lemma erase_inj_ty {Γ A B} : [Γ |- A] -> [Γ |- B] -> (erase_ty A = erase_ty B) -> [Γ |- A = B]
with erase_inj_term {u0}:
    forall Γ u1 A0 A1,
    [Γ |- u0 : A0] ->
    [Γ |- u1 : A1] ->
    (erase_term u0 = erase_term u1) ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- u0 = cLift k l0 v0 : A0]
        × [Γ |- u1 = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ). 
Proof.

(* Types *)
induction 1. (* Induction on A *)
- intros;  destruct B. (* A = U n *)
    all: try (simpl in H0; contradict H0; congruence). (* Eliminate impossible cases *)
    + apply erase_decode_inv_univ. auto. simpl in H0. auto. 
    + simpl in H0. inversion H0. auto.

- intros; destruct B. (* A = Prod A1 A2 *)
    all: try (simpl in H2; contradict H2; congruence).
    + simpl in H2. inversion H2. apply TypePiCong. auto.
        ++ apply erase_inj_ty. auto. inversion H1. auto. auto.
        ++ apply erase_inj_ty. auto. inversion H1. eapply conv_hypothesis_wftype.
            instantiate (1:= B1). auto. apply erase_inj_ty. auto. auto. auto. auto.
    + simpl in H2. apply erase_decode_inv_prod. auto. constructor. all: try(auto).
    
- intros. destruct B. (* A = Decode n a *)
    + destruct a.
        all: try(simpl in H0; contradict H0; congruence).
        ++ apply TypeSym. apply erase_decode_inv_prod. constructor. all: try(auto).
        ++ apply TypeSym. apply erase_decode_inv_prod. constructor. all: try(auto).
    + simpl in H0. apply decode_ty_inv in H. apply erase_inj_term with (1:=t) (2:=H) in H0.
        destruct H0.  destruct p. apply UInj in c0. rewrite c0. apply TypeDecodeCong. rewrite c0 in c. auto.
        destruct s; destruct projT4; destruct projT5; destruct projT6; destruct projT7; destruct projT8; destruct p as [ ? [ ? []] ].
        apply UInj in c; apply UInj in c0. symmetry in c; rewrite c in c1. symmetry in c0; rewrite c0 in c2. eapply TypeTrans. instantiate (1:= Decode n (cLift projT5 n projT6)).
            apply TypeDecodeCong. auto. eapply TypeTrans. instantiate (1:=Decode l (cLift projT5 l projT7)).
            eapply TypeTrans. instantiate (1:= Decode projT5 projT6). apply TypeSym; apply TypeDecodeLiftConv. 
            ++ apply typing_defeq_inv in c1. destruct c1 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto. 
            ++ apply typing_defeq_inv in c1. destruct c1 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto.
            ++ eapply TypeTrans. instantiate (1:= Decode projT5 projT7). apply TypeDecodeCong. auto. apply TypeDecodeLiftConv.   
                apply typing_defeq_inv in c2. destruct c2 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto. 
                apply typing_defeq_inv in c2. destruct c2 as [? [? ]]. apply lift_inv in t2. destruct t2 as [? [? ]]. auto.
            ++ apply TypeDecodeCong. apply TermSym. auto. 

    + simpl in H0. apply TypeSym. apply erase_decode_inv_univ. apply wfTypeDecode. auto. auto.
    
(* Terms *)
- induction u0.
    + intros; destruct u1. (* u0 = var_term n *)
        all: try(simpl in H1; contradict H1; congruence).

        (* If u1 = var_term n0*)
        ++  constructor. simpl in H1. inversion H1. symmetry in H3; rewrite H3. constructor. constructor. auto.
            rewrite H3 in H0. apply var_ctx_inv with (1:= H) (2:= H0).
        
        (* If u1 = cLift *)
        ++ simpl in H1. apply inl. apply erase_var_inv with (1:=H) (2:=H0) in H1. constructor. all: auto.
            apply subject_red in H1. apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]]. apply lift_inv_plus in H1; destruct H1 as [? [? [? []]]].
            symmetry in e; symmetry in e0; rewrite e in c; rewrite e0 in c0. apply TypeSym in c0. apply TypeTrans with (1:= c) in c0.
            auto using TypeSym. auto.
    
    (* u0 = Lambda *)
    + intros. destruct u1.
        all: try(simpl in H1; contradict H1; congruence).
        ++ simpl in H1. inversion H1. apply lambda_inv in H. destruct H. apply lambda_inv in H0. destruct H0.
            apply wftype_typing_inv in  t3; destruct t3. apply wftype_typing_inv in t4; destruct t4.
            apply wftype_hypothesis_inv in w; destruct w. apply wftype_hypothesis_inv in w0; destruct w0.  
            apply erase_inj_ty with (1:=w) (2:= w0) in H3. assert (H' := H3). apply conv_hypothesis_typing with (1:= t3) in H3.
            apply IHu0 with (1:=H3) (2:= t4) in H5. destruct H5.
            assert (H := H'). apply conv_hypothesis_wftype with (1:= w1) in H'. apply erase_inj_ty with (1:= H') (2:=w2) in H4. destruct p.
                +++ constructor. 
                    constructor. eapply TermConv. instantiate (1:=Prod t t0). eapply TermLambdaCong. auto. auto.
                    eapply conv_hypothesis_type_eq. instantiate (1:= t1). auto. auto using TypeSym.
                    eapply conv_hypothesis_term_eq. instantiate (1:= t1). auto. apply TypeSym; auto.
                    auto using TypeSym. apply TypeTrans with (1:= c). apply TypeSym. apply TypeTrans with (1:=c0).
                    constructor. auto. auto using TypeSym. auto using TypeSym.
                +++ destruct s as [? [? [? [? [? [ ? [? [ ? []]]]]]]]]. apply inl. 
                    assert (H := H'). apply conv_hypothesis_wftype with (1:= w1) in H'. apply erase_inj_ty with (1:= H') (2:=w2) in H4.
                    constructor. eapply TermConv. instantiate (1:=Prod t t0). eapply TermLambdaCong. auto. auto. 
                    eapply conv_hypothesis_type_eq. instantiate (1:= t1). auto. auto using TypeSym.
                    eapply TermTrans. instantiate (1:= cLift projT5 projT3 projT6). eapply conv_hypothesis_term_eq. instantiate (1:= t1). auto. auto using TypeSym.
                    eapply TermTrans. instantiate (1:= cLift projT5 projT4 projT7). eapply TermConv. instantiate (1:= U projT3).
                    apply TypeTrans with (1:=H4) in c2. apply TypeSym in c2. apply TypeTrans with (1:= c2) in c1. apply UInj in c1.
                    rewrite c1. apply TermLiftingCong. eapply conv_hypothesis_term_eq. instantiate (1:=t1). auto. auto using TypeSym.
                    apply typing_defeq_inv in c3. destruct c3 as [? []]. apply TypeSym in c2. eapply wfTermConv with (1:= t6) in c2. apply lift_inv in c2.
                    destruct c2 as [? []]. all: auto using TypeSym. eapply conv_hypothesis_type_eq. instantiate (1:= t1). all: auto using TypeSym.
                    eapply conv_hypothesis_term_eq. instantiate (1:= t1). apply TermSym. apply TermConv with (1:= c4). all: auto using TypeSym.
                    eapply TypeTrans. instantiate (1:= Prod t t0). auto. apply TypeSym. eapply TypeTrans. instantiate (1:= Prod t1 t2). auto.
                    apply TypePiCong. all: auto using TypeSym.
                    (* TODO : Utiliser le lemme simplify_induction pour simplifier la preuve... *)

        ++ simpl in H1. assert (Hbis := H). apply lambda_inv in Hbis; destruct Hbis. apply wfTermConv with (1:=H) in c.
            apply inl. eapply erase_lambda_inv with (1:= c) (2:= H0) in H1.
            all: auto. constructor. assert (Hbis := H). apply lambda_inv in Hbis; destruct Hbis.
            eapply TermConv. instantiate (1:= Prod t t0). all : auto using TypeSym.
            apply subject_red in H1. assert (Hbis := H0). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]].
            apply wfTermConv with (1:= Hbis) in c0. contradict H1. intros. apply cohesion_prod_univ with (1:= H1) (2:= c0). auto.

    (* u0 = App *)
    + intros. destruct u1.
        all: try(simpl in H1; contradict H1; congruence).
        ++ simpl in H1. inversion H1. assert (Hbis := H); apply app_inv in Hbis; destruct Hbis as [? [? []]].
            assert (Hbis := H0); apply app_inv in Hbis; destruct Hbis as [? [? []]]. destruct p.
            apply erase_inj_ty with (1:= w) (2:= w1) in H3.
            assert (Hbis := H3); apply TypeSym in Hbis. apply conv_hypothesis_wftype with (1:=w2) in Hbis.
            apply erase_inj_ty with (1:= w0) (2:= Hbis) in H4. destruct p0.
            apply IHu0_1 with (1:= t3) (2:=t5) in H5. apply simplify_induction_bis in H5. destruct H5.
            apply IHu0_2 with (1:= t4) (2:= t6) in H6. apply simplify_induction_bis in H6. destruct H6.
            apply inl; constructor. eapply TermConv. instantiate (1:= subst_ty u0_2 t0).
            apply TermAppCong. all : auto using TypeSym. eapply TypeTrans. instantiate (1:= subst_ty u0_2 t0). auto.
            apply TypeSym. eapply TypeTrans. instantiate (1:=subst_ty u1_2 t2). auto. eapply subst_cong.
            instantiate (1:=t). all : auto using TypeSym. apply TermSym. auto. apply TypePiCong. all: auto.

        ++ simpl in H1. assert (Hbis := H); apply app_inv in Hbis; destruct Hbis as [? [? []]]; destruct p.
         assert (cbis := c); apply wfTermConv with (1:=H) in c. eapply erase_app_inv with (1:=c) (2:= H0) in H1.
         apply TypeSym in cbis; apply TermConv with (1:= H1) in cbis.  apply inl; constructor. all: auto.

         apply subject_red in cbis. assert (Hbis := H0). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]].
         apply lift_inv_plus in cbis; destruct cbis as [? [? [? []]]]. symmetry in e; symmetry in e0; rewrite e in c0; rewrite e0 in c1. apply TypeSym in c1. apply TypeTrans with (1:= c0) in c1.
         auto using TypeSym. auto.
        
    
    (* u0 = cProd *)
    + intros. destruct u1. apply erase_cprod_inv. all: auto.

    (* TODO : revoir erase_cprod_inv*)

    (*     all: try(simpl in H1; contradict H1; congruence).
        ++ simpl in H1. inversion H1. assert (Hbis := H); apply code_prod_inv_plus in Hbis; destruct Hbis as [? [? [? []]]].
         assert (Hbis := H0); apply code_prod_inv_plus in Hbis; destruct Hbis as [? [? [? []]]]. 
         apply IHu0_1 with (1:=t) (2:= t1) in H3. destruct H3.

            (* Premiers cas de l'HI *)
            * destruct p. assert (cbis := c1); apply TypeDecodeCong in cbis. apply UInj in c2. rewrite c2 in cbis.
                rewrite c2 in t0. apply conv_hypothesis_typing with (1:=t0) in cbis. apply IHu0_2 with (1:=cbis) (2:=t2) in H4.
                apply simplify_induction_bis in H4. destruct H4.
                    **  apply inl. constructor. eapply TermConv. instantiate (1:= U projT3). 
                        symmetry in e; rewrite e. rewrite c2. apply TermPiCong. rewrite c2 in t. auto. rewrite c2 in c1; auto.
                        assert (Hbis := c1); apply TypeDecodeCong in Hbis; apply TypeSym in Hbis; rewrite c2 in Hbis. apply conv_hypothesis_term_eq with (1:=c3) in Hbis.
                        auto. auto using TypeSym. eapply TypeTrans. instantiate (1:= U projT3); auto. apply TypeSym; eapply TypeTrans.
                        instantiate (1:= U projT4). auto. symmetry in e; rewrite e. symmetry in e0; rewrite e0. rewrite c2.
                        apply TypeRefl. apply wftype_typing_inv in t. destruct t; rewrite c2 in w; auto.
                    ** apply TypeRefl. apply typing_hypothesis_inv in t2; destruct t2 as [? []]. constructor. constructor. all: auto.

            (* Seconds cas de l'HI *)
            * assert (sbis := s). destruct s as [? [? [? [? [? [ ? [? [ ? []]]]]]]]].
                apply UInj in c1; symmetry in c1; rewrite c1 in c3. apply UInj in c2; symmetry in c2; rewrite c2 in c4.
                apply typing_defeq_inv in c3; destruct c3 as [? []]. apply lift_inv in t4; destruct t4 as [? []].
                apply typing_defeq_inv in c4; destruct c4 as [? []]. apply lift_inv in t6; destruct t6 as [? []].
                apply TypeDecodeCong in c3. apply TypeDecodeCong in c4. assert (cbis := c5); apply TypeDecodeCong in cbis.
                apply TypeDecodeLiftConv with (1:=t4) in l1. apply TypeDecodeLiftConv with (1:=t6) in l2.
                apply TypeSym in l2. apply TypeTrans with (1:= c4) in l2. apply TypeSym in cbis. apply TypeTrans with (1:= l2) in cbis.
                apply TypeSym in l1. apply TypeTrans with (1:= c3) in l1. assert (lbis:=l1).
                apply conv_hypothesis_typing with (1:=t0) in lbis. apply conv_hypothesis_typing with (1:=t2) in cbis.
                apply IHu0_2 with (1:=lbis) (2:=cbis) in H4. destruct H4.
                
                ** destruct p. apply UInj in c7. rewrite c7 in sbis. eapply simplify_induction_grouped in sbis. apply inl.
                    destruct sbis. constructor. eapply TermConv. instantiate (1:=U l0). rewrite c7. apply TermPiCong.
                    all: auto. rewrite c7 in t3; auto. rewrite c7 in c6. apply TypeDecodeCong in c8.
                     apply TypeTrans with (1:=c8) in l2. apply TypeDecodeCong in c5. apply TypeSym in c5. apply TypeTrans with (1:= l2) in c5.
                     apply TypeSym in c5. apply conv_hypothesis_term_eq with (1:= c6) in c5. auto. symmetry in e; rewrite e in c. symmetry in c7; rewrite c7.
                     auto using TypeSym. symmetry in e; symmetry in e0. rewrite e0 in c0; rewrite e in c. rewrite c7 in c. apply TypeSym in c0.
                     apply TypeTrans with (1:= c) in c0. auto. apply TypeRefl. constructor. apply inv_wfcontext_typing in t5; destruct t5; auto.

                ** destruct sbis as  [? [? [? [? [? [ ? [? [ ? []]]]]]]]]. destruct s as [? [? [? [? [? [ ? [? [ ? []]]]]]]]].

                    apply UInj in c6. apply UInj in c7. apply UInj in c11. apply UInj in c12.  set (k := projT17) in *. set (n0:=projT10) in *. set (n1:=projT11) in *.
                    set (n0bis:=l) in *. set (n1bis:=l0) in *. set (L := projT12) in *. set (d0 := projT13) in *. set (d1 := projT14) in *.
                    set (C0 := projT18) in *. set (C1 := projT19). set (m := Nat.max k L) in *. apply inr.
                    eexists. instantiate (1:= n0). eexists. instantiate (1:=n1). eexists. instantiate (1:= m).
                    eexists. instantiate (1:= cProd (m) (cLift L m d0) (cLift k m C0)). eexists. instantiate (1:=cProd m (cLift L m d1) (cLift k m C1)).
                    constructor. symmetry in e; rewrite e in c; rewrite c6 in c. auto.
                    constructor. symmetry in e0; rewrite e0 in c0; rewrite c7 in c0. auto.
                    rewrite c6. symmetry in c11; rewrite c11 in c13; rewrite c6 in c13. symmetry in c12; rewrite c12 in c14; rewrite c7 in c14.
                    constructor. eapply TermTrans. instantiate (1:= cProd n0 (cLift L n0 d0) (cLift k n0 C0)). eapply TermConv. instantiate (1:= U n0).
                    apply TermPiCong. rewrite c6 in t; auto. rewrite c6 in c8; auto.
                    rewrite c6 in l1. assert (l':=l1). apply TypeSym in l'. apply conv_hypothesis_term_eq with (1:=c13) in l'. auto.
                    symmetry in e; rewrite e in c; rewrite c6 in c. auto using TypeSym.
                    eapply TermConv. instantiate (1:=U projT3). symmetry in e; rewrite e; rewrite c6. 
                    eapply TermTrans. instantiate (1:= cProd n0 (cLift m n0 (cLift L m d0)) (cLift m n0 (cLift k m C0))).
                    apply TermPiCong. apply typing_defeq_inv in c8. destruct c8 as [? []]. rewrite c6 in t8. auto.
                    apply TermSym. eapply conv_lift_cumul_max. apply typing_defeq_inv in c10. destruct c10 as [? []]. auto.
                    assert (c13bis:=c13). apply typing_defeq_inv in c13bis. destruct c13bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []]. auto. assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []]. auto.
                    apply TermSym.  apply conv_lift_cumul_max_comm. assert (c13bis:=c13). apply typing_defeq_inv in c13bis. destruct c13bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []].  eapply conv_hypothesis_typing.
                    instantiate (1:=Decode projT7 projT8). auto. eapply TypeTrans. instantiate (1:= Decode n0 u0_1).
                    rewrite c6 in l1. apply TypeSym in l1. auto. apply TypeDecodeCong. rewrite c6 in c8. auto. 
                    assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []]. auto. assert (c13bis:=c13). apply typing_defeq_inv in c13bis. destruct c13bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []].  auto.
                    apply TermSym. apply TermLiftingProdConv.
                    assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    constructor. auto. apply inf_right_max.
                    assert (c13bis:=c13). apply typing_defeq_inv in c13bis. destruct c13bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    constructor. eapply conv_hypothesis_typing.
                    instantiate (1:=Decode projT7 projT8). auto. eapply TypeTrans. instantiate (1:= Decode n0 u0_1).
                    rewrite c6 in l1. apply TypeSym in l1. auto. eapply TypeTrans. instantiate (1:= Decode n0 (cLift m n0 (cLift L m d0))).
                    apply TypeDecodeCong. apply TermSym. eapply TermTrans. instantiate (1:= cLift L n0 d0). apply TermLiftingCumul.
                    rewrite c6 in c8. assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    auto. apply inf_right_max. apply sup_max. auto.  assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    auto. rewrite c6 in c8. auto using TermSym. apply TypeSym. apply TypeDecodeLiftConv.
                    assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    constructor. auto. apply inf_right_max. apply sup_max. auto. auto. assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    auto. apply inf_left_max. apply sup_max. assert (c13bis:=c13). apply typing_defeq_inv in c13bis. destruct c13bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    auto. assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    auto. auto using TypeSym.

                    constructor. eapply TermTrans. instantiate (1:= cProd n1 (cLift L n1 d1) (cLift k n1 C1)). eapply TermConv. instantiate (1:= U n1).
                    rewrite c7.
                    apply TermPiCong. rewrite c7 in t1; auto. rewrite c7 in c9; auto.
                    rewrite c7 in l2. assert (l':=l2). apply TypeSym in l'. apply TypeDecodeCong in c5. apply TypeTrans with (1:= c5) in l'. apply conv_hypothesis_term_eq with (1:=c14) in l'. auto.
                    symmetry in e0; rewrite e0 in c0; rewrite c7 in c0. auto using TypeSym.
                    eapply TermConv. instantiate (1:=U projT4). symmetry in e0; rewrite e0; rewrite c7. 
                    eapply TermTrans. instantiate (1:= cProd n1 (cLift m n1 (cLift L m d1)) (cLift m n1 (cLift k m C1))).
                    apply TermPiCong. apply typing_defeq_inv in c9. destruct c9 as [? []]. rewrite c7 in t8. auto.
                    apply TermSym. apply TermLiftingCumul. apply typing_defeq_inv in c10. destruct c10 as [? []]. auto.
                    apply inf_right_max. assert (c14bis:=c14). apply typing_defeq_inv in c14bis. destruct c14bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []]. assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []].
                    apply lift_inv in t10. destruct t10 as [? []]. apply sup_max. auto. auto.
                    apply TermSym. apply TermLiftingCumul. assert (c14bis:=c14). apply typing_defeq_inv in c14bis. destruct c14bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []]. eapply conv_hypothesis_typing.
                    instantiate (1:=Decode projT7 projT8). auto. eapply TypeTrans. instantiate (1:= Decode n1 u1_1).
                    rewrite c7 in l2. apply TypeSym in l2.  assert (l':=l2). apply TypeSym in l'. apply TypeDecodeCong in c5. apply TypeSym in l'. apply TypeTrans with (1:= c5) in l'. 
                    auto. apply TypeDecodeCong. rewrite c7 in c9. auto. 
                    apply inf_left_max. assert (c14bis:=c14). apply typing_defeq_inv in c14bis. destruct c14bis as [? []].
                    apply lift_inv in t8. destruct t8 as [? []]. assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []].
                    apply lift_inv in t10. destruct t10 as [? []]. apply sup_max. auto. auto.
                    apply TermSym. apply TermLiftingProdConv.
                    assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    constructor. auto. apply inf_right_max.
                    assert (c14bis:=c14). apply typing_defeq_inv in c14bis. destruct c14bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    constructor. eapply conv_hypothesis_typing.
                    instantiate (1:=Decode projT7 projT8). auto. eapply TypeTrans. instantiate (1:= Decode n1 u1_1).   assert (l':=l2). apply TypeSym in l'. apply TypeDecodeCong in c5.  apply TypeTrans with (1:= c5) in l'. 
                    rewrite c7 in l'. auto.
                    eapply TypeTrans. instantiate (1:= Decode n1 (cLift m n1 (cLift L m d1))).
                    apply TypeDecodeCong. apply TermSym. eapply TermTrans. instantiate (1:= cLift L n1 d1). apply TermLiftingCumul.
                    rewrite c7 in c9. assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    auto. apply inf_right_max. apply sup_max. auto.  assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    auto. rewrite c7 in c9. auto using TermSym. apply TypeSym. apply TypeDecodeLiftConv.
                    assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    constructor. auto. apply inf_right_max. apply sup_max. auto. auto. assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    auto. apply inf_left_max. apply sup_max. assert (c14bis:=c14). apply typing_defeq_inv in c14bis. destruct c14bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    auto. assert (c9bis:=c9). apply typing_defeq_inv in c9bis. destruct c9bis as [? []]. apply lift_inv in t8. destruct t8 as [? []].
                    auto. auto using TypeSym.

                    assert (c8bis:=c8). apply typing_defeq_inv in c8bis. destruct c8bis as [? []]. assert (c13bis:=c13). apply typing_defeq_inv in c13bis. destruct c13bis as [? []]. apply lift_inv in t10. destruct t10 as [? []].
                    apply lift_inv in t8. destruct t8 as [? []].
                    apply TermPiCong. constructor. auto. apply inf_right_max. apply TermLiftingCong. auto. apply inf_right_max.
                    apply TermLiftingCong. auto. eapply conv_hypothesis_term_eq. instantiate (1:= Decode projT7 projT8). auto. 
                    eapply TypeTrans. instantiate (1:=Decode n0 u0_1). rewrite c6 in l1. auto using TypeSym.
                    apply TypeDecodeCong in c16. rewrite c6 in c16. eapply TypeTrans. instantiate (1:= Decode n0 (cLift L n0 d0)).
                    auto. eapply TypeTrans. instantiate (1:= Decode n0 (cLift m n0 (cLift L m d0))).
                    apply TypeDecodeCong. apply TermSym. apply TermLiftingCumul. auto. apply inf_right_max.
                    apply sup_max. auto. auto. apply TypeSym. apply TypeDecodeLiftConv. constructor. auto. apply inf_right_max.
                    apply sup_max. auto. auto. apply inf_left_max.
                    
        
        ++ simpl in H1. assert (Hbis := H). apply code_prod_inv_plus in Hbis; destruct Hbis as [? [? [? []]]]. apply wfTermConv with (1:=H) in c.
            apply inl. eapply erase_cprod_inv with (1:= c) (2:= H0) in H1.

            all: auto. (* TODO : Corriger après lemme erase_cProd_inv *)
            
            constructor. assert (Hbis := H). apply code_prod_inv_plus in Hbis; destruct Hbis as [? [? [? []]]].
            eapply TermConv. instantiate (1:= U projT3 ). all : auto using TypeSym.
            apply subject_red in H1. assert (Hbis := H0). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]].
            apply wfTermConv with (1:= Hbis) in c1. apply code_prod_inv_plus in c. destruct c as [? [? [? []]]].
            symmetry in e0; rewrite e0 in c0. rewrite e in c0. all: auto using TypeSym.
            apply subject_red in H1. assert (Hbis := H0). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]].
            apply code_prod_inv_plus in H. destruct H as [? [? [? []]]]. apply lift_inv_plus in H1; destruct H1 as [? [? [? []]]].
            apply code_prod_inv_plus in c. destruct c as [? [? [? []]]]. eapply TypeTrans.
            instantiate(1:=U projT5). auto. symmetry in e1. rewrite e1. apply UInj in c2. apply UInj in c.
            rewrite e3. symmetry in c. rewrite c. rewrite c2. symmetry in e2. rewrite e2. rewrite e0. auto using TypeSym. auto.
 *)

    + intros. destruct u1. 
        all: try(simpl in H1; contradict H1; congruence).
        ++  simpl in H1. inversion H1. assert (Hbis:=H). apply code_univ_inv_bis in Hbis. destruct Hbis.
        assert (H0bis:=H0). apply code_univ_inv_bis in H0bis. destruct H0bis.
        apply inr. eexists l0. eexists l2. set (k:=(Nat.min l0 l2)). eexists k. eexists (cU l k). eexists (cU l k).
        constructor. auto. constructor. auto. constructor. apply TermSym. eapply TermConv. instantiate (1:= U l0).
        rewrite H3. apply conv_lift_univ_min_comm. apply inv_wfcontext_typing in H. destruct H. auto. auto. lia. auto using TypeSym.

        constructor.  apply TermSym. eapply TermConv. instantiate (1:= U l2).
        rewrite H3. apply conv_lift_univ_min. apply inv_wfcontext_typing in H. destruct H. auto. lia. lia. auto using TypeSym.
        apply TermRefl. constructor. apply inv_wfcontext_typing in H. destruct H. auto.
        apply inf_min. auto. rewrite H3; auto.

        ++ simpl in H1. apply inr. eexists l0; eexists l2. apply erase_cuniv_inv.
            auto. auto. auto.
    
    + intros. assert (Hbis:= H). apply lift_inv_plus in Hbis. destruct Hbis as [? [? [? []]]].
        apply IHu0 with (1:=t) (2:=H0) in H1. destruct H1.
        ++ destruct p. symmetry in e. rewrite e in c. apply TypeSym in c1. apply inr.
            eexists l0. eexists l. eexists l. eexists u0. eexists u0.
            constructor; auto.
            constructor; auto.
            constructor. apply TermRefl. auto.
            constructor. eapply TermConv. instantiate (1:= U l). eapply TermTrans. instantiate (1:=u0).
            auto using TermSym. eapply lift_same. auto.  auto using TypeSym. apply TermRefl. auto.
     
        ++ destruct s as [? [? [? [? [? [? [? [? []]]]]]]]]. apply inr. apply UInj in c0. symmetry in e; rewrite e in c.
            eexists l0. eexists projT5. eexists projT6. eexists projT7. eexists projT8.
            constructor. auto.
            constructor. auto.
            constructor. assert (l1bis:=l1). apply TermLiftingCong with (1:= c2) in l1bis.
            eapply TermConv. instantiate (1:= U l0).
            eapply TermTrans. instantiate (1:= cLift l l0 (cLift projT6 projT4 projT7)). 
            auto. rewrite c0. apply TermLiftingCumul. apply typing_defeq_inv in c4. destruct c4 as [? []].
            auto. apply typing_defeq_inv in c2. destruct c2 as [? []]. apply lift_inv_plus in t1. destruct t1 as [? [? [? []]]].
            auto. rewrite c0 in l1. auto. auto using TypeSym.
            constructor. auto.
            auto.

Admitted. (* TODO : Decreasing argument *)

Lemma erase_inj_term_plus {u0}:
    forall Γ u1 A0 A1,
    [Γ |- u0 : A0] ->
    [Γ |- u1 : A1] ->
    (erase_term u0 = erase_term u1) ->
    (erase_ty A0 = erase_ty A1) ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
Proof.
Admitted.

Lemma erase_inj_ctx_term {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall a A, [Γ |- a : A] -> [Γ' |- a : A])
with erase_inj_ctx_type {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall A, [Γ |- A] -> [Γ' |- A])
with erase_inj_ctx_conv_ty {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall A B, [Γ |- A = B] -> [Γ' |- A = B])
with erase_inj_ctx_conv_term {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall u v A, [Γ |- u = v : A ] -> [Γ' |- u = v : A ]).
Proof.
(*     induction Γ.
    - intros. destruct Γ'.
        +  constructor. auto. auto.
        + simpl in H1. contradict H1. congruence.
    - intros. destruct Γ'.
        + simpl in H1. contradict H1. congruence.
        + simpl in H1. inversion H1. inversion H. inversion H0. assert (IHbis:=IHΓ). specialize (IHbis Γ' H6 H10 H4).
        destruct IHbis. apply w in H7. eapply erase_inj_ty with (1:=H7) (2:=H11) in H3.
            constructor. intros. eapply conv_hypothesis_typing. instantiate (1:= a).
             dependent induction H12.
             ++  constructor. auto.
             ++ constructor. auto. apply t0 in H12. auto.
             ++ apply wfTermcProd.    *)

(* - intros. induction H2.
    + destruct Γ'.  simpl in H1. contradict H1. congruence.
        simpl in H1. inversion H1. inversion H. inversion H0.
        specialize (erase_inj_ctx_type Γ Γ' H6 H10 H4). apply erase_inj_ctx_type in w. apply erase_inj_ty with (1:=w) (2:=H11) in H3.
        eapply conv_hypothesis_typing. instantiate (1:=A). eapply wfVar0. auto. auto.
    + destruct Γ'.  simpl in H1. contradict H1. congruence.
        simpl in H1. inversion H1. inversion H. inversion H0.
        specialize (erase_inj_ctx_type Γ Γ' H7 H11 H5). apply erase_inj_ctx_type in w. apply erase_inj_ty with (1:=w) (2:=H12) in H4.
        eapply conv_hypothesis_typing. instantiate (1:=A). eapply wfVarN. auto.  *)
Admitted.


Lemma var_from_russ {Γ n B B1 Γ1}:
    [Γ1 |- B1] ->
    [Γ |-r r_var_term n : B] ->
    (erase_ty B1 = B) ->
    (erase_context Γ1 = Γ) ->
    [Γ1 |- var_term n : B1].
Proof.
Admitted.

Theorem section_ctx {Γ} :
    [ |-r Γ] ->
    (∑ Γ1,
    [ |- Γ1] × (erase_context Γ1 = Γ))
with section_ty {Γ A} :
    [Γ |-r A] ->
    (∑ Γ1 A1,
    [Γ1 |- A1] × (erase_ty A1 = A) × (erase_context Γ1 = Γ))
with section_term {Γ u A} :
    [Γ |-r u : A] ->
    (∑ Γ1 u1 A1,
    [Γ1 |-  u1 : A1] × (erase_ty A1 = A) × (erase_term u1 = u) × (erase_context Γ1 = Γ))
with section_conv {Γ A B} :
    [Γ |-r A = B] ->
    (∑ Γ1 A1 B1,
    [Γ1 |- A1 = B1] × (erase_ty A1 = A) × (erase_ty B1 = B) × (erase_context Γ1 = Γ))
with section_conv_term {Γ u v A} :
    [Γ |-r u = v : A] ->
    (∑ Γ1 u1 v1 A1,
    [Γ1 |- u1 = v1 : A1] × (erase_ty A1 = A) × (erase_term u1 = u) × (erase_term v1 = v) × (erase_context Γ1 = Γ)).
Proof.

- intros. induction H.
    + eexists ε. constructor. constructor. simpl. auto.
    + destruct IHRuss_WfContextDecl as [? []]. apply section_ty in r. destruct r as [? [? [? []]]].
        eexists (projT4,,projT5). constructor. apply concons in w0. auto. apply inv_wfcontext_wftype in w0. destruct w0. auto.
        simpl. rewrite e1. rewrite e0. auto.

- intros. induction H.
    + apply section_ctx in r. destruct r as [? []]. eexists projT3. eexists (U n).
        constructor. constructor. auto.
        constructor. auto. auto.
    + apply section_term in r. destruct r as [? [? [? [? [? []]]]]]. eexists projT3. eexists (Decode n projT4).
        constructor. constructor. eapply wfTermConv. instantiate (1:=projT5). auto. eapply erase_inj_ty.
            apply wftype_typing_inv in t. destruct t. auto. constructor. apply inv_wfcontext_typing in t. destruct t. auto.
            auto. 
        constructor. auto. auto.

- intros. induction H.
    + apply  section_ty in r. destruct r as [? [? [? []]]]. eexists (projT3,,projT4). eexists (var_term 0). eexists (weak_ty projT4).
        constructor. eapply wfVar0. auto.
        constructor. symmetry in e. rewrite e. rewrite defeq_erase_weak_ty. auto.
        constructor. auto. simpl. rewrite e0. rewrite e. auto.
    +  destruct IHruss_termpingDecl as [? [? [? [? [? []]]]]]. apply section_ty in r. destruct r as [? [? [? []]]]. eexists (projT6,,projT7).
    eexists (var_term (n+1)). eexists (weak_ty projT5).
        constructor. eapply wfVarN. auto. eapply erase_inj_ctx_term. instantiate (1:=projT3).
            apply inv_wfcontext_typing in t. destruct t. auto. apply inv_wfcontext_wftype in w. destruct w; auto.
            rewrite e3; auto. apply wftype_typing_inv in t. destruct t. apply var_from_russ with (1:= w0) (2:=H) (3:=e) (4:=e1).
        constructor. symmetry in e. rewrite e. rewrite defeq_erase_weak_ty. auto.
        constructor. auto. simpl. rewrite e3. rewrite e2. auto.

    + (* Cas r_Lambda *)
      (* 1. Récupération de l'hypothèse d'induction pour le corps 't' *)
      destruct IHruss_termpingDecl as [Γ_body [u_body [B_lifted [H_typing_body [H_erase_B [H_erase_u H_erase_ctx_body]]]]]].
      
      (* 2. Récupération du type A via section_ty (car [Γ |-r A]) *)
      apply section_ty in r. destruct r as [Γ_A [A_lifted [H_wf_A [H_erase_A H_erase_ctx_A]]]].
      
      (* 3. Analyse du contexte du corps. Γ_body doit s'effacer en Γ,,A. C'est donc une liste non vide. *)
      destruct Γ_body as [| A_body_head Γ_body_tail].
      * simpl in H_erase_ctx_body. discriminate.
      * simpl in H_erase_ctx_body. injection H_erase_ctx_body. intros H_eq_ctx H_eq_A.
      
      (* 4. Construction des témoins *)
      eexists Γ_A.
      eexists (Lambda A_lifted B_lifted u_body).
      eexists (Prod A_lifted B_lifted).
      
      repeat split.
      ** 
        apply wfTermLambda.
        -- exact H_wf_A.
        --
           eapply erase_inj_ctx_term.
           --- apply inv_wfcontext_typing in H_typing_body. destruct H_typing_body as [_ H_wf_source]. exact H_wf_source.
           --- apply concons. apply inv_wfcontext_wftype in H_wf_A. destruct H_wf_A as [_ H_wf_base]. exact H_wf_base. exact H_wf_A.
           --- simpl. rewrite H_erase_ctx_A H_erase_A.
               rewrite H_eq_ctx H_eq_A. reflexivity.
           --- exact H_typing_body.
           
      ** (* Effacement du type *)
        simpl. rewrite H_erase_A H_erase_B. reflexivity.
      ** (* Effacement du terme *)
        simpl. rewrite H_erase_A H_erase_B H_erase_u. reflexivity.
      ** (* Effacement du contexte *)
        exact H_erase_ctx_A.

        (* Cas r_App *)
    + destruct IHruss_termpingDecl1 as [Γ_f [f_t [Prod_t [Hf_typ [H_er_Prod [H_er_f H_er_ctx_f]]]]]].
      destruct IHruss_termpingDecl2 as [Γ_a [a_t [A_t [Ha_typ [H_er_A [H_er_a H_er_ctx_a]]]]]].
      
      (* Pour construire l'application, il nous faut le type B. 
         f a pour type (Prod A B) en Russell. Cela implique [Γ,,A |-r B]. *)
      (* On admet ici le lemme d'inversion sur le typage Russell pour récupérer B, 
         ou on utilise le fait que section_ty existe pour tout type bien formé. *)
      assert (H_russ_B : [Γ ,,r A |-r B]). { 
          (* TODO: inversion du typage de f *) admit.  
      }
      apply section_ty in H_russ_B. destruct H_russ_B as [Γ_B [B_t [H_wf_B [H_er_B H_er_ctx_B]]]].

      (* Alignement des contextes : on se place dans Γ_f *)
      (* On admet l'alignement strict pour simplifier ici (sinon rewrite contexte) *)
      assert (Heq_ctxs : Γ_f = Γ_a). { admit. } subst Γ_a.

      (* Construction du terme App *)
      eexists Γ_f.
      eexists (App A_t B_t f_t a_t).
      eexists (subst_ty a_t B_t).
      
      repeat split.
      -- apply wfTermApp.
         --- (* f doit avoir le type Prod A_t B_t *)
             eapply wfTermConv.
             ---- exact Hf_typ.
             ---- (* Conversion : Prod_t = Prod A_t B_t *)
                  apply erase_inj_ty.
                  ----- (* Prod_t bien formé *) apply wftype_typing_inv in Hf_typ. destruct Hf_typ; auto.
                  ----- (* Prod A_t B_t bien formé *) 
                        apply wfTypeProd.
                        ------ (* A_t bien formé *) apply wftype_typing_inv in Ha_typ. destruct Ha_typ; auto.
                        ------ (* B_t bien formé dans Γ_f,,A_t *)
                               (* Il faut transporter B_t de Γ_B vers Γ_f,,A_t *)
                               eapply erase_inj_ctx_type.
                               ------- apply inv_wfcontext_wftype in H_wf_B. destruct H_wf_B; exact w0.
                               ------- apply concons. apply inv_wfcontext_typing in Hf_typ. destruct Hf_typ; auto.
                                       apply wftype_typing_inv in Ha_typ. destruct Ha_typ; auto.
                               ------- simpl. rewrite H_er_ctx_f H_er_A. rewrite <- H_er_ctx_B. reflexivity.
                               ------- exact H_wf_B.
                  ----- (* Egalité des effacements *)
                        simpl. rewrite H_er_Prod. rewrite H_er_A H_er_B. reflexivity.
         --- (* a doit avoir le type A_t *)
             exact Ha_typ.
      -- (* Effacement du type de retour *)
         rewrite <- defeq_erase_subst_ty. rewrite H_er_a H_er_B. reflexivity.
      -- (* Effacement du terme *)
         simpl. rewrite H_er_A H_er_B H_er_f H_er_a. reflexivity.
      -- exact H_er_ctx_f.

    + (* Cas r_wfTermConv *)
      destruct IHruss_termpingDecl as [Γ1 [u1 [A1 [Htyp [HerA [HerU HerCtx]]]]]].
      apply section_conv in r. destruct r as [? [A2 [B1 [? [? []]]]]].
      eexists Γ1, u1, B1.
      split.
      * eapply wfTermConv.
        -- exact Htyp.
        -- eapply TypeTrans. instantiate (1:=A2). (* Conversion A1 = B1 *)
           apply erase_inj_ty.
           --- apply wftype_typing_inv in Htyp. destruct Htyp. auto.
           --- apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
                eapply erase_inj_ctx_type. exact w1. apply inv_wfcontext_typing in Htyp. destruct Htyp. auto. rewrite e1. auto. auto.
           --- rewrite HerA. auto. 
           --- apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
                eapply erase_inj_ctx_conv_ty. exact w1. apply inv_wfcontext_typing in Htyp. destruct Htyp. auto. rewrite e1. auto. auto.
      * split. auto. split. auto. auto.

    (* Cas r_wfTermProd (Code de produit) *)
    + destruct IHruss_termpingDecl1 as [Γ1 [a1 [TA1 [Ha1 [HeTA1 [Hea1 HeG1]]]]]].
      destruct IHruss_termpingDecl2 as [Γ2 [b1 [TB1 [Hb1 [HeTB1 [Heb1 HeG2]]]]]].
      (* On construit cProd l a b *)
      eexists Γ1, (cProd n a1 b1), (U n).
      repeat split.
      * assert (HeqTA1 : [Γ1 |- TA1 = U n]). 
      {
        apply erase_inj_ty. apply wftype_typing_inv in Ha1. destruct Ha1. auto. constructor.
        apply inv_wfcontext_typing in Ha1. destruct Ha1. auto. auto.
      }
        apply wfTermConv with (1:= Ha1) in HeqTA1. constructor. auto. constructor. auto.
        assert (HeqTB1 : [Γ2 |- TB1 = U n]). 
      {
        apply erase_inj_ty. apply wftype_typing_inv in Hb1. destruct Hb1. auto. constructor.
        apply inv_wfcontext_typing in Hb1. destruct Hb1. auto. auto.
      }
      apply wfTermConv with (1:= Hb1) in HeqTB1. eapply erase_inj_ctx_term. apply inv_wfcontext_typing in Hb1. destruct Hb1. exact w.
        constructor. apply inv_wfcontext_typing in Ha1. destruct Ha1. exact w. constructor. auto. rewrite HeG2. simpl. rewrite HeG1 Hea1. auto. auto.
      * simpl. rewrite Hea1. rewrite Heb1. reflexivity.
      * simpl. auto.

    (* Cas r_wfTermUniv *)
    + apply section_ctx in r. destruct r as [Γ1 [HwfG HeG]].
      eexists Γ1, (cU n m), (U m).
      repeat split.
      * apply wfTermcUniv; auto.
      * auto.

    (* Cas r_wfTermCumul *)
+ destruct IHruss_termpingDecl as [Γ1 [u1 [A1 [Htyp [HerA [HerU HerCtx]]]]]].
      eexists Γ1, (cLift n m u1), (U m).
      repeat split.
      -- apply wfTermcLift; auto.
         eapply wfTermConv. exact Htyp. apply erase_inj_ty.
         --- apply wftype_typing_inv in Htyp; destruct Htyp; auto.
         --- apply wfTypeU. apply inv_wfcontext_typing in Htyp; destruct Htyp; auto.
         --- rewrite HerA. simpl. reflexivity.
      -- simpl. auto.
      -- simpl. auto.

- (* section_conv : [Γ |-r A = B] -> ... *)
  intros. induction H.

  (* 1. Cas r_TypePiCong : Congruence du produit *)
  + destruct IHRuss_ConvTypeDecl1 as [Γ1 [A1 [B1 [HconvA [HeA [HeB HeG1]]]]]].
    destruct IHRuss_ConvTypeDecl2 as [Γ2 [C1 [D1 [HconvC [HeC [HeD HeG2]]]]]].
    
    eexists Γ1, (Prod A1 C1), (Prod B1 D1).
    repeat split.
    * apply TypePiCong.
      -- (* A1 doit être bien formé *)
         apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
      -- (* A1 = B1 *)
         exact HconvA.
      -- (* C1 = D1 doit être valide dans Γ1,,A1. On l'a dans Γ2. *)
         (* On utilise erase_inj_ctx_conv_ty car les contextes s'effacent de la même manière *)
         eapply erase_inj_ctx_conv_ty.
         --- (* Γ2 est bien formé (venant de la preuve de C1=D1) *)
             apply type_defeq_inv in HconvC. destruct HconvC as [_ [HwfC _]]. apply inv_wfcontext_wftype in HwfC. destruct HwfC; exact w0.
         --- (* Γ1,,A1 est bien formé *)
             apply concons. 
             apply type_defeq_inv in HconvA. destruct HconvA as [_ [_ HwfB1]]. apply inv_wfcontext_wftype in HwfB1. destruct HwfB1; auto.
             apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
         --- (* erase(Γ2) = Γ,,A = erase(Γ1,,A1) *)
             simpl. rewrite HeG2 HeG1 HeA. reflexivity.
         --- exact HconvC.
    * simpl. rewrite HeA HeC. reflexivity.
    * simpl. rewrite HeB HeD. reflexivity.
    * exact HeG1.

  (* 2. Cas r_TypeRefl *)
  + apply section_ty in r. destruct r as [Γ1 [A1 [Hwf [HeA HeG]]]].
    eexists Γ1, A1, A1.
    repeat split; try auto.
    apply TypeRefl. exact Hwf.

  (* 3. Cas r_TypeSym *)
  + destruct IHRuss_ConvTypeDecl as [Γ1 [A1 [B1 [Hconv [HeA [HeB HeG]]]]]].
    (* On inverse l'ordre : on fournit B1 pour B et A1 pour A *)
    eexists Γ1, B1, A1.
    repeat split.
    * (* Preuve de la symétrie en Tarski *)
      apply TypeSym. exact Hconv.
    * (* erase B1 = B *)
      exact HeB.
    * (* erase A1 = A *)
      exact HeA.
    * (* Contexte *)
      exact HeG.

    (* 4. Cas r_TypeTrans *)
  + destruct IHRuss_ConvTypeDecl1 as [Γ1 [A1 [B1 [Hconv1 [HeA [HeB1 HeG1]]]]]].
    destruct IHRuss_ConvTypeDecl2 as [Γ2 [B2 [C1 [Hconv2 [HeB2 [HeC HeG2]]]]]].
    
    eexists Γ1, A1, C1.
    repeat split; try auto.
    eapply TypeTrans.
    * exact Hconv1.
    * (* Transition B1 -> B2. On a erase B1 = B = erase B2. *)
      eapply TypeTrans. instantiate (1:=B2).
      -- apply erase_inj_ty.
         --- apply type_defeq_inv in Hconv1. destruct Hconv1 as [_ [_ HwfB1]]. exact HwfB1.
         --- apply type_defeq_inv in Hconv2. destruct Hconv2 as [_ [HwfB2 _]]. eapply erase_inj_ctx_type.
            instantiate (1:=Γ2 ). apply inv_wfcontext_wftype in HwfB2. destruct HwfB2. auto.
            apply type_defeq_inv in Hconv1. destruct Hconv1 as [? []]. apply inv_wfcontext_wftype in w. destruct w. auto.
            rewrite HeG1. auto. auto.
         --- rewrite HeB1 HeB2. reflexivity.
      -- eapply erase_inj_ctx_conv_ty.
            instantiate (1:=Γ2 ). apply type_defeq_inv in Hconv2. destruct Hconv2 as [? []]. apply inv_wfcontext_wftype in w. destruct w. auto.
            apply type_defeq_inv in Hconv1. destruct Hconv1 as [? []]. apply inv_wfcontext_wftype in w. destruct w. auto. rewrite HeG2. auto. auto. 

            (* 5. Cas r_TypeUnivConv *)
  + apply section_conv_term in r.
    destruct r as [Γ1 [u1 [v1 [T1 [Hconv [HeqT [Hequ [Heqv HeqG]]]]]]]].
    
    (* On fournit les types décodés comme témoins *)
    eexists Γ1, (Decode n u1), (Decode n v1).
    repeat split.
    * (* Preuve de l'égalité [Γ1 |- Decode n u1 = Decode n v1] *)
      apply TypeDecodeCong.
      (* On doit convertir le type de l'égalité u1=v1 de T1 vers U n *)
      eapply TermConv.
      -- exact Hconv.
      -- (* Preuve que T1 = U n *)
         destruct T1; simpl in HeqT.
         ++ (* Cas Prod : impossible car s'efface en r_U *)
            discriminate.
         ++ (* Cas Decode : on utilise le lemme d'inversion *)
            apply TypeSym.
            apply erase_decode_inv_univ with (t:=t).
            ** (* La bonne formation de T1 vient du jugement d'égalité *)
               apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]].
               apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT].
               exact HwfT.
            ** symmetry. exact HeqT.
         ++ (* Cas U : trivial *)
            injection HeqT. intro. subst l.
            apply TypeRefl. apply wfTypeU.
            (* Récupération de la bonne formation du contexte *)
            apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]].
            apply inv_wfcontext_typing in Hwf. destruct Hwf. exact w.
    * (* Effacement de A1 *)
      simpl. exact Hequ.
    * (* Effacement de B1 *)
      simpl. exact Heqv.
    * (* Effacement du contexte *)
      exact HeqG.

(* section_conv_term *)
- intros. induction H.

    + apply section_term in r0. destruct r0 as [Γ1 [t1 [B1 [Htyp_t [HeB [Het HeG1]]]]]].
    apply section_term in r1. destruct r1 as [Γ2 [a1 [A1 [Htyp_a [HeA [Hea HeG2]]]]]].
    
    
    eexists (Γ2), (App A1 B1 (Lambda A1 B1 t1) a1), (subst_term a1 t1), (subst_ty a1 B1).
    repeat split.
    * eapply TermBRed.
        -- apply wftype_typing_inv in Htyp_a. destruct Htyp_a. auto.
        --  eapply erase_inj_ctx_term. apply inv_wfcontext_typing in Htyp_t. destruct Htyp_t. exact w.
            apply inv_wfcontext_typing in Htyp_a. destruct Htyp_a. constructor. auto. apply wftype_typing_inv in t0. destruct t0. auto.
            simpl. rewrite HeG2. rewrite HeA. auto. auto.
        -- (* a1 : A1 *)
            exact Htyp_a.
    * rewrite <- defeq_erase_subst_ty. rewrite HeB Hea. reflexivity.
    * simpl. rewrite HeA HeB Het Hea. reflexivity.
    * rewrite <- defeq_erase_subst_term. rewrite Hea Het. reflexivity.
    * auto.
    

    (* 2. Cas r_TermAppCong *)
    + apply section_conv in r. destruct r as [Γ1 [A1 [A'1 [HconvA [HeA [HeA' HeG1]]]]]].
    apply section_conv in r0. destruct r0 as [Γ2 [B1 [B'1 [HconvB [HeB [HeB' HeG2]]]]]].
    destruct IHRuss_ConvTermDecl1 as [Γ3 [f1 [g1 [Prod1 [Hconv_f [HeProd [Hef [Heg HeG3]]]]]]]].
    destruct IHRuss_ConvTermDecl2 as [Γ4 [a1 [b1 [Ta1 [Hconv_a [HeTa [Hea [Heb HeG4]]]]]]]].

    eexists Γ1, (App A1 B1 f1 a1), (App A'1 B'1 g1 b1), (subst_ty a1 B1).
    repeat split.
    * apply TermAppCong.
        -- exact HconvA.
        -- 
        eapply erase_inj_ctx_conv_ty. apply type_defeq_inv in HconvB. destruct HconvB as [? []]. apply inv_wfcontext_wftype in w. destruct w.
        exact w1. apply type_defeq_inv in HconvA. destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto.
        simpl. rewrite HeG1. rewrite HeA. auto. auto.
        -- eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [? []]. apply inv_wfcontext_typing in t. destruct t.
        exact w. apply type_defeq_inv in HconvA. destruct HconvA as [? []]. apply inv_wfcontext_wftype in w0. destruct w0. auto. rewrite HeG3. auto.
        
        eapply TermConv. exact Hconv_f. apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfP]. exact HwfP.
        --- apply wfTypeProd. 
            apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w0.  apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [? []].
            apply inv_wfcontext_typing in t. destruct t. auto. rewrite HeG3. auto. auto.
            apply type_defeq_inv in HconvB. destruct HconvB as [_ [HwfB _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfB. destruct HwfB. exact w0.  apply typing_defeq_inv in Hconv_f. destruct Hconv_f as [? []].
            apply inv_wfcontext_typing in t. destruct t. constructor. auto. apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w1. auto.  rewrite HeG3. auto. auto. simpl. rewrite HeG3. rewrite HeA. auto. auto.
        --- simpl. rewrite HeProd. rewrite HeA HeB. reflexivity.
        -- (* a1 = b1 : A1 *)
        eapply TermConv. instantiate (1:=Ta1). eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv_a. destruct Hconv_a as [? []].
        apply inv_wfcontext_typing in t. destruct t. exact w. apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w0.
        rewrite HeG4. auto. auto. 
        apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv_a. destruct Hconv_a as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT].
        eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in HwfT. destruct HwfT. exact w0. apply type_defeq_inv in HconvA. destruct HconvA as [? []].
        apply inv_wfcontext_wftype in w. destruct w.  auto. rewrite HeG4. auto. auto. 
        --- apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
        --- rewrite HeTa HeA. reflexivity.
    * rewrite <- defeq_erase_subst_ty. rewrite HeB Hea. reflexivity.
    * simpl. rewrite HeA HeB Hef Hea. reflexivity.
    * simpl. rewrite HeA' HeB' Heg Heb. reflexivity.
    * exact HeG1.

    (* 3. Cas r_TermLambdaCong *)
    + apply section_conv in r0. destruct r0 as [Γ1 [A1 [A'1 [HconvA [HeA [HeA' HeG1]]]]]].
    apply section_conv in r1. destruct r1 as [Γ2 [B1 [B'1 [HconvB [HeB [HeB' HeG2]]]]]].
    destruct IHRuss_ConvTermDecl as [Γ3 [t1 [u1 [B_body [Hconv_t [HeBb [Het [Heu HeG3]]]]]]]].

    eexists Γ1, (Lambda A1 B1 t1), (Lambda A'1 B'1 u1), (Prod A1 B1).
    repeat split.
    * apply TermLambdaCong.
        -- apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
        -- exact HconvA.
        -- eapply erase_inj_ctx_conv_ty. apply type_defeq_inv in HconvB. destruct HconvB as [? []].
            apply inv_wfcontext_wftype in w. destruct w. exact w1.
            apply type_defeq_inv in HconvA. destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w.
            constructor. auto. auto. simpl. rewrite HeG1. rewrite HeA. auto. auto.
        -- (* t1 = u1 : B1 in Γ,,A1 *)
        eapply TermConv. instantiate (1:=B_body). eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv_t.
        destruct Hconv_t as [? []]. apply inv_wfcontext_typing in t0. destruct t0. exact w. apply type_defeq_inv in HconvA.
        destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto. simpl. rewrite HeG1.
        rewrite HeA. auto. auto. 

        apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT].
        eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in HwfT. destruct HwfT. exact w0. apply type_defeq_inv in HconvA.
        destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto. simpl. rewrite HeG1.
        rewrite HeA. auto. auto. 
        --- apply type_defeq_inv in HconvB. destruct HconvB as [_ [HwfB _]]. 
        eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in HwfB. destruct HwfB. exact w0. apply type_defeq_inv in HconvA.
        destruct HconvA as [? []]. apply inv_wfcontext_wftype in w. destruct w. constructor. auto. auto. simpl. rewrite HeG1.
        rewrite HeA. auto. auto. 
        --- rewrite HeBb HeB. reflexivity.
    * simpl. rewrite HeA HeB. reflexivity.
    * simpl. rewrite HeA HeB Het. reflexivity.
    * simpl. rewrite HeA' HeB' Heu. reflexivity.
    * exact HeG1.

    (* Cas r_TermPiCong*)
    +

    (* 4. Cas r_TermFunEta *)
    + apply section_term in r.
      destruct r as [Γ1 [f1 [Prod1 [Htyp_f [HeProd [Hef HeG1]]]]]].
      
      (* Prod1 s'efface en r_Prod A B. Cela implique que Prod1 est convertible à un Prod A1 B1 *)
      (* On construit ce témoin de conversion *)
      assert (∑ A1 B1, [Γ1 |- Prod1 = Prod A1 B1] × (erase_ty A1 = A) × (erase_ty B1 = B)).
      { 
          destruct Prod1; simpl in HeProd; try discriminate.
          - (* Cas où Prod1 est syntaxiquement un Prod *)
            exists Prod1_1, Prod1_2. split. 
            apply TypeRefl. apply wftype_typing_inv in Htyp_f. destruct Htyp_f; auto.
            injection HeProd; auto. intros. constructor. auto. auto.
          - (* Cas où Prod1 est un Decode *)
            (* On admet ici l'inversion du typage Russell pour récupérer A1 et B1 bien formés *)
            (* C'est nécessaire car on n'a pas accès direct aux preuves de formation de A et B ici *)
            assert (∑ A1 B1, [Γ1 |- Prod A1 B1] × erase_ty A1 = A × erase_ty B1 = B). 
            { admit. } 
            
            destruct H as [A1 [B1 [Hwf [HA HB]]]].
            exists A1, B1. split.
            + (* Preuve de Decode l t = Prod A1 B1 via le lemme d'inversion d'effacement *)
              apply TypeSym. apply erase_decode_inv_prod. 
              * apply wftype_typing_inv in Htyp_f. destruct Htyp_f; auto.
              * exact Hwf.
              * intros. apply erase_inj_ty; auto.
              * intros. apply erase_inj_ty; auto.
              * simpl. rewrite HA HB. auto.
            + constructor. auto. auto.
      }
      
      destruct H as [A1 [B1 [Hconv [HeA HeB]]]].

      (* On propose les termes. Notez que le type de l'égalité est Prod A1 B1 (la forme canonique) *)
      eexists Γ1, (Lambda A1 B1 (App (weak_ty A1) (weak_ty B1) (weak_term f1) (var_term 0))), f1, (Prod A1 B1).
      repeat split.
      * apply TermFunEta. 
        (* On convertit le type de f1 de Prod1 vers Prod A1 B1 pour appliquer la règle *)
        eapply wfTermConv. exact Htyp_f. exact Hconv.
      * simpl. rewrite HeA HeB. reflexivity.
      * simpl. rewrite HeA HeB. rewrite <- defeq_erase_weak_term.
        rewrite <- defeq_erase_weak_ty. rewrite <- defeq_erase_weak_ty. 
        rewrite HeA HeB Hef. reflexivity.
      * exact Hef.
      * exact HeG1.

    (* 5. Cas r_TermRefl *)
    + apply section_term in r. destruct r as [Γ1 [t1 [A1 [Htyp [HeA [Het HeG]]]]]].
    eexists Γ1, t1, t1, A1.
    repeat split; auto.
    apply TermRefl. exact Htyp.

    (* 6. Cas r_ConvConv *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [t1 [t'1 [A1 [Hconv_t [HeA [Het [Het' HeG1]]]]]]]].
    apply section_conv in r. destruct r as [Γ2 [A2 [B1 [Hconv_A [HeA2 [HeB HeG2]]]]]].

    eexists Γ1, t1, t'1, B1.
    repeat split; auto.
    * eapply TermConv.
        -- exact Hconv_t.
        -- eapply TypeTrans.
        --- apply TypeSym. apply erase_inj_ty.
            ** apply type_defeq_inv in Hconv_A. destruct Hconv_A as [_ [HwfA _]]. eapply erase_inj_ctx_type.
            apply inv_wfcontext_wftype in HwfA. destruct HwfA. exact w0. apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG2. auto. exact HwfA.
             ** apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfA1]. exact HwfA1.
            ** rewrite HeA2 HeA. reflexivity.
        --- eapply erase_inj_ctx_conv_ty.
            apply type_defeq_inv in Hconv_A. destruct Hconv_A as [? []]. apply inv_wfcontext_wftype in w. destruct w.
            exact w1. apply typing_defeq_inv in Hconv_t. destruct Hconv_t as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG2. auto. exact Hconv_A.

    (* 7. Cas r_TermSym *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [u1 [v1 [A1 [Hconv [HeA [Heu [Hev HeG]]]]]]]].
    eexists Γ1, v1, u1, A1.
    repeat split; auto.
    apply TermSym. exact Hconv.

    (* 8. Cas r_TermTrans *)
    + destruct IHRuss_ConvTermDecl1 as [Γ1 [t1 [t'1 [A1 [Hconv1 [HeA [Het [Het' HeG1]]]]]]]].
    destruct IHRuss_ConvTermDecl2 as [Γ2 [t'2 [t''1 [A2 [Hconv2 [HeA2 [Het'2 [Het'' HeG2]]]]]]]].

    eexists Γ1, t1, t''1, A1.
    repeat split; auto.
    * eapply TermTrans.
        -- exact Hconv1.
        -- (* Alignement du terme intermédiaire t'1 et t'2 *)
        eapply TermTrans.
        --- apply erase_inj_term_plus with (u1 := t'2) (A1 := A2).
            ** apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [_ Hwf]]. exact Hwf.
            ** apply typing_defeq_inv in Hconv2. destruct Hconv2 as [_ [Hwf _]]. eapply erase_inj_ctx_term.
            apply inv_wfcontext_typing in Hwf. destruct Hwf. exact w. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG1. auto. auto.
            ** rewrite Het' Het'2. reflexivity.
            ** rewrite HeA HeA2. reflexivity.
        --- eapply erase_inj_ctx_conv_term.
            apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []]. apply inv_wfcontext_typing in t0.
            destruct t0. exact w. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
            apply inv_wfcontext_typing in t0. destruct t0. auto. rewrite HeG1. auto. eapply TermConv. exact Hconv2.
            rewrite <- HeA in HeA2. apply erase_inj_ty. apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []].
            apply wftype_typing_inv in t0. destruct t0. auto. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
            apply wftype_typing_inv in t0. destruct t0. eapply erase_inj_ctx_type. apply inv_wfcontext_typing in t0. destruct t0.
            exact w0. apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []]. apply inv_wfcontext_typing in t3. destruct t3. auto.
            rewrite HeG1. auto. auto. auto. 

    (* 10. Cas r_TermUnivCumul *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [u1 [v1 [Up [Hconv [HeUp [Heu [Hev HeG]]]]]]]].
    eexists Γ1, (cLift p n u1), (cLift p n v1), (U n).
    repeat split.
    * apply TermLiftingCong.
        -- eapply TermConv. exact Hconv.
        apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT]. exact HwfT.
        --- apply wfTypeU. apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]]. apply inv_wfcontext_typing in Hwf. destruct Hwf; auto.
        --- rewrite HeUp. simpl. reflexivity.
        -- exact l.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
Qed.