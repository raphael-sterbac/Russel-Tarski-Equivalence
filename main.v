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

(*
(* Fonction auxiliaire pour appliquer n fois l'affaiblissement *)
 Fixpoint iter_weak (n : nat) (A : ty) : ty :=
  match n with
  | 0 => A
  | S m => weak_ty (iter_weak m A)
  end.

(* Lemme intermédiaire généralisé pour l'inversion des variables *)
Lemma var_inv_gen :
  forall Γ t T, [Γ |- t : T] ->
  forall n Δ Γ' A,
  t = var_term n ->
  Γ = Δ ++ (A :: Γ') ->
  length Δ = n ->
  [Γ |- T = iter_weak (S n) A].
Proof.
  (* Induction sur la dérivation de typage *)
  intros Γ t T H. intros n0 Δ0 Γ'0 A0 HeqTerm HeqCtx Hlen. subst. dependent induction H.

  (* 1. Cas wfVar0 : var 0 *)
  -
    (* On déduit que Δ0 est vide car length Δ0 = 0 *)
    destruct Δ0. simpl in x; try discriminate.
    (* On déduit que A = A0 et Γ = Γ'0 *)
    simpl in x0. injection x0. intros; subst.
    simpl. (* iter_weak 1 A0 = weak_ty A0 *)
    apply TypeRefl. 
    apply weak_lemma. assumption.
    simpl in x. contradict x. auto.

  (* 2. Cas wfVarN : var (n+1) *)
  - destruct n.
    + simpl in x. symmetry in x. rewrite x. simpl. destruct Δ0.
        * discriminate.
        * simpl in x. destruct Δ0. simpl in x0. inversion x0. simpl. simpl in IHTypingDecl.
    + injection HeqTerm. intros; subst.
      (* Δ0 ne peut pas être vide car length  = S n0 *)
      destruct Δ0; simpl in Hlen; try discriminate.
      injection Hlen. intros Hlen'.
      simpl in HeqCtx. injection HeqCtx. intros HeqCtx' HeqHead. subst.
      
      (* Appel récursif de l'HI sur le contexte Γ (qui est Γ'0 dans la dérivation) *)
      (* On a [Γ |- var n0 : B] *)
      (* On veut prouver [Γ,, T_head |- weak B = iter_weak (S (S n0)) A0] *)
      
      simpl. (* iter_weak (S (S n0)) A0 = weak (iter_weak (S n0) A0) *)
      
      apply weak_cong. 
      eapply IHTypingDecl.
      * reflexivity.
      * reflexivity. (* Γ = Δ0 ++ A0 :: Γ'0 *)
      * exact Hlen'.

  (* 4. Cas Conv : conversion de type *)
  - (* H : [Γ |- t : A], H0 : [Γ |- A = B] *)
    eapply TypeTrans. [cite_start](* [cite: 44] *)
    + apply TypeSym. exact H0. [cite_start](* [cite: 45] *)
    + eapply IHTypingDecl; eauto.
Qed.
*)

Lemma var_inv Γ :
    forall n A,
    [Γ |- var_term n : A] ->
    ∑ B Γ', [Γ |- A = weak_ty B] × (Γ = Γ' ,, B).
    (*TODO : changer et mettre in_ctx *)
Proof.
    intros. dependent induction H.
    - eexists A. eexists Γ. constructor. apply TypeRefl. apply weak_lemma. auto. auto.
    - specialize (IHTypingDecl n0 eq_refl). destruct IHTypingDecl as [? [? []]]. eexists B. eexists Γ.
        constructor. apply TypeRefl. apply weak_lemma. auto.
Admitted.

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



(*TODO : Remove *)
Lemma variable_non_zero_inv Γ A n :
    [Γ |- (var_term (S n)) : A] ->
    ∑ Γ' B, (A = weak_ty B) × (Γ = Γ' ,, A) × [Γ' |- A].
Proof. Admitted.
Lemma variable_zero_inv Γ A:
    [Γ |- (var_term 0) : A] ->
    ∑ Γ' B, (A = weak_ty B) × (Γ = Γ' ,, A) × [Γ' |- A].
Proof. Admitted.
Lemma weaken_type Γ A B:
    [Γ |- A] ->
    [Γ,,B |- A].
Proof. Admitted.
Lemma weaken_typing Γ a A B:
    [Γ |- B] ->
    [Γ |- a: A] ->
    [Γ,,B |- a: A].
Proof. Admitted.



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
Axiom erase_weak_ty: forall {Γ A}, [Γ |-r r_weak_term (erase_ty A) = erase_ty (weak_ty A) ].
Axiom erase_subst_ty: forall {Γ a A}, [Γ |-r r_subst_term (erase_term a) (erase_ty A) = erase_ty (subst_ty a A) ].
Axiom erase_subst_term: forall {Γ a t B}, [Γ |-r r_subst_term (erase_term a) (erase_term t) = erase_term (subst_term a t) : B].


(* ----- Lemme de correction de l'effacement ----- *)

Lemma erasure_correction_wf_ty {A} : forall Γ, [Γ |- A] -> [(erase_context Γ) |-r (erase_ty A)]
with erasure_correction_typing {a} : forall Γ A, [Γ |- a : A] -> [(erase_context Γ) |-r (erase_term a) : (erase_ty A)]
with erasure_correction_conversion {A} : forall Γ B, [Γ |- A = B] -> [(erase_context Γ) |-r (erase_ty A) = (erase_ty B)]
with erasure_correction_conv_typing {a} : forall Γ b A, [Γ |- a = b: A] -> [(erase_context Γ) |-r (erase_term a) = (erase_term b) : (erase_ty A)]
with ctx_formation_to_russ {Γ} : [ |- Γ ]  ->  [ |-r erase_context Γ].
Proof.
- induction 1.
    + simpl; constructor; apply ctx_formation_to_russ; exact w.
    + simpl; apply product_wf_ty; auto.
    + simpl; apply erasure_correction_typing in t; apply r_wfTypeUniv in t; exact t.
- induction 1.
    + simpl. eapply r_TermConv. instantiate (1:=r_weak_term (erase_ty A)). constructor. apply erasure_correction_wf_ty in w. auto.
    apply erase_weak_ty.
    + simpl. eapply r_TermConv. instantiate (1:=r_weak_term (erase_ty B)). constructor. apply erasure_correction_wf_ty; auto. apply IHTypingDecl.
    apply erase_weak_ty.
    + simpl; simpl in IHTypingDecl1; simpl in IHTypingDecl2; constructor; auto.
    + simpl; constructor; auto.
    + simpl; simpl in IHTypingDecl. apply r_wfTermCumul with (1:=l0) in IHTypingDecl; auto.
    + simpl; simpl in IHTypingDecl; constructor; auto.
    + simpl; simpl in IHTypingDecl1; simpl in IHTypingDecl2. eapply r_TermConv. instantiate (1:=r_subst_term (erase_term a) (erase_ty B)). constructor; auto.
        apply erase_subst_ty.
    + apply erasure_correction_conversion in c; apply r_TermConv with (1:=IHTypingDecl); exact c.
- induction 1.
    + simpl; constructor; auto.
    + simpl. apply erasure_correction_conv_typing in c. apply r_TypeUnivConv in c. auto.
    + simpl; apply r_TypeRefl; constructor; apply ctx_formation_to_russ; auto.
    + simpl. constructor. apply erasure_correction_typing in t. simpl in t. apply r_wfTypeUniv in t. exact t.
    + simpl. constructor. apply erasure_correction_typing in t. simpl in t. apply r_wfTypeUniv in t. exact t. constructor.
        apply erasure_correction_typing in t. simpl in t. apply r_wfTypeUniv in t. auto. apply erasure_correction_typing in t0. simpl in t0.
        apply r_wfTypeUniv in t0. constructor. auto.
    + simpl; constructor; auto.
    + simpl. eapply r_TypeTrans. exact IHConvTypeDecl1. exact IHConvTypeDecl2.
    + simpl; constructor; auto.  
- induction 1.
    + simpl. eapply r_ConvConv. instantiate (1:=r_subst_term (erase_term a) (erase_ty B)). eapply r_TermTrans. instantiate (1:= r_subst_term (erase_term a) (erase_term t)).
     constructor. apply erasure_correction_wf_ty in w. auto. apply erasure_correction_typing in t0. auto. apply erasure_correction_typing in t1; auto. apply erase_subst_term. apply erase_subst_ty.
    + simpl. apply r_TermUnivConv. constructor. apply erasure_correction_typing in t. apply r_wfTypeUniv in t. auto.
        apply r_TypeUnivConv in IHConvTermDecl1. auto. apply r_TypeUnivConv in IHConvTermDecl2. auto.
    + simpl. eapply r_ConvConv. instantiate (1:=r_subst_term (erase_term a) (erase_ty B)). constructor. apply erasure_correction_conversion in c. auto. apply erasure_correction_conversion in c0. auto.
        auto. auto. apply erase_subst_ty. 
    + simpl. constructor. apply erasure_correction_wf_ty in w; auto. apply erasure_correction_conversion in c; auto.  
        apply erasure_correction_conversion in c0; auto. auto.
    + simpl. constructor. constructor. apply erasure_correction_typing in t; simpl in t; auto.  
        apply erasure_correction_typing in t0; simpl in t0. eapply r_wfTermCumul. instantiate (1:=p).
        auto. auto. eapply r_wfTermCumul. instantiate (1:=p). auto. apply erasure_correction_typing in t0. auto.
    + simpl. constructor. constructor. apply ctx_formation_to_russ in w. auto. lia.
    + simpl. constructor. apply erasure_correction_typing in t; simpl in t; auto. eapply r_wfTermCumul.
        instantiate (1:= p). auto. eapply r_wfTermCumul. instantiate (1:=n). auto. auto.
    + simpl. simpl in IHConvTermDecl. eapply r_TermUnivCumul. instantiate (1:=n). auto. auto.
    + simpl. eapply r_TermTrans. instantiate (1:= r_Lambda (erase_ty A) (erase_ty B) (r_App (erase_ty (weak_ty A)) (erase_ty (weak_ty B)) (r_weak_term (erase_term f)) (r_var_term 0))).
    apply wftype_typing_inv in t. destruct t. apply prod_ty_inv in w. destruct w. apply erasure_correction_wf_ty in w. apply erasure_correction_wf_ty in w0. apply r_TermLambdaCong. auto. apply r_TypeRefl. auto.
    apply r_TypeRefl. auto. rewrite defeq_erase_weak_term. apply r_TermRefl. eapply r_wfTermConv. eapply r_wfTermApp.
        * eapply weak_term_lemma in t. apply erasure_correction_typing in t. rewrite <- weak_ty_prod in t. simpl in t. exact t.
        * eapply r_wfTermConv. apply r_wfVar0. auto. apply erase_weak_ty.
        * pose (@subst_var_0 B) as H_temp. apply wftype_typing_inv in t. destruct t. inversion w1. eapply f_equal with (f := erase_ty) in H_temp.
            simpl in H_temp. simpl in H_temp. eapply r_TypeTrans. instantiate (1:=erase_ty (subst_ty (var_term 0) (weak_ty B))). rewrite <- defeq_erase_subst_ty. simpl. apply r_TypeRefl.
            pose (wfVar0 H2) as Hvar. eapply substitution_lemma in Hvar. apply erasure_correction_wf_ty in Hvar. rewrite <- defeq_erase_subst_ty in Hvar. exact Hvar.
            assert (H2bis:=H2). eapply weak_lemma in H2bis. eapply weak_lemma in H2bis. exact H2bis.
             rewrite H_temp. apply r_TypeRefl. apply erasure_correction_wf_ty in H3. auto.
        * rewrite <- defeq_erase_weak_ty. rewrite <- defeq_erase_weak_ty. eapply r_TermFunEta. apply erasure_correction_typing in t. auto.

    + constructor. apply erasure_correction_typing in t0; auto.
    + apply erasure_correction_conversion in c. eapply r_ConvConv. instantiate (1:= erase_ty A). auto. auto.
    + apply r_TermSym. auto.
    + eapply r_TermTrans. instantiate (1:= erase_term t'). auto. auto.
- induction 1.
    all: try (constructor; auto).
    all: try (constructor; auto).
Admitted. (*TODO : decreasing argument *)


(* ----- Lemmes utiles ----- *)

Lemma lift_same {u}:
    forall Γ l,
    [Γ |- u : U l] ->
    [Γ |- u = cLift l l u : U l].
Proof.
    (*TODO : Preuve ? *)
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

Lemma erase_var_inv Γ t:
    forall A A1 n,
    [Γ |- var_term n : A] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    r_var_term n = erase_term t ->
    [Γ |- var_term n = t : A ].
Proof.
        induction t.
        all: try(intros; simpl in H2; contradict H2; congruence).
        + intros. simpl in H2. inversion H2. constructor. assert (Hbis:= H0); apply var_inv in Hbis; destruct Hbis as [? [? []]].
        apply wfTermConv with (1:= H0). assert (Hbis := H); apply var_inv in Hbis; destruct Hbis as [? [? []]]. rewrite e0 in e.
        inversion e. eapply TypeTrans. instantiate (1:=weak_ty projT3); auto. symmetry in H5. rewrite H5. auto using TypeSym.
        + intros. simpl in H2. assert (Hbis:=H0); apply lift_inv_plus in Hbis; destruct Hbis as [? [? [? []]]].
        apply IHt with (1:=H) (2:=t0) in H2. assert (Hbis:= H); apply var_inv in Hbis; destruct Hbis as [? [? []]].
        apply subject_red in H2. contradict H2; intros. apply wfTermConv with (1:=H2) in c0. apply cohesion_weak_univ with (1:=c0) (2:=t0).
        auto. auto. 
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


Lemma erase_app_inv 
{Γ t}:
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
    ([Γ' |- a = u1 : A] × [Γ' |- B = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- B = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- a = cLift k l0 v0 : B]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    r_App (erase_ty A) (erase_ty B) (erase_term f) (erase_term a) = erase_term t ->
    [Γ |- App A B f a = t : subst_ty a B ].
Proof.
    induction t.
    all: try(intros; simpl in H5; contradict H5; congruence).
    - intros. simpl in H5. inversion H5. assert (Hbis:=H). apply app_inv in Hbis. destruct Hbis as [? [? [? []]]].
    apply H1 in H7. apply H2 in H8. 

    (* TODO : C'est le bazar dans les hypothèses, mettre les bonnes *)

Admitted.

Lemma erase_cprod_inv 
{Γ t}:
    forall a b l A0 A1 u B,
    [Γ |- cProd l a b : A0] ->
    [Γ |- t : A1] ->
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
    r_Prod (erase_term a) (erase_term b) = erase_term t ->
    [Γ |- cProd l a b = t : A0 ].
Proof.
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
            destruct n.
            
            (* Case n = 0*)
            +++ simpl in H1; inversion H1.  rewrite H3 in H0.
                apply variable_zero_inv in H; destruct H; destruct projT4; destruct projT5; destruct p.
                apply variable_zero_inv in H0; destruct H0; destruct projT6; destruct projT7; destruct p.
                rewrite e0 in e2; inversion e2. constructor. rewrite e2 in e0. rewrite e0. apply weaken_type. auto.

                (* TODO : on se passe de weaken_type et on utilise v_i+1 = weak v_i *)
            
            (* Case S n *)
            +++ simpl in H1; inversion H1.  rewrite H3 in H0. 
                apply variable_non_zero_inv in H; destruct H; destruct projT4; destruct projT5; destruct p.
                apply variable_non_zero_inv in H0; destruct H0; destruct projT6; destruct projT7; destruct p.
                rewrite e0 in e2; inversion e2. constructor. rewrite e2 in e0. rewrite e0. apply weaken_type. auto.
                
                (* TODO : Idem *)
        
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
         apply TypeSym in cbis; apply TermConv with (1:= H1) in cbis.  apply inl; constructor.
         
         all: try(instantiate (1:=App t t0 u0_1 u0_2)); auto. (*TODO : corriger après lemme erase_app_inv*)

         apply subject_red in cbis. assert (Hbis := H0). apply lift_inv_plus in H0; destruct H0 as [? [? [? []]]].
         apply lift_inv_plus in cbis; destruct cbis as [? [? [? []]]]. symmetry in e; symmetry in e0; rewrite e in c0; rewrite e0 in c1. apply TypeSym in c1. apply TypeTrans with (1:= c0) in c1.
         auto using TypeSym. auto. shelve. (*TODO : idem*)
        
    
    (* u0 = cProd *)
    + intros. destruct u1.
        all: try(simpl in H1; contradict H1; congruence).
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
                    a pply lift_inv in t10. destruct t10 as [? []]. apply sup_max. auto. auto.
                    aply TermSym. apply TermLiftingProdConv.
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

    + intros. destruct u1. 
        all: try(simpl in H1; contradict H1; congruence).
        ++  simpl in H1. inversion H1. assert (Hbis:=H). apply code_univ_inv_bis in Hbis. destruct Hbis.
        assert (H0bis:=H0). apply code_univ_inv_bis in H0bis. destruct H0bis.
        apply inr. eexists l0. eexists l2. set (k:=(Nat.min l0 l2)). eexists k. eexists (cU l k). eexists (cU l k).
        constructor. auto. constructor. auto. constructor. apply TermSym. eapply TermConv. instantiate (1:= U l0).
        rewrite H3. apply TermLiftingUnivConv. apply inv_wfcontext_typing in H. destruct H. apply code_univ_inv_bis in t. destruct t.
        apply code_univ_inv_bis in H0. destruct H0. auto.
        apply inf_min. rewrite H3 in l3. auto. auto. apply sup_left_min. auto using TypeSym.
        constructor.  apply TermSym. eapply TermConv. instantiate (1:= U l2).
        rewrite H3. apply TermLiftingUnivConv. apply inv_wfcontext_typing in H. destruct H. apply code_univ_inv_bis in t. destruct t.
        apply code_univ_inv_bis in H0. destruct H0. auto.
        apply inf_min. rewrite H3 in l3. auto. auto. apply sup_right_min. auto using TypeSym.
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

    
Admitted.

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
    (forall A, [Γ |- A] -> [Γ' |- A]).
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
    [Γ1 |-  u1 : A1] × (erase_ty A1 = A) × (erase_term u1 = u) × (erase_context Γ1 = Γ)).
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
    + destruct IHruss_termpingDecl as [? [? [? [? [? []]]]]]. apply section_ty in r. destruct r as [? [? [? []]]].
        destruct projT3. simpl in e1. contradict e1. congruence. simpl in e1. inversion e1. eexists projT6. eexists (Lambda t1 projT5 projT4). eexists (Prod t1 projT5).
        symmetry in e2. rewrite e2 in H1. apply inv_wfcontext_typing in t0; destruct t0; inversion w0. (* TODO : finir pour lambda *)