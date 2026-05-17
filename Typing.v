From Coq Require Import ssreflect Lia Program.Equality PeanoNat Lists.List Arith.
Require Import RussellTarskiEquivalence.core.
Require Import RussellTarskiEquivalence.unscoped.
Require Import RussellTarskiEquivalence.Autosubst.
Require Import RussellTarskiEquivalence.Syntax.


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
        [ Γ,, A|- var_term 0 : A⟨↑⟩ ]
    | wfVarN {Γ} {n A B} :
        [Γ |- A] ->
        [Γ |- var_term n : B] ->
        [Γ ,, A |- var_term (S n) : B⟨↑⟩ ]
    
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
        (m<=l) ->
        [Γ |- cLift m l a : U l]
    | wfTermLambda {Γ} {A B t} :
        [ Γ |- A ] ->        
        [ Γ ,, A |- t : B ] -> 
        [ Γ |- Lambda A B t : Prod A B]
    | wfTermApp {Γ} {f a A B} :
        [ Γ |- f : Prod A B ] -> 
        [ Γ |- a : A ] -> 
        [ Γ |- App A B f a : B[a..] ]
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
        (m <= n) ->
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
            [ Γ |- App A B (Lambda A B t) a = t[a..] : B[a..] ]
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
        [ Γ |- App A B f a = App A' B' g b : B[a..] ]
    | TermLambdaCong {Γ} {t u A A' B' B} :
        [ Γ |- A ] ->
        [ Γ |- A = A' ] ->
        [ Γ,,A |- B = B' ] ->
        [ Γ,, A |- t = u : B ] ->
        [ Γ |- Lambda A B t = Lambda A' B' u : Prod A B ]
    | TermLiftingProdConv {Γ a b n p}:
        [Γ |- a: U p] ->
        [Γ,, Decode p a |- b : U p ] ->
        (p <= n) ->
        [Γ |- cLift p n (cProd p a b) = cProd n (cLift p n a) (cLift p n b) : U n]
    | TermLiftingUnivConv {Γ p n m}:
        [   |- Γ] ->
        m < n ->
        n <= p ->
        [Γ |- cLift n p (cU m n) =  cU m p : U p]
    | TermLiftingCumul {Γ a n l p}:
        [Γ |- a : U n] ->
        (n <= p) ->
        (p <= l) ->
        [Γ |- cLift p l (cLift n p a) = cLift n l a : U l]
    | TermLiftingCong {Γ a b n p}:
        [Γ |- a = b: U n] ->
        (n <= p) ->
        [Γ |- cLift n p a = cLift n p b : U p]
    | TermLiftSame {u Γ l}:
        [Γ |- u : U l] ->
        [Γ |- u = cLift l l u : U l]
    | TermFunEta {Γ} {f A B} :
        [ Γ |- f : Prod A B ] ->
        [ Γ |- Lambda A B (App A⟨↑⟩ B⟨⇑⟩ f⟨↑⟩ (var_term 0)) = f : Prod A B ]
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
with Russ_TypingDecl : russ_ctx -> russ_term -> russ_term -> Type :=
    | r_wfVar0 {Γ} {A} :
        [ Γ |-r A ] ->
        [ Γ,,r A |-r r_var_term 0 : A⟨↑⟩ ]
    | r_wfVarN {Γ} {n A B} :
        [Γ |-r A] ->
        [Γ |-r r_var_term n : B] ->
        [Γ ,,r A |-r r_var_term (S n) : B⟨↑⟩ ]

    | r_wfTermLambda {Γ} {A B t} :
        [ Γ |-r A ] ->        
        [ Γ ,,r A |-r t : B ] -> 
        [ Γ |-r r_Lambda A B t : r_Prod A B]
    | r_wfTermApp {Γ} {f a A B} :
        [ Γ |-r f : r_Prod A B ] -> 
        [ Γ |-r a : A ] -> 
        [ Γ |-r r_App A B f a : B[a..] ]
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
            [ Γ |-r r_App A B (r_Lambda A B t) a = t[a..] : B[a..] ]
    | r_TermAppCong {Γ} {a b f g A B A' B'} :
        [ Γ |-r A = A'] ->
        [ Γ,,r A |-r B = B'] ->
        [ Γ |-r f = g : r_Prod A B ] ->
        [ Γ |-r a = b : A] ->
        [ Γ |-r r_App A B f a = r_App A' B' g b : B[a..] ]
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
        [ Γ |-r r_Lambda A B (r_App A⟨↑⟩ B⟨⇑⟩ f⟨↑⟩ (r_var_term 0)) = f : r_Prod A B ]
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
and   "[ Γ |-r t : T ]" := (Russ_TypingDecl Γ t T)
and   "[ Γ |-r A = B ]" := (Russ_ConvTypeDecl Γ A B)
and   "[ Γ |-r t = t' : T ]" := (Russ_ConvTermDecl Γ t t' T)
and   "[ |-r Γ ]" := (Russ_WfContextDecl Γ).