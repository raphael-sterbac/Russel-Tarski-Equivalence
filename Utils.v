From Coq Require Import ssreflect Lia Program.Equality PeanoNat Lists.List Arith.
Require Import RussellTarskiEquivalence.core.
Require Import RussellTarskiEquivalence.unscoped.
Require Import RussellTarskiEquivalence.Autosubst.
Require Import RussellTarskiEquivalence.Syntax.
Require Import RussellTarskiEquivalence.Typing.


(* --------- Axioms --------- *)

(* --------- Axioms --------- *)

(* --- Substitutions and weakenings --- *)

Axiom substitution_lemma :
    forall {Γ A B a},
    [ Γ ,, A |- B ] ->
    [ Γ |- a : A ] ->
    [ Γ |- B[a..] ].

Axiom substitution_lemma_term: forall {Γ A B a t},
    [ Γ ,, A |- t: B ] ->
    [ Γ |- a : A ] ->
    [ Γ |- t[a..] : B[a..]].

Axiom r_substitution_lemma: forall {Γ a A B},
    [ Γ ,,r A |-r B ] ->
    [ Γ |-r a : A ] ->
    [ Γ |-r B[a..] ].

Axiom r_substitution_lemma_term: forall {Γ a t A B},
    [ Γ ,,r A |-r t : B ] ->
    [ Γ |-r a : A ] ->
    [ Γ |-r t[a..] : B[a..] ].

Axiom subst_cong: forall {Γ A B B' a a'},
    [ Γ ,, A |- B = B' ] ->
    [ Γ |- a = a' : A ] ->
    [ Γ |- B[a..] = B'[a'..] ].

Axiom r_subst_cong: forall {Γ A B B' a a'},
    [ Γ ,,r A |-r B = B' ] ->
    [ Γ |-r a = a' : A ] ->
    [ Γ |-r B[a..] = B'[a'..] ].

Axiom weak_lemma: forall {Γ A B},
    [ Γ |- A] ->
    [ Γ,,A |- B⟨↑⟩ ].

Axiom r_weak_lemma: forall {Γ A B},
    [ Γ |-r A] ->
    [ Γ,,r A |-r B⟨↑⟩ ].

Axiom weak_cong: forall {Γ A B C},
    [Γ |- A = B] ->
    [Γ,, C |- A⟨↑⟩ = B⟨↑⟩].

Axiom r_weak_cong: forall {Γ A B C},
    [Γ |-r A = B] ->
    [Γ,,r C |-r A⟨↑⟩ = B⟨↑⟩].

Axiom weak_term_lemma: forall {Γ a A B},
    [Γ |- a : A] ->
    [Γ,, B |- a⟨↑⟩ : A⟨↑⟩].

Axiom r_weak_term_lemma: forall {Γ a A B},
    [Γ |-r a : A] ->
    [Γ,,r B |-r a⟨↑⟩ : A⟨↑⟩].

Axiom UInj: forall {Γ k l},
    [Γ |- U k = U l] ->
    k = l.

Axiom cohesion_prod_univ: forall {Γ t A B n},
    [Γ |- t : Prod A B] ->
    [Γ |- t : U n] ->
    False.

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

(* context_conversion_ctx *)
- intros Γ H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv.
    + destruct Δ0; inversion Heq.
    + destruct Δ0.
      * 
        simpl in Heq. injection Heq. intros HeqG HeqA. subst.
        simpl. apply concons.
        ** auto.
        ** 
           apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]].
           auto.
      * 
        simpl in Heq. injection Heq. intros. subst.
        simpl. apply concons.
        ** apply IHWfContextDecl with (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.
        ** apply context_conversion_ty with (Γ := (Δ0 ++ Γ'0,, A0)) (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.

(* context_conversion_ty *)
  - intros Γ T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* U *) apply wfTypeU. eapply context_conversion_ctx; eauto.
    + (* Prod *) apply wfTypeProd.
      * eapply IHWfTypeDecl1; eauto.
      * eapply IHWfTypeDecl2 with (Δ := Δ0 ,, A); eauto. simpl. reflexivity.
    + (* Decode *) apply wfTypeDecode. eapply context_conversion_term; eauto.

  (* context_conversion_term *)
  - intros Γ t T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + (* wfVar0 *)
      rename A into T_declared.
      destruct Δ0.
      * 
        simpl. injection Heq. intros. subst.
        eapply wfTermConv. instantiate (1 := B0⟨↑⟩ ).
        ** apply wfVar0. apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
        **
           apply TypeSym. 
           apply weak_cong.
           exact Hconv.
      * 
        simpl. injection Heq. intros. subst.
        apply wfVar0.
        eapply context_conversion_ty; eauto.

    + (* wfVarN *)
        rename A into T_head.
        destruct Δ0.
        * 
            simpl. injection Heq. intros. subst.
            apply wfVarN.
            **
            apply type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
            ** 
            exact H.
            
        * 
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

  (* context_conversion_ty_eq *)
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

  (* context_conversion_term_eq *)
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
    + (* TermLiftSame *) apply TermLiftSame. auto. eapply context_conversion_term; eauto.
    + (* FunEta *) apply TermFunEta. eapply context_conversion_term; eauto.
    + (* Refl *) apply TermRefl. eapply context_conversion_term; eauto.
    + (* Conv *) eapply TermConv.
       * eapply IHConvTermDecl; eauto.
       * eapply context_conversion_ty_eq; eauto.
    + (* Sym *) apply TermSym; eauto.
    + (* Trans *) eapply TermTrans; eauto.

  (* type_defeq_inv *)
  - intros. split.
    + auto.
    +
      *
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

  (* typing_defeq_inv *)
  - intros H. induction H.
    + (* TermBRed *)
      split. { eapply TermBRed; eassumption. }
      split.
      * apply wfTermApp; eauto. apply wfTermLambda; eauto.
      * eapply substitution_lemma_term; eauto.
    + (* TermPiCong *)
      destruct IHConvTermDecl1 as [Heq_AB [Htyp_A Htyp_B]].
      destruct IHConvTermDecl2 as [Heq_CD [Htyp_C Htyp_D]].
      split. { apply TermPiCong; eassumption. }
      split.
      * apply wfTermcProd.
        -- exact Htyp_A.
        -- apply wfTypeDecode. exact Htyp_A.
        -- exact Htyp_C.      * apply wfTermcProd; eauto. apply wfTypeDecode. exact Htyp_B.
        eapply conv_hypothesis_typing. exact Htyp_D. apply TypeDecodeCong. exact Heq_AB.
    + (* TermAppCong *)
      destruct IHConvTermDecl1 as [Heq_f [Htyp_f Htyp_g]].
      destruct IHConvTermDecl2 as [Heq_a [Htyp_a Htyp_b]].
      split. { eapply TermAppCong; eassumption. }
      split.
      * eapply wfTermApp; eauto.
      * eapply wfTermConv. instantiate (1 := B'[b..]).
        -- apply type_defeq_inv in c. destruct c as [c [Hwf_A Hwf_A']].
           apply type_defeq_inv in c0. destruct c0 as [c0 [Hwf_B Hwf_B']].
           eapply wfTermApp.
           ++ eapply wfTermConv. exact Htyp_g. apply TypePiCong. exact Hwf_A. exact c. apply TypeSym. apply TypeSym. exact c0.
           ++ eapply wfTermConv. exact Htyp_b. exact c.
        -- eapply subst_cong. apply TypeSym. exact c0. apply TermSym. exact Heq_a.
    + (* TermLambdaCong *)
      destruct IHConvTermDecl as [Heq_tu [Htyp_t Htyp_u]].
      split. { apply TermLambdaCong; eassumption. }
      split.
      * apply wfTermLambda; eauto.
      * eapply wfTermConv. instantiate (1:=Prod A' B').
        -- apply wfTermLambda.
           ++ apply type_defeq_inv in c0. destruct c0 as [? []]. auto.  apply type_defeq_inv in c. destruct c as [? []]. auto. 
           ++ eapply conv_hypothesis_typing. eapply wfTermConv. exact Htyp_u. exact c0. auto.
        -- apply TypePiCong. apply type_defeq_inv in c0. destruct c0 as [? []]. auto. apply type_defeq_inv in c. destruct c as [? []]. auto.
           auto using TypeSym. eapply conv_hypothesis_type_eq. apply TypeSym. exact c0. auto using TypeSym. 
    + (* TermLiftingProdConv *)
      split. { apply TermLiftingProdConv; eassumption. }
      split.
      * apply wfTermcLift; auto. apply wfTermcProd; eauto. apply typing_hypothesis_inv in t0. destruct t0 as [? []]. auto.
      * apply wfTermcProd.
        -- apply wfTermcLift; eauto.
        -- apply wfTypeDecode. apply wfTermcLift; eauto.
        -- eapply conv_hypothesis_typing.
           ++ apply wfTermcLift. exact t0. exact l.
           ++ apply TypeDecodeLiftConv; eauto.
    + (* TermLiftingUnivConv *)
      split. { apply TermLiftingUnivConv; eassumption. }
      split.
      * apply wfTermcLift; eauto. apply wfTermcUniv; eauto. 
      * apply wfTermcUniv; eauto. lia.
    + (* TermLiftingCumul *)
      split. { apply TermLiftingCumul; eassumption. }
      split.
      * apply wfTermcLift; eauto. apply wfTermcLift; eauto.
      * apply wfTermcLift; eauto. lia.
    + (* TermLiftingCong *)
      destruct IHConvTermDecl as [Heq_ab [Htyp_a Htyp_b]].
      split. { apply TermLiftingCong; eassumption. }
      split.
      * apply wfTermcLift; eauto.
      * apply wfTermcLift; eauto.
    + (* TermLiftSame *)
      split. { apply TermLiftSame; eassumption. }
      split.
      * exact t.
      * apply wfTermcLift; eauto.
    + (* TermFunEta *)
      split. { apply TermFunEta; eassumption. }
      split.
      * apply wftype_typing_inv in t. destruct t as [t Hwf_Prod].
        inversion Hwf_Prod. subst.
        apply wfTermLambda.
        -- exact H2.
        -- eapply wfTermConv.
           ++ eapply wfTermApp.
              ** assert (Hweak : [Γ,, A |- f⟨↑⟩ : (Prod A B)⟨↑⟩]).
              {eapply weak_term_lemma in t. instantiate (1:=A) in t. auto. }
              asimpl in Hweak. exact Hweak.
              ** apply wfVar0. exact H2.
           ++ rewrite subst_up_var_0_ty. apply TypeRefl. exact H3.
      * exact t.
    + (* TermRefl *)
      split. { apply TermRefl; eassumption. }
      split; assumption.
    + (* TermConv *)
      destruct IHConvTermDecl as [Heq_tt' [Htyp_t Htyp_t']].
      split. { eapply TermConv; eassumption. }
      split.
      * eapply wfTermConv; eauto.
      * eapply wfTermConv; eauto.
    + (* TermSym *)
      destruct IHConvTermDecl as [Heq_tt' [Htyp_t Htyp_t']].
      split. { apply TermSym; eassumption. }
      split; assumption.
    + (* TermTrans *)
      destruct IHConvTermDecl1 as [Heq_tt' [Htyp_t Htyp_t']].
      destruct IHConvTermDecl2 as [Heq_t't'' [Htyp_t'2 Htyp_t'']].
      split. { eapply TermTrans; eassumption. }
      split; assumption.

(* wftype_typing_inv *)
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
        eapply substitution_lemma.
        ** exact H5. 
        ** exact H0.
      * (* Conv *)
        apply type_defeq_inv in c. destruct c as [_ [_ HwfB]].
        exact HwfB.

(* wftype_hypothesis_inv *)
  - intros. 
    remember (Γ ,, A) as Γ' in H.
    dependent induction H; intros; subst; try discriminate.
    
    (* Cons : *)
    + inversion w; subst. constructor; auto. constructor. auto.
    
    (* Prod *)
    + 
      split.
      *
        eapply IHWfTypeDecl1; reflexivity.
      * 
        apply wfTypeProd.
        ** auto.
        ** assumption.

    (* Decode *)
    + split.
      * 
        eapply typing_hypothesis_inv in t. destruct t as [? []]. auto.
      * apply wfTypeDecode. assumption. 

  (* typing_hypothesis_inv *)
  - intros. split.
    + apply inv_wfcontext_typing in H. inversion H. inversion H1. auto.
    + split.
      * 
        inversion H; subst.
        ** (* wfVar0 *)  assumption.
        ** (* wfVarN *)  assumption.
        ** (* cProd *) apply inv_wfcontext_typing in H. inversion H. inversion H4. auto.
        ** (* cUniv *) inversion H0; subst; assumption.
        ** (* cLift *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* Lambda *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* App *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** (* Conv *) apply inv_wfcontext_typing in H. inversion H. inversion H3. auto.
      * 
        exact H.

  (* conv_hypothesis_wftype *)
  - intros A B Hwf Hconv.
    eapply context_conversion_ty with (Δ := ε).
    + simpl. exact Hwf.
    + reflexivity.
    + exact Hconv.

  (* conv_hypothesis_typing *)
  - intros A B a Htyp Hconv.
    eapply context_conversion_term with (Δ := ε).
    + simpl. exact Htyp.
    + reflexivity.
    + exact Hconv.

  (* conv_hypothesis_type_eq *)
  - intros Heq Hconv.
    eapply context_conversion_ty_eq with (Δ := ε).
    + simpl. exact Heq.
    + reflexivity.
    + exact Hconv.

  (* conv_hypothesis_term_eq *)
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
    ∑ n, [Γ |- A = U n] × l = n × k <= l × [Γ |- u : U k].
Proof.
    intros. dependent induction H.
    - eexists l. constructor. apply TypeRefl. constructor. apply inv_wfcontext_typing in H. destruct H. auto. constructor. auto. constructor. auto. auto.
    - specialize (IHTypingDecl k l u eq_refl). destruct IHTypingDecl as [? [? [? []]]]. eexists l. constructor. eapply TypeTrans. instantiate (1:=A).
        auto using TypeSym. rewrite e. auto. constructor. auto. constructor. auto. auto.
Qed.

Lemma lift_inv Γ k l n u:
    [Γ |- cLift k l u : U n] ->
    l = n × k <= l × [Γ |- u : U k].
Proof.
    intros.
    apply lift_inv_plus in H. destruct H as [? [? [? []]]]. apply UInj in c. constructor. rewrite e. auto. constructor. auto. auto.
Qed.

Lemma app_inv Γ A B C u1 u2:
    [Γ |- App A B u1 u2 : C] ->
    [Γ |- C = B[u2..]] ×  [Γ |- A] × [Γ,,A |- B] × [Γ |- u1 : Prod A B] × [Γ |- u2 : A].
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
  | S m => (iter_weak m A)⟨↑⟩
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

  (* wfVar0 : var 0 *)
  -
    destruct Δ0. simpl in x; try discriminate.
    simpl in x0. injection x0. intros; subst.
    simpl.
    apply TypeRefl. 
    apply weak_lemma. assumption.
    simpl in x. contradict x. auto.

  (* wfVarN : var (n+1) *)
  - destruct Δ0.
        * simpl in x. contradict x. lia.
        * simpl in x. simpl in x0. inversion x0. simpl. 
        specialize (IHTypingDecl Δ0 Γ'0 A0). simpl in IHTypingDecl. rewrite H2 in IHTypingDecl. specialize (IHTypingDecl JMeq_refl).
        eapply weak_cong in IHTypingDecl. exact IHTypingDecl. simpl.  assert (n = length Δ0) by lia. rewrite H0. auto.

  (* Conv : *)
  - 
    eapply TypeTrans.
    + apply TypeSym. exact c.
    + eapply IHTypingDecl; eauto.
Qed.

Lemma variable_zero_inv Γ A:
    [Γ |- var_term 0 : A] ->
    ∑ Γ' B, [Γ |- A = B⟨↑⟩] × (Γ = Γ' ,, B) × [Γ' |- B].
Proof.
    intros H.
    
    assert (Hstruct: ∑ Γ' B, Γ = Γ' ,, B).
    {
      remember (var_term 0) as t.
      induction H; try discriminate.
      -  exists Γ, A. reflexivity.
      -  apply IHTypingDecl. assumption.
    }
    
    destruct Hstruct as [Γ' [B HeqΓ]].
    
    exists Γ', B.
    
    split.
    
    - subst Γ.
      apply var_inv with (n:=0) (Δ:=ε) (Γ':=Γ') (A:=B) in H.
      + simpl in H. exact H.
      + reflexivity.
      + simpl. reflexivity.
      + reflexivity.

    - split.
      + exact HeqΓ.
      
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
      [Γ |- A = B⟨↑⟩].
Proof.
    intros H.
    remember (var_term (S n)) as t.
    induction H; try discriminate.

    - injection Heqt. intro Heqn. subst.
      exists Γ, A, B.
      
      split.
      + reflexivity.
      
      + split. 
        ++ exact H.
        ++ apply TypeRefl.
           apply weak_lemma.
           exact w. 

    - specialize (IHTypingDecl Heqt).
      destruct IHTypingDecl as [Γ' [T_head [B_origin [HeqΓ [Htyp HeqType]]]]].
      
      exists Γ', T_head, B_origin.
      split.
      + exact HeqΓ.
      + split.
        ++ exact Htyp.
        ++ eapply TypeTrans.
           * apply TypeSym. exact c.
           * exact HeqType.
Qed.

Lemma var_ctx_inv Γ A0 A1 n :
    [Γ |- var_term n : A0] ->
    [Γ |- var_term n : A1] ->
    [Γ |- A0 = A1].
Proof.
  revert Γ A0 A1.
  induction n; intros Γ A0 A1 H1 H2.

  - apply variable_zero_inv in H1.
    destruct H1 as [Γ1 [B1 [HeqA1 [HeqG1 Hwf1]]]].
    apply variable_zero_inv in H2.
    destruct H2 as [Γ2 [B2 [HeqA2 [HeqG2 Hwf2]]]].
    
    rewrite HeqG2 in HeqG1. injection HeqG1. intros HeqB HeqCtx. subst.
    
    eapply TypeTrans.
    + exact HeqA1.
    + apply TypeSym. exact HeqA2.

  - apply variable_non_zero_inv in H1.
    destruct H1 as [Γ1 [T1 [B1 [HeqG1 [Hvar1 HeqA1]]]]].
    apply variable_non_zero_inv in H2.
    destruct H2 as [Γ2 [T2 [B2 [HeqG2 [Hvar2 HeqA2]]]]].
    
    rewrite HeqG2 in HeqG1. injection HeqG1. intros HeqHead HeqTail. subst.
    
    assert (Hconv : [Γ1 |- B1 = B2]).
    { apply IHn; assumption. }
    
    eapply TypeTrans.
    + exact HeqA1. 
    + eapply TypeTrans.
      * 
        eapply weak_cong. exact Hconv. 
      * 
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


(* --- Russell inversion lemmas --- *)

Lemma r_inv_wfcontext_wftype Γ A:
    [Γ |-r A] -> [Γ |-r A] × [ |-r Γ]
with  r_inv_wfcontext_typing Γ a A:
    [Γ |-r a: A] -> [Γ |-r a: A] × [ |-r Γ].
Proof.
    + intros.
        constructor.
        auto.
        induction H.
        ++ auto.
        ++ apply r_inv_wfcontext_typing in r. destruct r. auto.
    + intros. constructor. auto. induction H.
        all : try(auto).
        ++ constructor. apply r_inv_wfcontext_wftype in r; destruct r. auto. auto.
        ++ constructor. auto. auto.
        ++ inversion IHRuss_TypingDecl. auto.
Qed. 

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

Lemma r_prod_typing_inv {Γ A B C} :
  [Γ |-r r_Prod A B : C] ->
  [Γ |-r A] × [Γ,,r A |-r B].
Proof.
  intros H. remember (r_Prod A B) as t.
  induction H; try discriminate.
  - apply IHRuss_TypingDecl. exact Heqt.
  - injection Heqt. intros HeqB HeqA. subst.
    split.
    + eapply r_wfTypeUniv; eassumption.
    + eapply r_wfTypeUniv; eassumption.
  - apply IHRuss_TypingDecl. exact Heqt.
Qed.

Lemma r_prod_ty_inv {Γ A B} : 
  [Γ |-r r_Prod A B] -> 
  [Γ |-r A] × [Γ,,r A |-r B].
Proof.
  intros H. 
  inversion H; subst.
  eapply r_prod_typing_inv. exact H0. 
Qed.


Definition r_subst_context (A B : russ_term) (Γ : russ_ctx) (Δ : russ_ctx) : russ_ctx :=
  Δ ++ (B :: Γ).

Lemma r_context_conversion_ctx :
  (forall Γ, [ |-r Γ ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |-r A = B] -> [ |-r r_subst_context A B Γ' Δ ])
with r_context_conversion_ty :
  (forall Γ T, [ Γ |-r T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |-r A = B] -> [ r_subst_context A B Γ' Δ |-r T ])
with r_context_conversion_term :
  (forall Γ t T, [ Γ |-r t : T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |-r A = B] -> [ r_subst_context A B Γ' Δ |-r t : T ])
with r_context_conversion_ty_eq :
  (forall Γ T1 T2, [ Γ |-r T1 = T2 ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |-r A = B] -> [ r_subst_context A B Γ' Δ |-r T1 = T2 ])
with r_context_conversion_term_eq :
  (forall Γ t1 t2 T, [ Γ |-r t1 = t2 : T ] -> forall Γ' A B Δ, Γ = Δ ++ (A :: Γ') -> [Γ' |-r A = B] -> [ r_subst_context A B Γ' Δ |-r t1 = t2 : T ])
with r_type_defeq_inv Γ A B:
    [Γ |-r A = B] ->
    [Γ |-r A = B] × [Γ |-r A] × [Γ |-r B]
with r_typing_defeq_inv Γ a b A:
    [Γ |-r a = b : A] ->
    [Γ |-r a = b : A] × [Γ |-r a : A] × [Γ |-r b : A]
with r_wftype_typing_inv Γ a A:
    [Γ |-r a : A] ->
    [Γ |-r a : A] × [Γ |-r A]
with r_wftype_hypothesis_inv Γ A B:
    [Γ,,r A |-r B] ->
    [Γ |-r A] × [Γ,,r A |-r B]
with r_typing_hypothesis_inv Γ A b B:
    [Γ,,r A |-r b: B] ->
    [ |-r Γ ] × [Γ |-r A] × [Γ,,r A |-r b: B]
with r_conv_hypothesis_wftype {Γ C}:
    forall  A B,
    [Γ,,r A |-r C] ->
    [Γ |-r A = B] ->
    [Γ,,r B |-r C]
with r_conv_hypothesis_typing {Γ C}:
    forall  A B a,
    [Γ,,r A |-r a : C] ->
    [Γ |-r A = B] ->
    [Γ,,r B |-r a : C]
with  r_conv_hypothesis_type_eq {Γ A B C1 C2}:
    [Γ,,r A |-r C1 = C2] ->
    [Γ |-r A = B] ->
    [Γ,,r B |-r C1 = C2]
with r_conv_hypothesis_term_eq {Γ A B a b C}:
    [Γ,,r A |-r a = b : C] ->
    [Γ |-r A = B] ->
    [Γ,,r B |-r a = b : C].
Proof.

(* r_context_conversion_ctx *)
- intros Γ H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv.
    + destruct Δ0; inversion Heq.
    + destruct Δ0.
      * simpl in Heq. injection Heq. intros HeqG HeqA. subst.
        simpl. apply r_concons.
        ** auto.
        ** apply r_type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
      * simpl in Heq. injection Heq. intros. subst.
        simpl. apply r_concons.
        ** apply IHRuss_WfContextDecl with (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.
        ** apply r_context_conversion_ty with (Γ := (Δ0 ++ Γ'0,,r A0)) (Γ' := Γ'0) (A := A0) (B := B0) (Δ := Δ0); auto.

(* r_context_conversion_ty *)
  - intros Γ T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + apply r_wfTypeU. eapply r_context_conversion_ctx; eauto.
    +  eapply r_wfTypeUniv. eapply r_context_conversion_term; eauto.

  (* r_context_conversion_term *)
  - intros Γ t T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + rename A into T_declared.
      destruct Δ0.
      * simpl. injection Heq. intros. subst.
        eapply r_wfTermConv.
        ** apply r_wfVar0. apply r_type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
        ** apply r_TypeSym. apply r_weak_cong. exact Hconv.
      * simpl. injection Heq. intros. subst.
        apply r_wfVar0. eapply r_context_conversion_ty; eauto.
    + rename A into T_head.
      destruct Δ0.
      * simpl. injection Heq. intros. subst.
        apply r_wfVarN.
        ** apply r_type_defeq_inv in Hconv. destruct Hconv as [_ [_ HwfB]]. auto.
        ** exact H.
      * simpl. injection Heq. intros. subst.
        apply r_wfVarN.
        ** eapply r_context_conversion_ty; eauto.
        ** eapply IHRuss_TypingDecl with (Δ := Δ0); auto.
    + apply r_wfTermLambda.
      * eapply r_context_conversion_ty; eauto.
      * eapply IHRuss_TypingDecl with (Δ := Δ0 ,,r A); eauto. simpl. reflexivity.
    + eapply r_wfTermApp.
      * eapply IHRuss_TypingDecl1; eauto.
      * eapply IHRuss_TypingDecl2; eauto.
    + eapply r_wfTermConv.
      * eapply IHRuss_TypingDecl; eauto.
      * eapply r_context_conversion_ty_eq; eauto.
    + apply r_wfTermProd.
      * eapply IHRuss_TypingDecl1; eauto.
      * eapply IHRuss_TypingDecl2 with (Δ := Δ0 ,,r A); eauto. simpl. reflexivity.
    + apply r_wfTermUniv; auto. eapply r_context_conversion_ctx; eauto.
    + eapply r_wfTermCumul; auto. auto.

  (* r_context_conversion_ty_eq *)
  - intros Γ T1 T2 H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + apply r_TypePiCong.
      * eapply r_context_conversion_ty; eauto.
      * eapply IHRuss_ConvTypeDecl1; eauto.
      * eapply IHRuss_ConvTypeDecl2 with (Δ := Δ0 ,,r A); eauto. simpl. reflexivity.
    + apply r_TypeRefl. eapply r_context_conversion_ty; eauto.
    + apply r_TypeSym; eauto.
    + eapply r_TypeTrans; eauto.
    + eapply r_TypeUnivConv. eapply r_context_conversion_term_eq; eauto.

  (* r_context_conversion_term_eq *)
  - intros Γ t1 t2 T H. induction H; intros Γ'0 A0 B0 Δ0 Heq Hconv; subst.
    + eapply r_TermBRed.
      * eapply r_context_conversion_ty; eauto.
      * eapply r_context_conversion_term with (Δ := Δ0 ,,r A); eauto. simpl. reflexivity.
      * eapply r_context_conversion_term; eauto.
    + eapply r_TermAppCong.
      * eapply r_context_conversion_ty_eq; eauto.
      * eapply r_context_conversion_ty_eq with (Δ := Δ0 ,,r A); eauto. simpl. reflexivity.
      * eapply IHRuss_ConvTermDecl1; eauto.
      * eapply IHRuss_ConvTermDecl2; eauto.
    + apply r_TermLambdaCong.
       * eapply r_context_conversion_ty; eauto.
       * eapply r_context_conversion_ty_eq; eauto.
       * eapply r_context_conversion_ty_eq with (Δ := Δ0 ,,r A); eauto. simpl. reflexivity.
       * eapply IHRuss_ConvTermDecl with (Δ := Δ0 ,,r A); eauto. simpl. reflexivity.
    + apply r_TermPiCong.
       * eapply r_context_conversion_term; eauto.
       * specialize (IHRuss_ConvTermDecl1 Γ'0 A0 B0 Δ0 eq_refl Hconv). auto.
       * specialize (IHRuss_ConvTermDecl2 Γ'0 A0 B0 (Δ0,,r A) eq_refl Hconv). auto.
    + apply r_TermFunEta. eapply r_context_conversion_term; eauto.
    + apply r_TermRefl. eapply r_context_conversion_term; eauto.
    + eapply r_ConvConv.
       * eapply IHRuss_ConvTermDecl; eauto.
       * eapply r_context_conversion_ty_eq; eauto.
    + apply r_TermSym; eauto.
    + eapply r_TermTrans; eauto.
    + eapply r_TermUnivCumul; auto. 

(* r_type_defeq_inv *)
  - intros H. induction H.
    + destruct IHRuss_ConvTypeDecl1 as [HeqAB [HwfA HwfB]].
      destruct IHRuss_ConvTypeDecl2 as [HeqCD [HwfC HwfD]].
      split. { apply r_TypePiCong; assumption. }
      split.
      * apply product_wf_ty; assumption.
      * apply product_wf_ty; try assumption. 
        eapply r_conv_hypothesis_wftype. exact HwfD. exact HeqAB.
        
    + split. { apply r_TypeRefl; assumption. }
      split; assumption.
      
    + destruct IHRuss_ConvTypeDecl as [HeqAB [HwfA HwfB]].
      split. { apply r_TypeSym; assumption. }
      split; assumption.
      
    + destruct IHRuss_ConvTypeDecl1 as [HeqAB [HwfA HwfB]].
      destruct IHRuss_ConvTypeDecl2 as [HeqBC [HwfB' HwfC]].
      split. { eapply r_TypeTrans; eassumption. }
      split; assumption.
      
    + apply r_typing_defeq_inv in r. destruct r as [HeqAB [HtypA HtypB]].
      split. { eapply r_TypeUnivConv. exact HeqAB. }
      split.
      * eapply r_wfTypeUniv. exact HtypA.
      * eapply r_wfTypeUniv. exact HtypB.

  (* r_typing_defeq_inv *)
  - intros H. induction H.
    + (* r_TermBRed *)
      split. { eapply r_TermBRed; eassumption. }
      split.
      * apply r_wfTermApp; eauto. apply r_wfTermLambda; eauto.
      * eapply r_substitution_lemma_term; eauto.
    + (* r_TermAppCong *)
      destruct IHRuss_ConvTermDecl1 as [Heq_f [Htyp_f Htyp_g]].
      destruct IHRuss_ConvTermDecl2 as [Heq_a [Htyp_a Htyp_b]].
      split. { eapply r_TermAppCong; eassumption. }
      split.
      * eapply r_wfTermApp; eauto.
      * eapply r_wfTermConv. instantiate (1 := B'[b..]).
        -- apply r_type_defeq_inv in r. destruct r as [r [Hwf_A Hwf_A']].
           apply r_type_defeq_inv in r0. destruct r0 as [r0 [_ Hwf_B']].
           eapply r_wfTermApp.
           ++ eapply r_wfTermConv. exact Htyp_g. apply r_TypePiCong. exact Hwf_A. apply r_TypeSym. apply r_TypeSym. exact r. apply r_TypeSym. apply r_TypeSym. exact r0.
           ++ eapply r_wfTermConv. exact Htyp_b. apply r_TypeSym. apply r_TypeSym. exact r.
        -- eapply r_subst_cong. apply r_TypeSym. exact r0. apply r_TermSym. exact Heq_a.
    + (* r_TermLambdaCong *)
      destruct IHRuss_ConvTermDecl as [Heq_tu [Htyp_t Htyp_u]].
      split. { apply r_TermLambdaCong; eassumption. }
      split.
      * apply r_wfTermLambda; eauto.
      * eapply r_wfTermConv. instantiate (1:=r_Prod A' B').
        -- apply r_wfTermLambda.
           ++ apply r_type_defeq_inv in r0. destruct r0 as [? []]. auto.
           ++ eapply r_conv_hypothesis_typing. eapply r_wfTermConv. exact Htyp_u. exact r1. exact r0.
        -- apply r_TypePiCong. apply r_type_defeq_inv in r0. destruct r0 as [? []]. auto.
           auto using r_TypeSym. eapply r_conv_hypothesis_type_eq. apply r_TypeSym. exact r1. auto using r_TypeSym.
    + (* r_TermPiCong *)
      destruct IHRuss_ConvTermDecl1 as [Heq_AB [Htyp_A Htyp_B]].
      destruct IHRuss_ConvTermDecl2 as [Heq_CD [Htyp_C Htyp_D]].
      split. { apply r_TermPiCong; eassumption. }
      split.
      * apply r_wfTermProd; eauto.
      * apply r_wfTermProd. exact Htyp_B.
        eapply r_conv_hypothesis_typing. exact Htyp_D. eapply r_TypeUnivConv. exact H.
    + (* r_TermFunEta *)
      split. { apply r_TermFunEta; eassumption. }
      split.
      * pose proof r as Htyp_f. apply r_wftype_typing_inv in Htyp_f. destruct Htyp_f as [_ Hwf_Prod].
        apply r_prod_ty_inv in Hwf_Prod. destruct Hwf_Prod as [Hwf_A Hwf_B].
        apply r_wfTermLambda.
        -- exact Hwf_A.
        -- eapply r_wfTermConv.
           ++ eapply r_wfTermApp.
              ** assert (Hweak : [Γ,,r A |-r f⟨↑⟩ : (r_Prod A B)⟨↑⟩]).
              {eapply r_weak_term_lemma in r. instantiate (1:=A) in r. auto. }
              asimpl in Hweak. exact Hweak.
              ** apply r_wfVar0. exact Hwf_A.
           ++ rewrite subst_up_var_0_russ. apply r_TypeRefl. exact Hwf_B.
      * exact r.
    + (* r_TermRefl *)
      split. { apply r_TermRefl; eassumption. }
      split; assumption.
    + (* r_ConvConv *)
      destruct IHRuss_ConvTermDecl as [Heq_tt' [Htyp_t Htyp_t']].
      split. { eapply r_ConvConv; eassumption. }
      split.
      * eapply r_wfTermConv; eauto.
      * eapply r_wfTermConv; eauto.
    + (* r_TermSym *)
      destruct IHRuss_ConvTermDecl as [Heq_tt' [Htyp_t Htyp_t']].
      split. { apply r_TermSym; eassumption. }
      split; assumption.
    + (* r_TermTrans *)
      destruct IHRuss_ConvTermDecl1 as [Heq_tt' [Htyp_t Htyp_t']].
      destruct IHRuss_ConvTermDecl2 as [Heq_t't'' [Htyp_t'2 Htyp_t'']].
      split. { eapply r_TermTrans; eassumption. }
      split; assumption.
    + (* r_TermUnivCumul *)
      destruct IHRuss_ConvTermDecl as [Heq_AB [Htyp_A Htyp_B]].
      split. { eapply r_TermUnivCumul; eassumption. }
      split.
      * eapply r_wfTermCumul; eauto.
      * eapply r_wfTermCumul; eauto.

  (* r_wftype_typing_inv *)
  - intros. split.
    + exact H.
    + induction H.
      * apply r_weak_lemma. assumption.
      * apply r_weak_lemma. assumption.
      * apply product_wf_ty. auto. auto. 
      * inversion IHRuss_TypingDecl1. subst. eapply r_substitution_lemma. apply r_prod_ty_inv in IHRuss_TypingDecl1.
        destruct IHRuss_TypingDecl1. exact r0. exact H0.
      * apply r_type_defeq_inv in r. destruct r as [_ [_ HwfB]]. exact HwfB.
      * eapply r_wfTypeUniv. apply r_inv_wfcontext_wftype in IHRuss_TypingDecl1. destruct IHRuss_TypingDecl1. apply r_wfTermUniv. auto. auto.
      * eapply r_wfTypeUniv. apply r_wfTermUniv. auto. auto.
      * eapply r_wfTypeUniv. apply r_inv_wfcontext_wftype in IHRuss_TypingDecl. destruct IHRuss_TypingDecl. apply r_wfTermUniv. auto. auto.

  (* r_wftype_hypothesis_inv *)
  - intros. remember (Γ ,,r A) as Γ' in H.
    dependent induction H; intros; subst; try discriminate.
    + inversion r; subst. constructor; auto. constructor. auto.
    + split.
      * eapply r_typing_hypothesis_inv in r. destruct r as [? []]. auto.
      * eapply r_wfTypeUniv. exact r. 

  (* r_typing_hypothesis_inv *)
  - intros. split.
    + apply r_inv_wfcontext_typing in H. inversion H. inversion H1. auto.
    + split.
      * inversion H; subst.
        ** assumption.
        ** assumption.
        ** apply r_inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** apply r_inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** apply r_inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** apply r_inv_wfcontext_typing in H. inversion H. inversion H3. auto.
        ** inversion H0; subst; assumption.
        ** apply r_inv_wfcontext_typing in H. inversion H. inversion H3. auto.
      * exact H.

  (* r_conv_hypothesis_wftype *)
  - intros A B Hwf Hconv. eapply r_context_conversion_ty with (Δ := εr).
    + simpl. exact Hwf.
    + reflexivity.
    + exact Hconv.

  (* r_conv_hypothesis_typing *)
  - intros A B a Htyp Hconv. eapply r_context_conversion_term with (Δ := εr).
    + simpl. exact Htyp.
    + reflexivity.
    + exact Hconv.

  (* r_conv_hypothesis_type_eq *)
  - intros Heq Hconv. eapply r_context_conversion_ty_eq with (Δ := εr).
    + simpl. exact Heq.
    + reflexivity.
    + exact Hconv.

  (* r_conv_hypothesis_term_eq *)
  - intros  Heq Hconv. eapply r_context_conversion_term_eq with (Δ := εr).
    + simpl. exact Heq.
    + reflexivity.
    + exact Hconv.
Admitted.
