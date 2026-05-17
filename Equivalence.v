From Coq Require Import ssreflect Lia Program.Equality PeanoNat Lists.List Arith.
Require Import RussellTarskiEquivalence.core.
Require Import RussellTarskiEquivalence.unscoped.
Require Import RussellTarskiEquivalence.Autosubst.
Require Import RussellTarskiEquivalence.Syntax.
Require Import RussellTarskiEquivalence.Typing.
Require Import RussellTarskiEquivalence.Utils.
Require Import RussellTarskiEquivalence.Erasure.


Lemma simplify_induction {Γ A0 A1 l0 l1 k v0 v1 u0 u1}:
    [Γ |- A0 = U l0] ->
    [Γ |- A1 = U l1] ->
    [Γ |- u0 = cLift k l0 v0 : A0] ->
    [Γ |- u1 = cLift k l1 v1 : A1] ->
    [Γ |- v0 = v1 : U k] ->
    [Γ |- A0 = A1] ->
    [Γ |- u0 = u1 : A0].
Proof.
    intros. apply TypeSym in H. apply TypeTrans with (1:=H) in H4. apply TypeSym in H0, H4. apply TypeTrans with (1:=H0) in H4. apply UInj in H4. subst.
    apply TypeSym in H. apply TypeTrans with (1:=H) in H0. apply TypeSym in H0. apply TermConv with (1:= H2) in H0.
    eapply TermLiftingCong in H3. eapply TermTrans. exact H1. eapply TermTrans. eapply TermConv. exact H3. auto using TypeSym. auto using TermSym.
    apply typing_defeq_inv in H0. destruct H0 as [? []]. apply lift_inv_plus in t0. destruct t0 as [? [? [? []]]]. auto. 
Qed.

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

Lemma erase_var_inv {Γ t}:
    forall A A1 n,
    [Γ |- var_term n : A] ->
    [Γ |- t : A1] ->
    r_var_term n = erase_term t ->
    ([Γ |- var_term n = t : A] × [Γ |- A = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- var_term n = cLift k l0 v0 : A]
        × [Γ |- t = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ).
Proof.
    induction t; intros A A1 n0 Hvar Ht Herase;
    try (simpl in Herase; discriminate).
    
    - (* t = var_term *)
      simpl in Herase. injection Herase. intro Heq. subst.
      apply inl. split.
      + apply TermRefl. exact Hvar.
      + eapply var_ctx_inv; eauto.
      
    - (* t = cLift k_t l_t t *)
      simpl in Herase. rename l into k_t. rename l0 into l_t.
      
      pose proof Ht as Ht_orig.
      apply lift_inv_plus in Ht. destruct Ht as [n1 [H_A1_Un1 [H_lt_n1 [H_kt_lt H_t_Ukt]]]].
      subst n1.
      
      specialize (IHt A (U k_t) n0 Hvar H_t_Ukt Herase).
      
      destruct IHt as [[Heq_var_t H_A_Ukt] | [l0' [l1' [k_in [v0 [v1 [H_A_Ul0 [H_Ukt_Ul1 [H_var_lift [H_t_lift H_v0_v1]]]]]]]]]].
      + 
        apply inr. eexists k_t, l_t, k_t, (var_term n0), t.
        repeat split; auto.
        * 
          eapply TermConv. instantiate (1:= U k_t).
          -- apply TermLiftSame. eapply wfTermConv. exact Hvar. exact H_A_Ukt.
          -- apply TypeSym. exact H_A_Ukt.
        * (* cLift k_t l_t t = cLift k_t l_t t *)
          apply TermRefl. exact Ht_orig.
        * 
          eapply TermConv. exact Heq_var_t. exact H_A_Ukt.
          
      +
        apply UInj in H_Ukt_Ul1. subst l1'.
        apply inr. eexists l0', l_t, k_in, v0, v1.
        repeat split; auto.
        * 
          eapply TermConv. instantiate (1:= U l_t).
          eapply TermTrans. instantiate (1:= cLift k_t l_t (cLift k_in k_t v1)).
          -- apply TermLiftingCong. exact H_t_lift. exact H_kt_lt.
          -- apply TermLiftingCumul.
             ++ apply typing_defeq_inv in H_v0_v1. destruct H_v0_v1 as [_ [_ Hwf_v1]]. exact Hwf_v1.
             ++ apply typing_defeq_inv in H_t_lift. destruct H_t_lift as [_ [_ Hwf_t]]. apply lift_inv in Hwf_t. destruct Hwf_t as [_ [H_kin_kt _]]. exact H_kin_kt.
             ++ exact H_kt_lt.
          -- apply TypeSym. exact H_A1_Un1.
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
        + intros. simpl in H4.
          exfalso.
          apply lift_inv_plus in H0. 
          destruct H0 as [n_lift [Heq_A1 [Hl_n [Hk_l Htyp_inner]]]].
        
          eapply IHt in H4; eauto.
          
          apply typing_defeq_inv in H4. 
          destruct H4 as [_ [_ Htyp_inner_prod]].
          
          eapply cohesion_prod_univ.
          * exact Htyp_inner_prod.
          * exact Htyp_inner.     
Qed.

Lemma erase_app_inv {Γ t}:
    forall A B f a A0 A1,
    [Γ |- App A B f a : A0] ->
    [Γ |- t : A1] ->
    (forall C, [Γ |- A] -> [Γ |- C] -> (erase_ty A = erase_ty C) -> [Γ |- A = C]) ->
    (forall C, [Γ,, A |- B] -> [Γ,,A |- C] -> (erase_ty B = erase_ty C) -> [Γ,,A |- B = C]) ->
    (forall Γ' u1 A1',
    [Γ' |- f : Prod A B] ->
    [Γ' |- u1 : A1'] ->
    (erase_term f = erase_term u1) ->
    ([Γ' |- f = u1 : Prod A B] × [Γ' |- Prod A B = A1'])
    + (∑ l0 l1 k v0 v1, [Γ' |- Prod A B = U l0] 
        × [Γ' |- A1' = U l1]
        × [Γ' |- f = cLift k l0 v0 : Prod A B]
        × [Γ' |- u1 = cLift k l1 v1 : A1']
        × [Γ' |- v0 = v1 : U k] )) ->
    (forall Γ' u1 A1',
    [Γ' |- a : A] ->
    [Γ' |- u1 : A1'] ->
    (erase_term a = erase_term u1) ->
    ([Γ' |- a = u1 : A] × [Γ' |- A = A1']) 
    + (∑ l0 l1 k v0 v1, [Γ' |- A = U l0] 
        × [Γ' |- A1' = U l1]
        × [Γ' |- a = cLift k l0 v0 : A] 
        × [Γ' |- u1 = cLift k l1 v1 : A1']
        × [Γ' |- v0 = v1 : U k] )) ->
    r_App (erase_ty A) (erase_ty B) (erase_term f) (erase_term a) = erase_term t ->
    ([Γ |- App A B f a = t : A0 ] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- App A B f a = cLift k l0 v0 : A0]
        × [Γ |- t = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ).
Proof.
    induction t; intros A B f a A0 A1 H_App H_t Hinj_A Hinj_B H_f H_a Herase;
    try (simpl in Herase; discriminate).
    
    - (* t = App t1 t2 t3 t4 *)
      simpl in Herase. injection Herase. intros Heq_a Heq_f Heq_B Heq_A.
      
      pose proof H_App as Happ_orig.
      
      apply app_inv in H_App. destruct H_App as [Heq_A0_subst [HwfA [HwfB [Htyp_f Htyp_a]]]].
      
      pose proof H_t as Ht_orig.
      apply app_inv in H_t. destruct H_t as [Heq_A1_subst [HwfA0_t [HwfB0_t [Htyp_f0 Htyp_a0]]]].
      
      assert (HeqA : [Γ |- A = t1]).
      { apply Hinj_A. exact HwfA. exact HwfA0_t. exact Heq_A. }
      
      assert (HeqB : [Γ,, A |- B = t2]). 
      { apply Hinj_B. 
        - exact HwfB. 
        - eapply conv_hypothesis_wftype. exact HwfB0_t. apply TypeSym. exact HeqA. 
        - exact Heq_B. }
      
      assert (Htyp_f0_conv : [Γ |- t3 : Prod A B]).
      { eapply wfTermConv. 
        - exact Htyp_f0. 
        - apply TypeSym. apply TypePiCong. 
          ++ exact HwfA. 
          ++ exact HeqA. 
          ++ exact HeqB. }
      
      specialize (H_f Γ t3 (Prod A B) Htyp_f Htyp_f0_conv Heq_f).
      destruct H_f as [[Heq_f_conv H_Prod_eq] | Right_f].
      
      + 
        assert (Htyp_a0_conv : [Γ |- t4 : A]).
        { eapply wfTermConv. 
          - exact Htyp_a0. 
          - apply TypeSym. exact HeqA. }
        specialize (H_a Γ t4 A Htyp_a Htyp_a0_conv Heq_a).
        
        destruct H_a as [[Heq_a_conv H_A_eq] | Right_a].
        * 
          apply inl. split.
          -- eapply TermConv. 
             ++ apply TermAppCong.
                ** exact HeqA.
                ** exact HeqB.
                ** exact Heq_f_conv.
                ** exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A0_subst.
          -- eapply TypeTrans. exact Heq_A0_subst.
             eapply TypeTrans. instantiate (1 := t2[t4..]).
             ++ eapply subst_cong. exact HeqB. exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A1_subst.

        * 
          assert (Heq_a_conv : [Γ |- a = t4 : A]).
          { eapply simplify_induction_grouped. exact Right_a. apply TypeRefl. exact HwfA. }
          apply inl. split.
          -- eapply TermConv.
             ++ apply TermAppCong.
                ** exact HeqA.
                ** exact HeqB.
                ** exact Heq_f_conv.
                ** exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A0_subst.
          -- eapply TypeTrans. exact Heq_A0_subst.
             eapply TypeTrans. instantiate (1 := t2[t4..]).
             ++ eapply subst_cong. exact HeqB. exact Heq_a_conv.
             ++ apply TypeSym. exact Heq_A1_subst.

      +
        destruct Right_f as [l0' [l1' [k [v0 [v1 [Heq_Prod_U _]]]]]].
        exfalso. eapply cohesion_prod_univ. 
        ++ exact Htyp_f.
        ++ eapply wfTermConv. exact Htyp_f. exact Heq_Prod_U.
        
    -
      simpl in Herase. rename l into k_t. rename l0 into l_t.
      
      pose proof H_t as Ht_orig.
      apply lift_inv_plus in H_t. destruct H_t as [n1 [H_A1_Un1 [H_lt_n1 [H_kt_lt H_t_Ukt]]]].
      subst n1.
      
      specialize (IHt A B f a A0 (U k_t) H_App H_t_Ukt Hinj_A Hinj_B H_f H_a Herase).
      
      destruct IHt as [[Heq_App_t H_A0_Ukt] | [l0' [l1' [k_in [v0 [v1 [H_A0_Ul0 [H_Ukt_Ul1 [H_App_lift [H_t_lift H_v0_v1]]]]]]]]]].
      + 
        apply inr. eexists k_t, l_t, k_t, (App A B f a), t.
        repeat split; auto.
        *
          eapply TermConv. instantiate (1:= U k_t).
        -- apply TermLiftSame. eapply wfTermConv. exact H_App. exact H_A0_Ukt.
          -- apply TypeSym. exact H_A0_Ukt.
        *
          apply TermRefl. exact Ht_orig.
        * 
          eapply TermConv. exact Heq_App_t. exact H_A0_Ukt.
          
      +
        apply UInj in H_Ukt_Ul1. subst l1'.
        apply inr. eexists l0', l_t, k_in, v0, v1.
        repeat split; auto.
        * 
          eapply TermConv. instantiate (1:= U l_t).
          eapply TermTrans. instantiate (1:= cLift k_t l_t (cLift k_in k_t v1)).
          -- apply TermLiftingCong. exact H_t_lift. exact H_kt_lt.
          -- apply TermLiftingCumul.
             ++ apply typing_defeq_inv in H_v0_v1. destruct H_v0_v1 as [_ [_ Hwf_v1]]. exact Hwf_v1.
             ++ apply typing_defeq_inv in H_t_lift. destruct H_t_lift as [_ [_ Hwf_t]]. apply lift_inv in Hwf_t. destruct Hwf_t as [_ [H_kin_kt _]]. exact H_kin_kt.
             ++ exact H_kt_lt.
          -- apply TypeSym. exact H_A1_Un1.
Qed.


Lemma erase_cprod_inv {Γ t}:
    forall a b l A0 A1,
    [Γ |- cProd l a b : A0] ->
    [Γ |- t : A1] ->
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

    (forall Γ' u1 A1,
    [Γ' |- b : U l] -> 
    [Γ' |- u1 : A1] ->
    (erase_term b = erase_term u1) ->
    ([Γ' |- b = u1 : U l] × [Γ' |- U l = A1])
    + (∑ l0 l1 k v0 v1, [Γ' |- U l = U l0] 
        × [Γ' |- A1 = U l1]
        × [Γ' |- b = cLift k l0 v0 : U l]
        × [Γ' |- u1 = cLift k l1 v1 : A1]
        × [Γ' |- v0 = v1 : U k] )) ->
    r_Prod (erase_term a) (erase_term b) = erase_term t ->

    ([Γ |- cProd l a b = t : A0 ] × [Γ |- A0 = A1])
    + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
        × [Γ |- A1 = U l1]
        × [Γ |- cProd l a b = cLift k l0 v0 : A0]
        × [Γ |- t = cLift k l1 v1 : A1]
        × [Γ |- v0 = v1 : U k] ).
Proof.
  induction t; intros a b l_ A0 A1 Hprod Ht Ha Hb Herase;
  
  try (simpl in Herase; discriminate).

  - (* t = cProd l_t t1 t2 *)
    rename l into l_t.
    simpl in Herase. injection Herase. intros Heb Hea.
    
    apply code_prod_inv_plus in Hprod. destruct Hprod as [n_A0 [H_A0_Ul [H_l_nA0 [H_a_Ul H_b_Ul]]]]. subst n_A0.
    apply code_prod_inv_plus in Ht. destruct Ht as [n' [H_A1_Ult [H_lt_n' [H_t1_Ult H_t2_Ult]]]]. subst n'.

    specialize (Ha Γ t1 (U l_t) H_a_Ul H_t1_Ult Hea).

    assert (H_dec_eq : [Γ |- Decode l_ a = Decode l_t t1]).
    {
      destruct Ha as [[Heq_a H_Ul] | [l0' [l1' [ka [va [va' [H_Ul [H_Ult [H_a_lift [H_t1_lift H_va_eq]]]]]]]]]].
      - apply UInj in H_Ul. subst l_t.
        apply TypeDecodeCong. exact Heq_a.
      - apply UInj in H_Ul. subst l0'.
        apply UInj in H_Ult. subst l1'.
        
        eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
        { apply TypeDecodeCong. exact H_a_lift. }
        eapply TypeTrans. instantiate (1 := Decode ka va).
        { apply TypeSym. apply TypeDecodeLiftConv.
          - apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [Hwf_va _]]. exact Hwf_va.
          - apply typing_defeq_inv in H_a_lift. destruct H_a_lift as [_ [_ H_lift_a]].
            apply lift_inv in H_lift_a. destruct H_lift_a as [_ [H_ka_l _]]. exact H_ka_l. }
        eapply TypeTrans. instantiate (1 := Decode ka va').
        { apply TypeDecodeCong. exact H_va_eq. }
        eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
        { apply TypeDecodeLiftConv.
          - apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [_ Hwf_va']]. exact Hwf_va'.
          - apply typing_defeq_inv in H_t1_lift. destruct H_t1_lift as [_ [_ H_lift_t1]].
            apply lift_inv in H_lift_t1. destruct H_lift_t1 as [_ [H_ka_lt _]]. exact H_ka_lt. }
        { apply TypeSym. apply TypeDecodeCong. exact H_t1_lift. }
    }

    assert (Ht2_trans : [Γ ,, Decode l_ a |- t2 : U l_t]).
    { eapply conv_hypothesis_typing. exact H_t2_Ult. apply TypeSym. exact H_dec_eq. }

    specialize (Hb (Γ ,, Decode l_ a) t2 (U l_t) H_b_Ul Ht2_trans Heb).

    destruct Ha as [[Heq_a H_Ul_a] | [l0_a [l1_a [ka [va [va' [H_Ul_a [H_Ult_a [H_a_lift [H_t1_lift H_va_eq]]]]]]]]]].
    
    +
      apply UInj in H_Ul_a. subst l_t.
      destruct Hb as [[Heq_b H_Ul_b] | [l0_b [l1_b [kb [vb [vb' [H_Ul_b [H_Ult_b [H_b_lift [H_t2_lift H_vb_eq]]]]]]]]]].
      *
        apply inl. split.
        -- eapply TermConv. instantiate (1:= U l_).
           apply TermPiCong. exact H_a_Ul. exact Heq_a. exact Heq_b.
           apply TypeSym. exact H_A0_Ul.
        -- eapply TypeTrans. instantiate (1 := U l_). exact H_A0_Ul. apply TypeSym. exact H_A1_Ult.
      
      *
        apply UInj in H_Ul_b. subst l0_b. 
        apply UInj in H_Ult_b. subst l1_b. 
        assert (Heq_b : [Γ ,, Decode l_ a |- b = t2 : U l_]).
        { eapply TermTrans. exact H_b_lift. 
          eapply TermTrans. 2: { apply TermSym. exact H_t2_lift. }
          apply TermLiftingCong. exact H_vb_eq.
          apply typing_defeq_inv in H_b_lift. destruct H_b_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        apply inl. split.
        -- eapply TermConv. instantiate (1:= U l_).
           apply TermPiCong. exact H_a_Ul. exact Heq_a. exact Heq_b.
           apply TypeSym. exact H_A0_Ul.
        -- eapply TypeTrans. instantiate (1 := U l_). exact H_A0_Ul. apply TypeSym. exact H_A1_Ult.

    +
      apply UInj in H_Ul_a. subst l0_a. 
      apply UInj in H_Ult_a. subst l1_a.
      
      destruct Hb as [[Heq_b H_Ul_b] | [l0_b [l1_b [kb [vb [vb' [H_Ul_b [H_Ult_b [H_b_lift [H_t2_lift H_vb_eq]]]]]]]]]].
      * 
        apply UInj in H_Ul_b. subst l_t.
        assert (Heq_a : [Γ |- a = t1 : U l_]).
        { eapply TermTrans. exact H_a_lift. 
          eapply TermTrans. 2: { apply TermSym. exact H_t1_lift. }
          apply TermLiftingCong. exact H_va_eq.
          apply typing_defeq_inv in H_a_lift. destruct H_a_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        apply inl. split.
        -- eapply TermConv. instantiate (1:= U l_).
           apply TermPiCong. exact H_a_Ul. exact Heq_a. exact Heq_b.
           apply TypeSym. exact H_A0_Ul.
        -- eapply TypeTrans. instantiate (1 := U l_). exact H_A0_Ul. apply TypeSym. exact H_A1_Ult.

      * (* Lifts *)
        apply UInj in H_Ul_b. subst l0_b. 
        apply UInj in H_Ult_b. subst l1_b.
        
        assert (H_va_U : [Γ |- va : U ka]).
        { apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [Hwf _]]. exact Hwf. }
        assert (H_vb_U : [Γ ,, Decode l_ a |- vb : U kb]).
        { apply typing_defeq_inv in H_vb_eq. destruct H_vb_eq as [_ [Hwf _]]. exact Hwf. }
        assert (H_ka_l : ka <= l_).
        { apply typing_defeq_inv in H_a_lift. destruct H_a_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        assert (H_kb_l : kb <= l_).
        { apply typing_defeq_inv in H_b_lift. destruct H_b_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        
        assert (H_va'_U : [Γ |- va' : U ka]).
        { apply typing_defeq_inv in H_va_eq. destruct H_va_eq as [_ [_ Hwf]]. exact Hwf. }
        assert (H_vb'_U : [Γ ,, Decode l_ a |- vb' : U kb]).
        { apply typing_defeq_inv in H_vb_eq. destruct H_vb_eq as [_ [_ Hwf]]. exact Hwf. }
        assert (H_ka_lt : ka <= l_t).
        { apply typing_defeq_inv in H_t1_lift. destruct H_t1_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }
        assert (H_kb_lt : kb <= l_t).
        { apply typing_defeq_inv in H_t2_lift. destruct H_t2_lift as [_ [_ Hwf]]. apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }

        destruct (lt_eq_lt_dec ka kb) as [[H_ka_lt_kb | H_ka_eq_kb] | H_kb_lt_ka].
        
        ++ apply inr. eexists l_, l_t, kb.
           eexists (cProd kb (cLift ka kb va) vb), (cProd kb (cLift ka kb va') vb').
           
           assert (H_dec_kb : [Γ |- Decode l_ a = Decode kb (cLift ka kb va)]).
           { eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
             { apply TypeDecodeCong. exact H_a_lift. }
             eapply TypeTrans. instantiate (1 := Decode ka va).
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va_U. exact H_ka_l. } 
             { apply TypeDecodeLiftConv. exact H_va_U. lia. } 
           }
           
           assert (H_dec_kb' : [Γ |- Decode l_t t1 = Decode kb (cLift ka kb va')]).
           { eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
             { apply TypeDecodeCong. exact H_t1_lift. }
             eapply TypeTrans. instantiate (1 := Decode ka va').
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va'_U. exact H_ka_lt. } 
             { apply TypeDecodeLiftConv. exact H_va'_U. lia. } 
           }

           repeat split.
           -- exact H_A0_Ul.
           -- exact H_A1_Ult.
           -- eapply TermConv. instantiate (1:= U l_).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_a_Ul. 
                 *** eapply TermTrans. exact H_a_lift. apply TermSym. eapply TermLiftingCumul. exact H_va_U. instantiate(1:=kb). lia. exact H_kb_l.
                 *** exact H_b_lift.
              ** apply TermSym. apply TermLiftingProdConv.
                 *** apply wfTermcLift. exact H_va_U. lia.
                 *** eapply conv_hypothesis_typing. exact H_vb_U. exact H_dec_kb.
                 *** exact H_kb_l.
              ** apply TypeSym. exact H_A0_Ul.
           -- eapply TermConv. instantiate (1:= U l_t).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_t1_Ult.
                 *** eapply TermTrans. exact H_t1_lift. apply TermSym. eapply TermLiftingCumul. exact H_va'_U. instantiate(1:=kb). lia. exact H_kb_lt.
                 *** eapply conv_hypothesis_term_eq. exact H_t2_lift. exact H_dec_eq.
              ** apply TermSym. apply TermLiftingProdConv.
                 *** apply wfTermcLift. exact H_va'_U. lia.
                 *** eapply conv_hypothesis_typing. 2: { exact H_dec_kb'. }
                     eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                 *** exact H_kb_lt.
              ** apply TypeSym. exact H_A1_Ult.
           -- apply TermPiCong. 
              ** apply wfTermcLift. exact H_va_U. lia.
              ** apply TermLiftingCong. exact H_va_eq. lia.
              ** eapply conv_hypothesis_term_eq. exact H_vb_eq. exact H_dec_kb.

        ++ subst kb. apply inr. eexists l_, l_t, ka.
           eexists (cProd ka va vb), (cProd ka va' vb').

           assert (H_dec_ka : [Γ |- Decode l_ a = Decode ka va]).
           { eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
             { apply TypeDecodeCong. exact H_a_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va_U. exact H_ka_l. } 
           }
           
           assert (H_dec_ka' : [Γ |- Decode l_t t1 = Decode ka va']).
           { eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
             { apply TypeDecodeCong. exact H_t1_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va'_U. exact H_ka_lt. } 
           }

           repeat split.
           -- exact H_A0_Ul.
           -- exact H_A1_Ult.
           -- eapply TermConv. instantiate (1:= U l_).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_a_Ul. exact H_a_lift. exact H_b_lift.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va_U.
                 eapply conv_hypothesis_typing. exact H_vb_U. exact H_dec_ka.
                 exact H_ka_l.
              ** apply TypeSym. exact H_A0_Ul.
           -- eapply TermConv. instantiate (1:= U l_t).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_t1_Ult. exact H_t1_lift. 
                 eapply conv_hypothesis_term_eq. exact H_t2_lift. exact H_dec_eq.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va'_U.
                 eapply conv_hypothesis_typing. 2: { exact H_dec_ka'. }
                 eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                 exact H_ka_lt.
              ** apply TypeSym. exact H_A1_Ult.
           -- apply TermPiCong. exact H_va_U. exact H_va_eq.
              eapply conv_hypothesis_term_eq. exact H_vb_eq. exact H_dec_ka.

        ++ (* kb < ka *)
           apply inr. eexists l_, l_t, ka.
           eexists (cProd ka va (cLift kb ka vb)), (cProd ka va' (cLift kb ka vb')).

           assert (H_dec_ka : [Γ |- Decode l_ a = Decode ka va]).
           { eapply TypeTrans. instantiate (1 := Decode l_ (cLift ka l_ va)).
             { apply TypeDecodeCong. exact H_a_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va_U. exact H_ka_l. } 
           }
           
           assert (H_dec_ka' : [Γ |- Decode l_t t1 = Decode ka va']).
           { eapply TypeTrans. instantiate (1 := Decode l_t (cLift ka l_t va')).
             { apply TypeDecodeCong. exact H_t1_lift. }
             { apply TypeSym. apply TypeDecodeLiftConv. exact H_va'_U. exact H_ka_lt. } 
           }

           repeat split.
           -- exact H_A0_Ul.
           -- exact H_A1_Ult.
           -- eapply TermConv. instantiate (1:= U l_).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_a_Ul. exact H_a_lift.
                 *** eapply TermTrans. exact H_b_lift. apply TermSym. eapply TermLiftingCumul. exact H_vb_U. instantiate(1:=ka). lia. exact H_ka_l.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va_U.
                 apply wfTermcLift. eapply conv_hypothesis_typing. exact H_vb_U. exact H_dec_ka.
                 lia. exact H_ka_l.
              ** apply TypeSym. exact H_A0_Ul.
           -- eapply TermConv. instantiate (1:= U l_t).
              eapply TermTrans. 
              ** eapply TermPiCong. exact H_t1_Ult. exact H_t1_lift.
                 *** eapply TermTrans. eapply conv_hypothesis_term_eq. exact H_t2_lift. exact H_dec_eq.
                     apply TermSym. eapply TermLiftingCumul. eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                     instantiate(1:=ka). lia. exact H_ka_lt.
              ** apply TermSym. apply TermLiftingProdConv. exact H_va'_U.
                 apply wfTermcLift. eapply conv_hypothesis_typing. 2: { exact H_dec_ka'. }
                 eapply conv_hypothesis_typing. exact H_vb'_U. exact H_dec_eq.
                 lia. exact H_ka_lt.
              ** apply TypeSym. exact H_A1_Ult.
           -- apply TermPiCong. exact H_va_U. exact H_va_eq.
              apply TermLiftingCong. eapply conv_hypothesis_term_eq. exact H_vb_eq. exact H_dec_ka.
              lia.

  - (* t = cLift k_t l_t t *)
    rename l into k_t. rename l0 into l_t.
    simpl in Herase.
    
    pose proof Hprod as Hprod_orig.
    
    apply code_prod_inv_plus in Hprod. destruct Hprod as [n_A0 [H_A0_Ul [H_l_nA0 [H_a_Ul H_b_Ul]]]]. subst n_A0.
    apply lift_inv_plus in Ht. destruct Ht as [n' [H_A1_Un' [H_lt_n' [H_kt_lt H_t'_Ukt]]]]. subst n'.
    
    specialize (IHt a b l_ A0 (U k_t) Hprod_orig H_t'_Ukt Ha Hb Herase).
    
    destruct IHt as [[Heq_cProd H_A0_Ukt] | [l0' [l1' [k_in [v0 [v1 [H_A0_Ul0 [H_Ukt_Ul1 [H_cProd_lift [H_t'_lift H_v0_v1]]]]]]]]]].
    +
      assert (H_U_eq : [Γ |- U l_ = U k_t]).
      { eapply TypeTrans. apply TypeSym. exact H_A0_Ul. exact H_A0_Ukt. }
      apply UInj in H_U_eq. subst k_t.
      
      apply inr. eexists l_, l_t, l_.
      eexists (cProd l_ a b). eexists t.
      repeat split; auto.
      * eapply TermConv. instantiate (1 := U l_).
        -- apply TermLiftSame. eapply wfTermConv. exact Hprod_orig. exact H_A0_Ul.
        -- apply TypeSym. exact H_A0_Ul.
      * apply TermRefl. eapply wfTermConv. eapply wfTermcLift; eauto. auto using TypeSym.
      * eapply TermConv. exact Heq_cProd. exact H_A0_Ul.
      
    +
      assert (H_U_eq0 : [Γ |- U l_ = U l0']).
      { eapply TypeTrans. apply TypeSym. exact H_A0_Ul. exact H_A0_Ul0. }
      apply UInj in H_U_eq0. subst l0'.
      
      apply UInj in H_Ukt_Ul1. subst l1'.
      
      apply inr. eexists l_, l_t, k_in.
      eexists v0. eexists v1.
      
      repeat split; auto.
      
      assert (H_kin_kt : k_in <= k_t).
      { apply typing_defeq_inv in H_t'_lift. destruct H_t'_lift as [_ [_ Hwf]].
        apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt. }

      eapply TermConv. instantiate (1:= U l_t).
      eapply TermTrans. instantiate (1:= cLift k_t l_t (cLift k_in k_t v1)).
      
      * apply TermLiftingCong. exact H_t'_lift. exact H_kt_lt.
      * apply TermLiftingCumul.
        -- apply typing_defeq_inv in H_v0_v1. destruct H_v0_v1 as [_ [_ Hwf_v1]]. exact Hwf_v1.
        -- exact H_kin_kt.
        -- exact H_kt_lt.
      * apply TypeSym. exact H_A1_Un'.
Qed.


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
    apply TermSym. eapply TermConv. instantiate (1:=U l1). apply TermLiftingUnivConv. apply inv_wfcontext_typing in t. destruct t. all: auto using TypeSym. lia. lia. 
    constructor. eapply TermConv. instantiate (1:= U l2). rewrite c0. eapply TermTrans.
    instantiate (1:= cU l l2). apply TermLiftingUnivConv. apply inv_wfcontext_typing in t. destruct t. auto.
    auto. rewrite c0 in l3. auto. apply TermSym. apply TermLiftingUnivConv. apply inv_wfcontext_typing in t. destruct t. auto.
    lia. auto. auto. lia. rewrite e. auto using TypeSym. apply TermRefl. constructor. apply inv_wfcontext_typing in t. destruct t. auto.
    lia. 
    
    - intros. simpl in H1. assert (H0bis:=H0). apply lift_inv_plus in H0bis. destruct H0bis as [? [? [? []]]].
    assert (t0bis:=t0). apply lift_inv_plus in t0bis. destruct t0bis as [? [? [? []]]].
    apply UInj in c0. symmetry in e0. rewrite e0 in c0. rewrite c0 in l3.  apply TermLiftingCumul with (1:=t1) (2:= l4) in l3.
    apply typing_defeq_inv in l3. destruct l3 as [? []]. 
    eapply IHt with (1:= H) (2:= t3) in H1. destruct H1 as [projT5 [projT6 [projT7 [? [? [? []]]]]]].
    eexists projT5. eexists projT6. eexists projT7.
    constructor. auto.
    constructor. rewrite e. auto.
    constructor. auto.
    constructor. eapply TermConv. instantiate (1:= U l2). eapply TermTrans. instantiate (1:= cLift l l2 t).
    rewrite c0. auto. auto. rewrite e. auto using TypeSym. auto.
Qed. 

Lemma decode_eq_simpl {Γ u0 l0} :
  forall u1 l1,
  ([Γ |- u0 = u1 : U l0] × [Γ |- U l0 = U l1])
  + (∑ l0' l1' k v0 v1, [Γ |- U l0 = U l0'] 
      × [Γ |- U l1 = U l1']
      × [Γ |- u0 = cLift k l0' v0 : U l0]
      × [Γ |- u1 = cLift k l1' v1 : U l1]
      × [Γ |- v0 = v1 : U k] ) ->
  [Γ |- Decode l1 u1 = Decode l0 u0].
Proof.
  intros u1 l1 Hsum.
  destruct Hsum as [[Heq_term Heq_U] | [l0' [l1' [k [v0 [v1 [HU1 [HU2 [Hlift1 [Hlift2 Hveq]]]]]]]]]].
  
  - apply UInj in Heq_U. subst l1.
    
    apply TypeSym. 
    apply TypeDecodeCong. exact Heq_term.
  
  - apply UInj in HU1. subst l0'.
    apply UInj in HU2. subst l1'.
    
    eapply TypeTrans.
    + instantiate (1 := Decode l1 (cLift k l1 v1)).
      apply TypeDecodeCong. exact Hlift2.
    + eapply TypeTrans.
      * instantiate (1 := Decode k v1).
        apply TypeSym. apply TypeDecodeLiftConv.
        -- apply typing_defeq_inv in Hveq. destruct Hveq as [_ [_ Hwf]]. exact Hwf.
        -- apply typing_defeq_inv in Hlift2. destruct Hlift2 as [_ [_ Hwf]]. 
           apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt.
      * eapply TypeTrans.
        -- instantiate (1 := Decode k v0).
           apply TypeSym. apply TypeDecodeCong. exact Hveq.
        -- eapply TypeTrans.
           ++ instantiate (1 := Decode l0 (cLift k l0 v0)).
              apply TypeDecodeLiftConv.
              ** apply typing_defeq_inv in Hveq. destruct Hveq as [_ [Hwf _]]. exact Hwf.
              ** apply typing_defeq_inv in Hlift1. destruct Hlift1 as [_ [_ Hwf]]. 
                 apply lift_inv in Hwf. destruct Hwf as [_ [Hlt _]]. exact Hlt.
           ++ apply TypeSym. apply TypeDecodeCong. exact Hlift1.
Qed.


(* ----- Principal lemma : judgemental injectivity of erasure ----- *)

Scheme ty_rect_mut := Induction for ty Sort Type
with term_rect_mut := Induction for term Sort Type.

Combined Scheme mut_ind_ty_term from ty_rect_mut, term_rect_mut.

Definition P_erase_ty (A : ty) :=
  forall Γ B, [Γ |- A] -> [Γ |- B] -> (erase_ty A = erase_ty B) -> [Γ |- A = B].

Definition P_erase_term (u0 : term) :=
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

Definition P_erase_decode_inv (t: term) :=
    forall Γ l B,
    [Γ |- t : U l] ->
    [Γ |- B] ->
    erase_ty B = erase_term t ->
    [Γ |- B = Decode l t].

Definition P_term_combined (u0 : term) :=
  (P_erase_term u0 * P_erase_decode_inv u0)%type.

Theorem erase_inj_mutual :
  (forall A, P_erase_ty A) * (forall u0, P_term_combined u0).
Proof.
  apply mut_ind_ty_term. 
  unfold P_erase_ty, P_term_combined, P_erase_term, P_erase_decode_inv.

  (* ---- erase_inj_ty ---- *)
  
  (* Prod t t0 *)
  - intros t IHA1 t0 IHA2 Γ B H_wfA H_wfB Herase.
    destruct B as [B1 B2 | | ].
    all: try (simpl in Herase; contradict Herase; congruence).
    + simpl in Herase. inversion Herase. apply TypePiCong. apply prod_ty_inv in H_wfA. destruct H_wfA. auto.
        ++ apply IHA1. apply prod_ty_inv in H_wfA,H_wfB. destruct H_wfA,H_wfB. auto. auto. inversion H_wfB. auto. auto.
        ++ apply IHA2. apply prod_ty_inv in H_wfA,H_wfB. destruct H_wfA,H_wfB. auto. auto. inversion H_wfB. eapply conv_hypothesis_wftype.
            instantiate (1:= B1). auto. apply TypeSym. apply IHA1. apply prod_ty_inv in H_wfA,H_wfB. destruct H_wfA,H_wfB. auto.
            apply prod_ty_inv in H_wfA,H_wfB. destruct H_wfA,H_wfB. auto. auto. auto.
    + simpl in Herase. apply erase_decode_inv_prod. auto. constructor.
      apply prod_ty_inv in H_wfA. destruct H_wfA. auto. apply prod_ty_inv in H_wfA. destruct H_wfA. auto.
      specialize (IHA1 Γ). exact IHA1.
      specialize (IHA2 (Γ,,t)). exact IHA2. auto.

  (* Decode l t *)
  - intros l t [p p0] Γ B H_wfA H_wfB Herase.
    apply TypeSym. 
    eapply p0.
    + apply decode_ty_inv in H_wfA. exact H_wfA.
    + exact H_wfB.
    + simpl in Herase. symmetry. exact Herase.


  (* U n *)
  - intros n Γ B H_wfA H_wfB Herase. destruct B.
    all: try (simpl in Herase; contradict Herase; congruence).
    + apply erase_decode_inv_univ; auto.
    + simpl in Herase. inversion Herase. subst.
      apply TypeRefl. exact H_wfA.

  (* ----- erase_inj_term et erase_decode_inv ----*)

  (* var_term n *)
  - split.
  
    (* erase_inj_term *)
    + intros Γ u1 A0 A1 Htyp0 Htyp1 Herase. apply erase_var_inv. all:auto.

    (* erase_decode_inv *)
    +  intros Γ u1 B Hterm Htyp Herase. destruct B.
      all: try(simpl in Herase; contradict Herase; congruence).
      ++ simpl in Herase. apply decode_ty_inv in Htyp. apply sym_eq in Herase. apply erase_var_inv with (1:=Hterm) (2:=Htyp) in Herase.
      apply decode_eq_simpl. auto.

  (* Lambda t t0 u *)
  - intros t IHA t0 IHB u [IHu IHu_decode]. split.
  
    (* erase_inj_term *)
    + intros Γ u1 A0 A1 Htyp0 Htyp1 Herase. destruct u1 as [ | t1_0 t2 u_1 | | | | ].
    all: try(simpl in Herase; contradict Herase; congruence).
    ++ simpl in Herase. injection Herase; intros Heq_u Heq_t0_erase Heq_t_erase.

        apply lambda_inv in Htyp0. destruct Htyp0 as [Heq_A0 Htyp_u].
        apply lambda_inv in Htyp1. destruct Htyp1 as [Heq_A1 Htyp_u1].

        apply wftype_typing_inv in Htyp_u. destruct Htyp_u as [Htyp_u Hwf_t0].
        apply wftype_typing_inv in Htyp_u1. destruct Htyp_u1 as [Htyp_u1 Hwf_t2].

        apply wftype_hypothesis_inv in Hwf_t0. destruct Hwf_t0 as [Hwf_t Hwf_t0].
        apply wftype_hypothesis_inv in Hwf_t2. destruct Hwf_t2 as [Hwf_t1_0 Hwf_t2].

        pose proof (IHA Γ t1_0 Hwf_t Hwf_t1_0 Heq_t_erase) as Heq_t.
        
        assert (Hwf_t0_conv : [Γ,, t1_0 |- t0]).
        { eapply conv_hypothesis_wftype. exact Hwf_t0. exact Heq_t. }
        
        pose proof (IHB (Γ,, t1_0) t2 Hwf_t0_conv Hwf_t2 Heq_t0_erase) as Heq_t0.

        assert (Htyp_u_conv : [Γ,, t1_0 |- u : t0]).
        { eapply conv_hypothesis_typing. exact Htyp_u. exact Heq_t. }

        pose proof (IHu (Γ,, t1_0) u_1 t0 t2 Htyp_u_conv Htyp_u1 Heq_u) as IHu_applied.
        
        pose proof (simplify_induction_bis IHu_applied Heq_t0) as [Heq_u_conv _].
        apply inl. split.
        *** eapply TermConv. instantiate (1:=Prod t t0). 
            **** eapply TermLambdaCong.
                 ----- exact Hwf_t.
                 ----- exact Heq_t.
                 ----- eapply conv_hypothesis_type_eq. instantiate (1:= t1_0). exact Heq_t0. apply TypeSym. exact Heq_t.
                 ----- eapply conv_hypothesis_term_eq. instantiate (1:= t1_0). exact Heq_u_conv. apply TypeSym. exact Heq_t. 
            **** apply TypeSym. exact Heq_A0.
        *** eapply TypeTrans. exact Heq_A0.
            eapply TypeTrans. 2: { apply TypeSym. exact Heq_A1. }
            apply TypePiCong. exact Hwf_t. exact Heq_t. 
            eapply conv_hypothesis_type_eq. instantiate (1:= t1_0). exact Heq_t0. apply TypeSym; exact Heq_t.

      ++ simpl in Herase.
       exfalso.
       assert (Hbis := Htyp0).
       apply lambda_inv in Hbis; destruct Hbis. apply wfTermConv with (1:=Htyp0) in c.
       
       eapply erase_lambda_inv with (1:= c) (2:= Htyp1) in Herase.
       
       -- apply typing_defeq_inv in Herase. destruct Herase as [_ [_ Htyp_u1_prod]].
          assert (Hbis := Htyp1). apply lift_inv_plus in Htyp1; destruct Htyp1 as [n_lift [Heq_A1_Un _]].
          
          eapply cohesion_prod_univ.
          ** exact Htyp_u1_prod.
          ** eapply wfTermConv. exact Hbis. exact Heq_A1_Un.
          
       -- intros C HC1 HC2 Heq. apply IHA; auto.
       -- intros C HC1 HC2 Heq. apply IHB; auto.
       -- intros Γ' u_1' A_1' Ht1_ Ht2_ Heq. apply IHu; auto.

    (* erase_decode_inv *)
    + intros Γ u1 B Hterm Htyp Herase. assert (H:=Hterm). apply lambda_inv in Hterm. destruct Hterm.
      exfalso. eapply cohesion_prod_univ. eapply wfTermConv. exact H. exact c. exact H.
      
  (* App t t0 t1 t2 *)
  - intros t IHA t0 IHB t1 [IHf IHf_decode] t2 [IHa IHa_decode]. split.
  
    + intros Γ u1 A0 A1 Htyp0 Htyp1 Herase.
      
      apply erase_app_inv with (A:=t) (B:=t0) (f:=t1) (a:=t2); auto.

    + intros Γ l_univ B Hterm Htyp Herase. destruct B.
      all: try(simpl in Herase; contradict Herase; congruence).
      ++ simpl in Herase. apply decode_ty_inv in Htyp. apply sym_eq in Herase. apply erase_app_inv with (1:=Hterm) (2:=Htyp) in Herase.
      apply decode_eq_simpl. auto. auto. auto. auto. auto.


  (* cProd l t t0 *)
  - intros l a [IHa IHa_decode] b [IHb IHb_decode]. split.
  
    + intros Γ u1 A0 A1 Htyp0 Htyp1 Herase.
      
      apply erase_cprod_inv with (a:=a) (b:=b) (l:=l); auto.
      
    + 
      intros Γ l_univ B Hterm Htyp Herase.  destruct B.
      all: try(simpl in Herase; contradict Herase; congruence).
      ++ simpl in Herase. inversion Herase. apply prod_ty_inv in Htyp. apply code_prod_inv in Hterm. destruct Hterm as [? []]. destruct Htyp.
      eapply IHa_decode in H0. eapply IHb_decode in H1. eapply TypeTrans. instantiate (1:= Prod (Decode l a) (Decode l b)).
      apply TypePiCong. auto. exact H0. exact H1. apply TypeSym. subst l. apply TypeDecodeProdConv. auto. auto. eapply conv_hypothesis_typing.
      exact t0. auto using TypeSym. auto. auto. auto.
      ++ simpl in Herase. apply decode_ty_inv in Htyp. apply sym_eq in Herase. apply erase_cprod_inv with (1:=Hterm) (2:=Htyp) in Herase.
      apply decode_eq_simpl. auto. auto. auto.

  (* cU k l *)
  - intros k l. split.
  
    + intros Γ u1 A0 A1 Htyp0 Htyp1 Herase.
      destruct u1 as [ | | | | l0 l2 | ].
      all: try(simpl in Herase; contradict Herase; congruence).
      
      ++ simpl in Herase. injection Herase; intro H_k_l0. subst l0.
         assert (Hbis:=Htyp0). apply code_univ_inv_bis in Hbis. destruct Hbis as [Heq_A0 Hlt_kl].
         assert (H0bis:=Htyp1). apply code_univ_inv_bis in H0bis. destruct H0bis as [Heq_A1 Hlt_kl2].
         apply inr. 
         
         eexists l, l2. set (l_min:=(Nat.min l l2)).
         eexists l_min, (cU k l_min), (cU k l_min).
         
         split. { exact Heq_A0. }
         split. { exact Heq_A1. }
         split.
         *** apply TermSym. eapply TermConv. instantiate (1:= U l).
             apply TermLiftingUnivConv.  
             apply inv_wfcontext_typing in Htyp0. destruct Htyp0. auto. lia. lia. auto using TypeSym.
         *** split. 
             **** apply TermSym. eapply TermConv. instantiate (1:= U l2).
                  apply TermLiftingUnivConv. 
                  apply inv_wfcontext_typing in Htyp0. destruct Htyp0. auto. lia. lia. auto using TypeSym.
             **** apply TermRefl. constructor. 
                  apply inv_wfcontext_typing in Htyp0. destruct Htyp0. auto.
                  lia. 

      ++ simpl in Herase. apply inr. eexists _, _. apply erase_cuniv_inv; eauto.

    + intros Γ l_univ B Hterm Htyp Herase. destruct B.
      all: try(simpl in Herase; contradict Herase; congruence).
      ++ simpl in Herase. apply decode_ty_inv in Htyp. apply sym_eq in Herase. 
      destruct t as [ | | | | l1 l2 | ].
            all: try(simpl in Herase; contradict Herase; congruence).

      
        +++ simpl in Herase. injection Herase; intro H_k_l0. subst l1.
          assert (Hbis:=Hterm). apply code_univ_inv_bis in Hbis. destruct Hbis as [Heq_A0 Hlt_kl].
          assert (H0bis:=Htyp). apply code_univ_inv_bis in H0bis. destruct H0bis as [Heq_A1 Hlt_kl2]. 
          apply UInj in Heq_A0,Heq_A1. subst. eapply TypeTrans. apply TypeSym. apply TypeDecodeConv. apply inv_wfcontext_typing in Hterm. destruct Hterm.
          auto. auto. apply TypeDecodeConv. apply inv_wfcontext_typing in Hterm. destruct Hterm. auto. auto. 
                                                      

        +++ simpl in Herase. apply erase_cuniv_inv with (1:=Hterm) (2:=Htyp) in Herase.
          destruct Herase as [k0 [v0 [v1 [H1 [H2 [Hlift1 [Hlift2 Hconv]]]]]]]. apply code_univ_inv_bis in Hterm. destruct Hterm. apply UInj in c.
          apply lift_inv in Htyp. destruct Htyp as [? []]. subst. eapply TypeTrans. eapply TypeDecodeCong. exact Hlift2.
          eapply TypeTrans. apply TypeSym. apply TypeDecodeLiftConv. apply typing_defeq_inv in Hconv. destruct Hconv as [? []]. auto.
          apply typing_defeq_inv in Hlift2. destruct Hlift2 as [? []]. apply lift_inv in t2. destruct t2 as [? []]. auto.
          eapply TypeTrans. eapply TypeDecodeCong. apply TermSym. exact Hconv.
          eapply TypeTrans. apply TypeDecodeLiftConv. apply typing_defeq_inv in Hconv. destruct Hconv as [? []]. auto.
          apply typing_defeq_inv in Hlift1. destruct Hlift1 as [? []]. apply lift_inv in t2. destruct t2 as [? []]. exact l2.
          apply TypeDecodeCong. auto using TermSym.
      
      ++ simpl in Herase. inversion Herase. apply code_univ_inv_bis in Hterm. destruct Hterm. apply UInj in c. subst.
          apply TypeDecodeConv. apply inv_wfcontext_wftype in Htyp. destruct Htyp. auto. auto.  
         

  (* cLift k l t *)
  - intros k l t [IHt IHt_decode]. split.

    + intros Γ u1 A0 A1 Htyp0 Htyp1 Herase.
      
      assert (Hbis:= Htyp0). apply lift_inv_plus in Hbis.
      destruct Hbis as [n_lift [H_A0_Un [H_l_n [H_k_l H_t_Uk]]]].
      
      simpl in Herase.
      
      pose proof (IHt Γ u1 (U k) A1 H_t_Uk Htyp1 Herase) as IHt_applied. 
      
      destruct IHt_applied as [ [c c0] | s ].
      
      ++  symmetry in H_l_n. rewrite H_l_n in H_A0_Un. 
          
          apply TypeSym in c0. 
          apply inr.
          
          eexists l, k, k, t, u1.
          
          split. { exact H_A0_Un. }
          split. { exact c0. }
          split. { apply TermRefl. exact Htyp0. }
          split. 
          *** eapply TermConv. instantiate (1:= U k).
              apply TermLiftSame. 
              eapply wfTermConv. exact Htyp1. exact c0.
              apply TypeSym. exact c0.
          *** exact c.

      ++ destruct s as [l0_ih [l1_ih [k_ih [v0_ih [v1_ih [Hc_U [Hc_A1 [Hc_t [Hc_u1 Hc_v]]]]]]]]].
         apply inr.
         
         apply UInj in Hc_U. subst l0_ih.
         symmetry in H_l_n. subst n_lift.
         
         eexists l, l1_ih, k_ih, v0_ih, v1_ih.
         
         split. { exact H_A0_Un. }
         split. { exact Hc_A1. }
         split.
         *** eapply TermConv. instantiate (1:= U l).
             eapply TermTrans. 
             instantiate (1:= cLift k l (cLift k_ih k v0_ih)).
             **** apply TermLiftingCong. exact Hc_t. exact H_k_l.
             **** apply TermLiftingCumul.
                  ---- apply typing_defeq_inv in Hc_t. destruct Hc_t as [_ [_ Hwf_v0]]. apply lift_inv in Hwf_v0. destruct Hwf_v0 as [? []]. exact t0.
                  ---- apply typing_defeq_inv in Hc_t. destruct Hc_t as [_ [_ Hwf_lift]].
                       apply lift_inv in Hwf_lift. destruct Hwf_lift as [_ [Hlt _]]. exact Hlt.
                  ---- exact H_k_l.
             **** apply TypeSym. exact H_A0_Un.
         *** split. 
             **** exact Hc_u1.
             **** exact Hc_v.

    (* erase_decode_inv *)
    + intros Γ l_univ B Hterm Htyp Herase. apply lift_inv in Hterm. destruct Hterm as [? []]. simpl in Herase. subst.
      eapply IHt_decode in Herase. eapply TypeTrans. exact Herase. apply TypeDecodeLiftConv. auto. auto. auto. auto.
Qed.


Lemma erase_inj_ty {Γ A} :
  forall B,
  [Γ |- A] ->
  [Γ |- B] ->
  erase_ty A = erase_ty B ->
  [Γ |- A = B].
Proof.
  intros B HwfA HwfB Herase.
  eapply (fst erase_inj_mutual A).
  - exact HwfA.
  - exact HwfB.
  - exact Herase.
Qed.

Lemma erase_inj_term {Γ u0} :
  forall u1 A0 A1,
  [Γ |- u0 : A0] ->
  [Γ |- u1 : A1] ->
  erase_term u0 = erase_term u1 ->
  ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1])
  + (∑ l0 l1 k v0 v1, [Γ |- A0 = U l0] 
      × [Γ |- A1 = U l1]
      × [Γ |- u0 = cLift k l0 v0 : A0]
      × [Γ |- u1 = cLift k l1 v1 : A1]
      × [Γ |- v0 = v1 : U k] ).
Proof.
  intros u1 A0 A1 Htyp0 Htyp1 Herase.
  eapply (fst (snd erase_inj_mutual u0)).
  - exact Htyp0.
  - exact Htyp1.
  - exact Herase.
Qed.

Lemma erase_decode_inv {Γ l t B} :
  [Γ |- t : U l] ->
  [Γ |- B] ->
  erase_ty B = erase_term t ->
  [Γ |- B = Decode l t].
Proof.
  intros Htyp Hwf Herase.
  eapply (snd (snd erase_inj_mutual t)).
  - exact Htyp.
  - exact Hwf.
  - exact Herase.
Qed.


Lemma erase_inj_term_plus {u0}:
    forall Γ u1 A0 A1,
    [Γ |- u0 : A0] ->
    [Γ |- u1 : A1] ->
    (erase_term u0 = erase_term u1) ->
    (erase_ty A0 = erase_ty A1) ->
    ([Γ |- u0 = u1 : A0] × [Γ |- A0 = A1]).
Proof.
    intros. apply erase_inj_term with (1:=H) (2:=H0) in H1. apply wftype_typing_inv in H, H0. destruct H, H0. apply erase_inj_ty with (1:= w) (2:=w0) in H2.
    destruct H1.
    - auto.
    - apply simplify_induction_grouped. auto. auto. 
Qed.

Theorem erase_inj_ctx_mutual :
  (forall Γ (H:[|- Γ]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> True) *
  ((forall Γ A (H:[Γ |- A]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- A]) *
  ((forall Γ a A (H:[Γ |- a : A]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- a : A]) *
  ((forall Γ A B (H:[Γ |- A = B]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- A = B]) *
  (forall Γ a b A (H:[Γ |- a = b : A]), forall Γ', [|- Γ'] -> erase_context Γ = erase_context Γ' -> [Γ' |- a = b : A])))).
Proof.
  apply mut_ind_erasure_rect; intros.
  
  all: try match goal with H : erase_context _ = erase_context _ |- _ => rename H into Heq end.
  all: try match goal with H : [ |- _ ] |- _ => rename H into HwfG' end.

  (* --- WfContextDecl --- *)
  - (* connil *) trivial.
  - (* concons *)
    destruct Γ' as [|A' Γ']; simpl in Heq; try discriminate.
    injection Heq; intros HeqA HeqG.
    inversion HwfG'.
    apply H with (1:=H3) (2:=HeqA).

  (* --- WfTypeDecl --- *)
  - (* wfTypeU *) constructor; auto.
  - (* wfTypeProd *)
    apply wfTypeProd.
    + apply H; auto. 
    + apply H0.      
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.
  - (* wfTypeDecode *) constructor. apply H; auto.

  (* --- TypingDecl --- *)
  - (* wfVar0  *)
    destruct Γ' as [|A' Γ']; simpl in Heq; try discriminate.
    injection Heq; intros HeqA HeqG.
    inversion HwfG'.
    assert (Heq_types: [Γ' |- A = A']).
    { apply erase_inj_ty. apply H with (1:=H2); auto. auto. auto. }
    eapply wfTermConv.
    + apply wfVar0. exact H3.
    + apply TypeSym. apply weak_cong. exact Heq_types.

  - (* wfVarN *)
    destruct Γ' as [|A' Γ']; simpl in Heq; try discriminate.
    injection Heq; intros HeqA HeqG.
    inversion HwfG'.
    apply wfVarN.
    + exact H4.
    + apply H0; auto.

    - (* wfTermcProd *)
    apply wfTermcProd.
    + apply H; auto.
    + apply H0; auto.
    + apply H1.
      * constructor. apply HwfG'. apply wfTypeDecode. apply H; auto.
      * simpl. rewrite Heq. auto.

    - econstructor. eauto. eauto.
    - econstructor. eauto. eauto.

  - (* wfTermLambda *)
    apply wfTermLambda.
    + apply H; auto.
    + apply H0.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.

    - econstructor. eauto. eauto.
  - econstructor. eauto. eauto.
  - econstructor. eauto. eauto.
    assert (Heq' : erase_context (Γ,,A) = erase_context (Γ',,A)).
    {simpl. rewrite Heq. auto. }
    apply H1. econstructor. eauto. eauto. eauto.

  - econstructor. eauto.
  - econstructor. eauto. eauto.
  - econstructor. eauto. eauto.

  - (* TypeDecodeProdConv*)
    apply TypeDecodeProdConv.
    + apply H; auto.
    + apply H0.
      * constructor. apply HwfG'. apply wfTypeDecode. apply H; auto.
      * simpl. rewrite Heq. auto.

  - econstructor. eauto.
  - econstructor. eauto. eauto.
  - apply TypeSym. eauto.

  - (* TermBRed *)
    eapply TermBRed.
    + apply H; auto.
    + apply H0.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.
    + apply H1; auto.

  (* --- ConvTermDecl --- *)
  - (* TermPiCong *)
    apply TermPiCong.
    + apply H; auto.
    + apply H0; auto.
    + apply H1.
      * constructor. apply HwfG'. apply wfTypeDecode. apply H; auto.
      * simpl. rewrite Heq. auto.

  - econstructor. eauto. apply H0. econstructor. eauto. eapply type_defeq_inv. apply TypeSym. eapply H.
    eauto. eauto. simpl. rewrite Heq. eauto. eauto. eauto.

  - (* TermLambdaCong *)
    apply TermLambdaCong.
    + apply H; auto.
    + apply H0; auto.
    + apply H1.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.
    + apply H2.
      * constructor. apply HwfG'. apply H; auto.
      * simpl. rewrite Heq. reflexivity.

  - (* TermLiftingProdConv : Extension de contexte *)
    apply TermLiftingProdConv; auto.
    + apply H0; auto. constructor. auto. constructor. auto. simpl. rewrite Heq. auto.
  
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. all: try(eauto).
  - econstructor. apply TermSym. eauto. apply TypeRefl. apply H in HwfG'. apply typing_defeq_inv in HwfG'. destruct HwfG' as [? []].
    apply wftype_typing_inv in t1. destruct t1. eauto. eauto.
  - eapply TermTrans. eauto. eauto. 
Qed.

Lemma erase_inj_ctx_term {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall a A, [Γ |- a : A] -> [Γ' |- a : A]).
Proof.
  intros Γ' HwfG HwfG' Heq a A Htyp.
  eapply (fst (snd (snd erase_inj_ctx_mutual))).
  - exact Htyp.
  - exact HwfG'.
  - exact Heq.
Qed.

Lemma erase_inj_ctx_type {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall A, [Γ |- A] -> [Γ' |- A]).
Proof.
  intros Γ' HwfG HwfG' Heq A Htyp.
  eapply (fst (snd erase_inj_ctx_mutual)).
  - exact Htyp.
  - exact HwfG'.
  - exact Heq.
Qed.

Lemma erase_inj_ctx_conv_ty {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall A B, [Γ |- A = B] -> [Γ' |- A = B]).
Proof.
  intros Γ' HwfG HwfG' Heq A B Hconv.
  eapply (fst (snd (snd (snd erase_inj_ctx_mutual)))).
  - exact Hconv.
  - exact HwfG'.
  - exact Heq.
Qed.

Lemma erase_inj_ctx_conv_term {Γ} :
    forall Γ',
    [ |- Γ] ->
    [ |- Γ'] ->
    (erase_context Γ = erase_context Γ') ->
    (forall u v A, [Γ |- u = v : A ] -> [Γ' |- u = v : A ]).
Proof.
  intros Γ' HwfG HwfG' Heq u v A Hconv.
  eapply (snd (snd (snd (snd erase_inj_ctx_mutual)))).
  - exact Hconv.
  - exact HwfG'.
  - exact Heq.
Qed.


Lemma decode_prod_structure_from_erasure:
  forall t Γ l A B,
  [Γ |- t : U l] ->
  erase_term t = r_Prod A B ->
  ∑  A1 B1,
    [Γ |- Decode l t = Prod A1 B1] ×
    erase_ty A1 = A ×
    erase_ty B1 = B.
Proof.
  induction t; intros; simpl in H0; try discriminate.
  (* cProd *)
  - injection H0; intros; subst.
    apply code_prod_inv in H. destruct H as [? [? ?]]. subst.
    eexists (Decode l0 t1), (Decode l0 t2).
    split.
    + apply TypeDecodeProdConv; auto.
    + simpl. split; auto.
  (* cLift *)
  - apply lift_inv in H. destruct H as [? [? ?]]. subst.
    specialize (IHt _ _ _ _  t0 H0).
    destruct IHt as [A1 [B1 [Heq [HA HB]]]].
    exists A1, B1.
    split.
    + eapply TypeTrans. 
      2: exact Heq.
      apply TypeSym. apply TypeDecodeLiftConv; auto.
    + split; auto.
Qed.

(* ----- Principal théorème d'équivalence ----- *)
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
    + destruct IHRuss_WfContextDecl as [? []]. apply section_ty in r. destruct r as [projT4 [projT5 [? []]]].
        eexists (projT4,,projT5). constructor. apply concons in w0. auto. apply inv_wfcontext_wftype in w0. destruct w0. auto.
        simpl. rewrite e1. rewrite e0. auto.

- intros. induction H.
    + apply section_ctx in r. destruct r as [projT3 []]. eexists projT3. eexists (U n).
        constructor. constructor. auto.
        constructor. auto. auto.
    + apply section_term in r. destruct r as [projT3 [projT4 [projT5 [? [? []]]]]]. eexists projT3. eexists (Decode n projT4).
        constructor. constructor. eapply wfTermConv. instantiate (1:=projT5). auto. eapply erase_inj_ty.
            apply wftype_typing_inv in t. destruct t. auto. constructor. apply inv_wfcontext_typing in t. destruct t. auto.
            auto. 
        constructor. auto. auto.

- intros. induction H.

    (* r_var0 *)
    + apply  section_ty in r. destruct r as [projT3 [projT4 [? []]]]. eexists (projT3,,projT4). eexists (var_term 0). eexists (projT4⟨↑⟩).
        constructor. eapply wfVar0. auto.
        constructor. symmetry in e. rewrite e. rewrite defeq_erase_weak_ty. auto.
        constructor. auto. simpl. rewrite e0. rewrite e. auto.

      (* r_VarN *)
    +  destruct IHRuss_TypingDecl as [projT3 [projT4 [projT5 [? [? []]]]]]. apply section_ty in r. destruct r as [projT6 [projT7 [? []]]]. eexists (projT3,,projT7).
        eexists (projT4⟨↑⟩). eexists (projT5⟨↑⟩).
        constructor. eapply weak_term_lemma. auto.
        constructor. rewrite <- defeq_erase_weak_ty. rewrite e. auto.
        constructor. rewrite <- defeq_erase_weak_term. rewrite e0. auto. 
        simpl. rewrite e1. rewrite e2. auto. 

    + (* r_Lambda *)
      destruct IHRuss_TypingDecl as [Γ_body [u_body [B_lifted [H_typing_body [H_erase_B [H_erase_u H_erase_ctx_body]]]]]].
      
      apply section_ty in r. destruct r as [Γ_A [A_lifted [H_wf_A [H_erase_A H_erase_ctx_A]]]].
      
      destruct Γ_body as [| A_body_head Γ_body_tail].
      * simpl in H_erase_ctx_body. discriminate.
      * simpl in H_erase_ctx_body. injection H_erase_ctx_body. intros H_eq_ctx H_eq_A.
      
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
           
      **
        simpl. rewrite H_erase_A H_erase_B. reflexivity.
      **
        simpl. rewrite H_erase_A H_erase_B H_erase_u. reflexivity.
      ** 
        exact H_erase_ctx_A.

    (* r_App *)
    + destruct IHRuss_TypingDecl1 as [Γ_f [f_t [Prod_t [Hf_typ [H_er_Prod [H_er_f H_er_ctx_f]]]]]].
      destruct IHRuss_TypingDecl2 as [Γ_a [a_t [A_t [Ha_typ [H_er_A [H_er_a H_er_ctx_a]]]]]].

      assert (H_Bt_exists : ∑ B_t, [Γ_f ,, A_t |- B_t] × erase_ty B_t = B).
      {   assert (Hf_typbis := Hf_typ).
          apply wftype_typing_inv in Hf_typ. destruct Hf_typ as [_ Hwf_Prod_t].
          destruct Prod_t.
          - (* Prod *)
            simpl in H_er_Prod. injection H_er_Prod. intros HeqB HeqA.
            apply prod_ty_inv in Hwf_Prod_t. destruct Hwf_Prod_t as [_ Hwf_B0].
            exists Prod_t2. split.
            + eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in Hwf_B0. destruct Hwf_B0. exact w0. apply concons.
              apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto.
              apply wftype_typing_inv in Ha_typ. destruct Ha_typ.
              eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in w. destruct w. exact w0.
              apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto. rewrite H_er_ctx_f. auto. auto.
              simpl. rewrite H_er_ctx_f. rewrite H_er_A. rewrite HeqA. auto. auto.
            + auto.
          - (* Decode *)
            simpl in H_er_Prod. apply decode_ty_inv in Hwf_Prod_t.
            apply decode_prod_structure_from_erasure with (A:=A) (B:=B) in Hwf_Prod_t; auto.
            destruct Hwf_Prod_t as [A1 [B1 [Heq_Decode [HeqA HeqB]]]].
            apply type_defeq_inv in Heq_Decode. destruct Heq_Decode as [_ [_ Hwf_Prod]].
            apply prod_ty_inv in Hwf_Prod. destruct Hwf_Prod as [_ Hwf_B1].
            exists B1. split.
            + eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in Hwf_B1. destruct Hwf_B1. exact w0.
              apply concons. apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto.
              apply wftype_typing_inv in Ha_typ. destruct Ha_typ.
              eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in w. destruct w. exact w0.
              apply inv_wfcontext_typing in Hf_typbis. destruct Hf_typbis. auto. rewrite H_er_ctx_f. auto. auto.
              simpl. rewrite H_er_ctx_f. rewrite H_er_A. rewrite HeqA. auto. auto.
            + auto.
          - (* U *)
            simpl in H_er_Prod. discriminate.
      }
      destruct H_Bt_exists as [B_t [H_wf_B H_er_B]].

      eexists Γ_f.
      eexists (App A_t B_t f_t a_t).
      eexists (B_t[a_t..]).

      repeat split.
      -- apply wfTermApp.
         --- 
             eapply wfTermConv.
             ---- exact Hf_typ.
             ---- 
                  apply erase_inj_ty.
                  ----- apply wftype_typing_inv in Hf_typ. destruct Hf_typ; auto.
                  -----
                        apply wfTypeProd.
                        ------ apply wftype_typing_inv in Ha_typ. destruct Ha_typ; auto.
                               eapply erase_inj_ctx_type. apply inv_wfcontext_wftype in w. destruct w. exact w0.
                               apply inv_wfcontext_typing in Hf_typ. destruct Hf_typ. auto. rewrite H_er_ctx_f. auto. auto.
                        ------ exact H_wf_B.
                  ----- simpl. rewrite H_er_Prod. rewrite H_er_A H_er_B. reflexivity.
         --- eapply erase_inj_ctx_term. apply inv_wfcontext_typing in Ha_typ. destruct Ha_typ. exact w.
             apply inv_wfcontext_typing in Hf_typ. destruct Hf_typ. auto. rewrite H_er_ctx_f. auto.
             auto.
      --
         rewrite <- defeq_erase_subst_ty. rewrite H_er_a H_er_B. reflexivity.
      -- 
         simpl. rewrite H_er_A H_er_B H_er_f H_er_a. reflexivity.
      -- exact H_er_ctx_f.

    + 
      destruct IHRuss_TypingDecl as [Γ1 [u1 [A1 [Htyp [HerA [HerU HerCtx]]]]]].
      apply section_conv in r. destruct r as [? [A2 [B1 [? [? []]]]]].
      eexists Γ1, u1, B1.
      split.
      * eapply wfTermConv.
        -- exact Htyp.
        -- eapply TypeTrans. instantiate (1:=A2).
           apply erase_inj_ty.
           --- apply wftype_typing_inv in Htyp. destruct Htyp. auto.
           --- apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
                eapply erase_inj_ctx_type. exact w1. apply inv_wfcontext_typing in Htyp. destruct Htyp. auto. rewrite e1. auto. auto.
           --- rewrite HerA. auto. 
           --- apply type_defeq_inv in c. destruct c as [? []]. apply inv_wfcontext_wftype in w. destruct w.
                eapply erase_inj_ctx_conv_ty. exact w1. apply inv_wfcontext_typing in Htyp. destruct Htyp. auto. rewrite e1. auto. auto.
      * split. auto. split. auto. auto.

    (* r_wfTermProd *)
    + destruct IHRuss_TypingDecl1 as [Γ1 [a1 [TA1 [Ha1 [HeTA1 [Hea1 HeG1]]]]]].
      destruct IHRuss_TypingDecl2 as [Γ2 [b1 [TB1 [Hb1 [HeTB1 [Heb1 HeG2]]]]]].
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

    (* r_wfTermUniv *)
    + apply section_ctx in r. destruct r as [Γ1 [HwfG HeG]].
      eexists Γ1, (cU n m), (U m).
      repeat split.
      * apply wfTermcUniv; auto.
      * auto.

    (* r_wfTermCumul *)
+ destruct IHRuss_TypingDecl as [Γ1 [u1 [A1 [Htyp [HerA [HerU HerCtx]]]]]].
      eexists Γ1, (cLift n m u1), (U m).
      repeat split.
      -- apply wfTermcLift; auto.
         eapply wfTermConv. exact Htyp. apply erase_inj_ty.
         --- apply wftype_typing_inv in Htyp; destruct Htyp; auto.
         --- apply wfTypeU. apply inv_wfcontext_typing in Htyp; destruct Htyp; auto.
         --- rewrite HerA. simpl. reflexivity.
         --- lia. 
      -- simpl. auto.
      -- simpl. auto.

- (* section_conv *)
  intros. induction H.

  (* r_TypePiCong *)
  + destruct IHRuss_ConvTypeDecl1 as [Γ1 [A1 [B1 [HconvA [HeA [HeB HeG1]]]]]].
    destruct IHRuss_ConvTypeDecl2 as [Γ2 [C1 [D1 [HconvC [HeC [HeD HeG2]]]]]].
    
    eexists Γ1, (Prod A1 C1), (Prod B1 D1).
    repeat split.
    * apply TypePiCong.
      -- apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
      -- exact HconvA.
      -- eapply erase_inj_ctx_conv_ty.
         --- apply type_defeq_inv in HconvC. destruct HconvC as [_ [HwfC _]]. apply inv_wfcontext_wftype in HwfC. destruct HwfC; exact w0.
         --- apply concons. 
             apply type_defeq_inv in HconvA. destruct HconvA as [_ [_ HwfB1]]. apply inv_wfcontext_wftype in HwfB1. destruct HwfB1; auto.
             apply type_defeq_inv in HconvA. destruct HconvA as [_ [HwfA _]]. exact HwfA.
         --- simpl. rewrite HeG2 HeG1 HeA. reflexivity.
         --- exact HconvC.
    * simpl. rewrite HeA HeC. reflexivity.
    * simpl. rewrite HeB HeD. reflexivity.
    * exact HeG1.

  (* r_TypeRefl *)
  + apply section_ty in r. destruct r as [Γ1 [A1 [Hwf [HeA HeG]]]].
    eexists Γ1, A1, A1.
    repeat split; try auto.
    apply TypeRefl. exact Hwf.

  (* r_TypeSym *)
  + destruct IHRuss_ConvTypeDecl as [Γ1 [A1 [B1 [Hconv [HeA [HeB HeG]]]]]].
    eexists Γ1, B1, A1.
    repeat split.
    * apply TypeSym. exact Hconv.
    * exact HeB.
    * exact HeA.
    * exact HeG.

    (* r_TypeTrans *)
  + destruct IHRuss_ConvTypeDecl1 as [Γ1 [A1 [B1 [Hconv1 [HeA [HeB1 HeG1]]]]]].
    destruct IHRuss_ConvTypeDecl2 as [Γ2 [B2 [C1 [Hconv2 [HeB2 [HeC HeG2]]]]]].
    
    eexists Γ1, A1, C1.
    repeat split; try auto.
    eapply TypeTrans.
    * exact Hconv1.
    * eapply TypeTrans. instantiate (1:=B2).
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

  (* r_TypeUnivConv *)
  + apply section_conv_term in r.
    destruct r as [Γ1 [u1 [v1 [T1 [Hconv [HeqT [Hequ [Heqv HeqG]]]]]]]].
    
    eexists Γ1, (Decode n u1), (Decode n v1).
    repeat split.
    * apply TypeDecodeCong.
      eapply TermConv.
      -- exact Hconv.
      -- destruct T1; simpl in HeqT.
         ++ discriminate.
         ++ apply TypeSym.
            apply erase_decode_inv_univ with (t:=t).
            ** apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]].
               apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT].
               exact HwfT.
            ** symmetry. exact HeqT.
         ++ injection HeqT. intro. subst l.
            apply TypeRefl. apply wfTypeU.
            apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]].
            apply inv_wfcontext_typing in Hwf. destruct Hwf. exact w.
    * simpl. exact Hequ.
    * simpl. exact Heqv.
    * exact HeqG.

(* section_conv_term *)
- intros. induction H.

    + apply section_term in r0. destruct r0 as [Γ1 [t1 [B1 [Htyp_t [HeB [Het HeG1]]]]]].
    apply section_term in r1. destruct r1 as [Γ2 [a1 [A1 [Htyp_a [HeA [Hea HeG2]]]]]].
    
    
    eexists (Γ2), (App A1 B1 (Lambda A1 B1 t1) a1), (t1[a1..]), (B1[a1..]).
    repeat split.
    * eapply TermBRed.
        -- apply wftype_typing_inv in Htyp_a. destruct Htyp_a. auto.
        --  eapply erase_inj_ctx_term. apply inv_wfcontext_typing in Htyp_t. destruct Htyp_t. exact w.
            apply inv_wfcontext_typing in Htyp_a. destruct Htyp_a. constructor. auto. apply wftype_typing_inv in t0. destruct t0. auto.
            simpl. rewrite HeG2. rewrite HeA. auto. auto.
        -- exact Htyp_a.
    * rewrite <- defeq_erase_subst_ty. rewrite HeB Hea. reflexivity.
    * simpl. rewrite HeA HeB Het Hea. reflexivity.
    * rewrite <- defeq_erase_subst_term. rewrite Hea Het. reflexivity.
    * auto.
    

    (* r_TermAppCong *)
    + apply section_conv in r. destruct r as [Γ1 [A1 [A'1 [HconvA [HeA [HeA' HeG1]]]]]].
    apply section_conv in r0. destruct r0 as [Γ2 [B1 [B'1 [HconvB [HeB [HeB' HeG2]]]]]].
    destruct IHRuss_ConvTermDecl1 as [Γ3 [f1 [g1 [Prod1 [Hconv_f [HeProd [Hef [Heg HeG3]]]]]]]].
    destruct IHRuss_ConvTermDecl2 as [Γ4 [a1 [b1 [Ta1 [Hconv_a [HeTa [Hea [Heb HeG4]]]]]]]].

    eexists Γ1, (App A1 B1 f1 a1), (App A'1 B'1 g1 b1), (B1[a1..]).
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
        -- 
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

    (* r_TermLambdaCong *)
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
        -- eapply TermConv. instantiate (1:=B_body). eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv_t.
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

    (* r_TermPiCong *)
    + destruct IHRuss_ConvTermDecl1 as [Γ1 [u1 [v1 [T1 [Hconv1 [HeqT1 [Hequ1 [Heqv1 HeqG1]]]]]]]].
      destruct IHRuss_ConvTermDecl2 as [Γ2 [u2 [v2 [T2 [Hconv2 [HeqT2 [Hequ2 [Heqv2 HeqG2]]]]]]]].

      eexists Γ1, (cProd n u1 u2), (cProd n v1 v2), (U n).
      repeat split.
      * apply TermPiCong.

        -- eapply wfTermConv.
           --- apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. exact Htyp.
           --- apply erase_inj_ty.
               ++ apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
                 apply wftype_typing_inv in Htyp. destruct Htyp. exact w.
               ++ apply wfTypeU. apply typing_defeq_inv in Hconv1. 
                 destruct Hconv1 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
                 destruct Htyp. exact w.
               ++ rewrite HeqT1. simpl. reflexivity.

        -- eapply TermConv. exact Hconv1.
           apply erase_inj_ty.
           --- apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
               apply wftype_typing_inv in Htyp. destruct Htyp. exact w.
           --- apply wfTypeU. apply typing_defeq_inv in Hconv1. 
               destruct Hconv1 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
               destruct Htyp. exact w.
           --- rewrite HeqT1. simpl. reflexivity.

        -- eapply erase_inj_ctx_conv_term.
           --- eapply concons.
               ++ apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
                 apply inv_wfcontext_typing in Htyp. destruct Htyp. exact w.
               ++ eapply wfTypeDecode. eapply wfTermConv.
                 ** apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. exact Htyp.
                 ** apply erase_inj_ty.
                    +++ apply typing_defeq_inv in Hconv1. destruct Hconv1 as [_ [Htyp _]]. 
                        apply wftype_typing_inv in Htyp. destruct Htyp. exact w.
                    +++ apply wfTypeU. apply typing_defeq_inv in Hconv1. 
                        destruct Hconv1 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
                        destruct Htyp. exact w.
                    +++ rewrite HeqT1. simpl. reflexivity.
           --- apply typing_defeq_inv in Hconv2. destruct Hconv2 as [_ [Htyp _]]. 
               apply inv_wfcontext_typing in Htyp. destruct Htyp. constructor. eapply inv_wfcontext_typing.
               eapply typing_defeq_inv. exact Hconv1. constructor. eapply typing_defeq_inv. apply TermSym.
               eapply TermConv. exact Hconv1. apply erase_inj_ty. eapply wftype_typing_inv. eapply typing_defeq_inv.
               exact Hconv1. constructor. eapply inv_wfcontext_typing. eapply typing_defeq_inv. exact Hconv1. simpl. auto.
           --- simpl. rewrite HeqG1 Hequ1. rewrite <- HeqG2. reflexivity.
           --- eapply TermConv. eapply erase_inj_ctx_conv_term. apply typing_defeq_inv in Hconv2. destruct Hconv2 as [? []].
                apply inv_wfcontext_typing in t. destruct t. exact w. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                apply inv_wfcontext_typing in t. destruct t. exact w. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                eapply wfTermConv. exact t. apply erase_inj_ty. apply wftype_typing_inv in t. destruct t. auto. constructor. apply inv_wfcontext_typing in t.
                destruct t. auto. simpl. auto. simpl. rewrite HeqG1. rewrite Hequ1. auto. exact Hconv2.
               apply erase_inj_ty.
               ++ apply typing_defeq_inv in Hconv2. destruct Hconv2 as [_ [Htyp _]]. 
                 apply wftype_typing_inv in Htyp. destruct Htyp. apply wftype_typing_inv in t. destruct t. eapply erase_inj_ctx_type.
                 apply inv_wfcontext_typing in t. destruct t. exact w1. constructor.  apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                apply inv_wfcontext_typing in t0. destruct t0. auto. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                eapply wfTermConv. exact t0. apply erase_inj_ty. apply wftype_typing_inv in t0. destruct t0. auto. constructor. apply inv_wfcontext_typing in t0.
                destruct t0. auto. simpl. auto. simpl. rewrite HeqG1. rewrite Hequ1. auto. exact w0.
               ++ apply wfTypeU. apply typing_defeq_inv in Hconv2. 
                 destruct Hconv2 as [_ [Htyp _]]. apply inv_wfcontext_typing in Htyp. 
                 destruct Htyp.  constructor.  apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                apply inv_wfcontext_typing in t0. destruct t0. auto. constructor. apply typing_defeq_inv in Hconv1. destruct Hconv1 as [? []].
                eapply wfTermConv. exact t0. apply erase_inj_ty. apply wftype_typing_inv in t0. destruct t0. auto. constructor. apply inv_wfcontext_typing in t0.
                destruct t0. auto. simpl. auto.
               ++ rewrite HeqT2. simpl. reflexivity.

      * simpl. subst. auto.
      * simpl. subst. auto.
      * simpl. subst. auto.

    (* r_TermFunEta *)
    + apply section_term in r.
      destruct r as [Γ1 [f1 [Prod1 [Htyp_f [HeProd [Hef HeG1]]]]]].
      
      assert (∑ A1 B1, [Γ1 |- Prod1 = Prod A1 B1] × (erase_ty A1 = A) × (erase_ty B1 = B)).
      { 
          destruct Prod1; simpl in HeProd; try discriminate.
          - exists Prod1_1, Prod1_2.
            split; [| split]. 
            apply TypeRefl. apply wftype_typing_inv in Htyp_f. destruct Htyp_f; auto.
            injection HeProd; auto. injection HeProd; auto.
          - apply wftype_typing_inv in Htyp_f. destruct Htyp_f as [_ Hwf].
            apply decode_ty_inv in Hwf.
            apply decode_prod_structure_from_erasure with (A:=A) (B:=B) in Hwf; auto.
      }
      
      destruct H as [A1 [B1 [Hconv [HeA HeB]]]].

      eexists Γ1, (Lambda A1 B1 (App (A1⟨↑⟩) (B1⟨⇑⟩) (f1⟨↑⟩) (var_term 0))), f1, (Prod A1 B1).
      repeat split.
      * apply TermFunEta. 
        eapply wfTermConv. exact Htyp_f. exact Hconv.
      * simpl. rewrite HeA HeB. reflexivity.
      * simpl. rewrite HeA HeB. rewrite <- defeq_erase_weak_term.
        rewrite <- defeq_erase_weak_ty. rewrite <- defeq_erase_weak_ty_up. 
        rewrite HeA HeB Hef. reflexivity.
      * exact Hef.
      * exact HeG1.


    (* r_TermRefl *)
    + apply section_term in r. destruct r as [Γ1 [t1 [A1 [Htyp [HeA [Het HeG]]]]]].
    eexists Γ1, t1, t1, A1.
    repeat split; auto.
    apply TermRefl. exact Htyp.

    (* r_ConvConv *)
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

    (* r_TermSym *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [u1 [v1 [A1 [Hconv [HeA [Heu [Hev HeG]]]]]]]].
    eexists Γ1, v1, u1, A1.
    repeat split; auto.
    apply TermSym. exact Hconv.

    (* r_TermTrans *)
    + destruct IHRuss_ConvTermDecl1 as [Γ1 [t1 [t'1 [A1 [Hconv1 [HeA [Het [Het' HeG1]]]]]]]].
    destruct IHRuss_ConvTermDecl2 as [Γ2 [t'2 [t''1 [A2 [Hconv2 [HeA2 [Het'2 [Het'' HeG2]]]]]]]].

    eexists Γ1, t1, t''1, A1.
    repeat split; auto.
    * eapply TermTrans.
        -- exact Hconv1.
        -- eapply TermTrans.
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

    (* r_TermUnivCumul *)
    + destruct IHRuss_ConvTermDecl as [Γ1 [u1 [v1 [Up [Hconv [HeUp [Heu [Hev HeG]]]]]]]].
    eexists Γ1, (cLift p n u1), (cLift p n v1), (U n).
    repeat split.
    * apply TermLiftingCong.
        -- eapply TermConv. exact Hconv.
        apply erase_inj_ty.
        --- apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]]. apply wftype_typing_inv in Hwf. destruct Hwf as [_ HwfT]. exact HwfT.
        --- apply wfTypeU. apply typing_defeq_inv in Hconv. destruct Hconv as [_ [_ Hwf]]. apply inv_wfcontext_typing in Hwf. destruct Hwf; auto.
        --- rewrite HeUp. simpl. reflexivity.
        -- lia.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
Qed.