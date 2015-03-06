Add LoadPath ".".

Require Import SysF.
Require Import Arith.
Require Import Reduction.
Require Import Metatheory.

Section part_1.

    Definition interp (T : typ) (e : env) t :=
      normal t /\ typing e t T.

    Notation "t `in` [| T |] e" := (interp T e t) (at level 80).

    Theorem inversion_var :
      forall x e T, ((var x) `in` [|T|]e) <-> get_typ e x = Some T /\ wf_env e.
      split; intros.
      - inversion H. inversion H1. auto.
      - split. normalize. destruct H. apply t_var; auto.
    Qed.

    Theorem inversion_app :
      forall t1 t2 e T, ((app t1 t2) `in` [|T|]e) <->
                        exists T', t1 `in` [|tarr T' T|]e /\ t2 `in` [|T'|]e /\ neutral t1.
      split; intros.
      - inversion H. inversion H1. inversion H0. inversion H8. exists T1. split.
        + split. normalize. auto.
        + do 2 (split; auto).
      - do 2 destruct H. inversion H. inversion H0. inversion H3. split.
        + normalize.
        + eapply t_app; eauto.
    Qed.
    
    Theorem inversion_abs :
      forall T1 t e T, ((abs T1 t) `in` [|T|]e) <->
                       exists T2, T = tarr T1 T2 /\ t `in` [|T2|](evar T1 e).
      split; intros.
      - inversion H. inversion H1. exists T2. split; auto. split; auto.
        + inversion H0. inversion H8. auto.
      - do 2 destruct H. inversion H0. split.
        + normalize.
        + rewrite H; apply t_abs; auto. apply typing_wf_env in H2. apply H2.
    Qed.
    
    Theorem inversion_abs_t :
      forall K t e T, ((abs_t K t) `in` [|T|]e) <->
                      exists T2, T = tall K T2 /\ t `in` [|T2|](etvar K e).
      split; intros.
      - inversion H. inversion H1. exists T0. split; auto. split; auto.
        + inversion H0. inversion H7. normalize.
      - do 2 destruct H. inversion H0. split.
        + normalize.
        + rewrite H. apply t_abs_t. auto.
    Qed.
    
    Theorem inversion_app_t :
      forall t T' e T, ((app_t t T') `in` [|T|]e) <->
                       exists T'' K, T = tsubst T'' 0 T' /\ kinding e T' K
                                     /\ t `in` [|tall K T''|]e /\ neutral t.
      split; intros.
      - inversion H. inversion H0. inversion H1. inversion H2. 
        exists T1. exists K. repeat split; auto. normalize.
      - do 3 destruct H. destruct H0. destruct H1. inversion H1. split.
        + normalize.
        + rewrite H. eapply t_app_t; eauto.
    Qed. 
 
End part_1.

Section part_2.
  Inductive type_lt : env -> typ -> typ -> Prop :=
  | order_arrow_l e T1 T2 : type_lt e T1 (tarr T1 T2)
  | order_arrow_r e T1 T2 : type_lt e T2 (tarr T1 T2)
  | order_arrow_all e U T K :
      kinding e T K ->
      type_lt e (tsubst U 0 T) (tall K U).
  
  Section Lexicographic_Product.
    Variable A : Type.
    Variable B : Type.
    Variables eqA ltA : A -> A -> Prop.
    Variable ltB : B -> B -> Prop.
    
    Variable eqA_lt :
      forall a a',
        eqA a a' -> 
        forall a'',
          ltA a'' a' -> ltA a'' a.

    Variable eqA_trans :
      forall a a' a'',
        eqA a' a ->
        eqA a'' a ->
        eqA a' a''.
    
    Variable eqA_symm :
      forall a a',
        eqA a a' -> eqA a' a.

    Lemma Acc_eqA :
      forall a a',
        eqA a a' ->
        Acc ltA a ->
        Acc ltA a'.
      intros. apply Acc_intro. intros.
      destruct H0.
      eauto.
    Qed.
      
    Definition le_lexprod (p : A * B) (p' : A * B) :=
      let (a1, b1) := p in
      let (a2, b2) := p' in
      ltA a1 a2 \/ (eqA a1 a2 /\ ltB b1 b2).

    Lemma Acc_eqA_ltB :
      forall a b,
        Acc le_lexprod (a, b) ->
        forall a',
          eqA a a' -> 
          Acc le_lexprod (a', b).
      intros a b.
      intros H a' eq.
      apply Acc_intro. intros (a0, b0). intro le.
      destruct H.
      destruct le.
      - apply (eqA_lt a a' eq a0) in H0. apply H.
        left. auto.
      - destruct H0. apply H. right. split; eauto.
    Qed.
      
    Lemma acc_lexprod :
      well_founded ltB ->
      forall x, 
        Acc ltA x ->
        forall y,
          Acc ltB y ->
          Acc le_lexprod (x, y).
      do 3 intro.
      induction H0.
      - intros. induction H2.
        + apply Acc_intro. intros (a, b).
          inversion 1.
          * auto.
          * eapply Acc_eqA_ltB. apply H3. apply H5. apply eqA_symm. apply H5.
    Qed.

    Theorem my_wf_lexprod : 
      well_founded ltA ->
      well_founded ltB ->
      well_founded le_lexprod.
      intros wfA wfB.
      unfold well_founded.
      intros (a, b).
      auto using acc_lexprod.
    Qed.
  End Lexicographic_Product.

  Fixpoint num_quantifiers_variables (T : typ) : nat :=
    match T with
      | tvar _ => 1
      | tarr T1 T2 => (num_quantifiers_variables T1) + (num_quantifiers_variables T2)
      | tall _ T0 => 1 + (num_quantifiers_variables T0)
    end.
  
  Require Import Relation_Operators.
  Require Import Wellfounded.Inverse_Image.
  Require Import Wellfounded.Lexicographic_Product.

  Definition lt_option o1 o2 :=
    match o1, o2 with
      | None, None => False
      | None, Some _ => True
      | Some _, None => False
      | Some a, Some b => a < b
    end.
  
  Lemma Acc_none : Acc lt_option None.
    apply Acc_intro. intros. destruct y; inversion H.
  Qed.

  Lemma wf_lt_option : well_founded lt_option.
    unfold well_founded.
    intro. destruct a.
    - induction n. 
      + apply Acc_intro. intros. destruct y; inversion H. apply Acc_none.
      + apply Acc_intro. intros. destruct y.
        * inversion H. auto. destruct IHn. specialize (H2 (Some n0)). apply H2.
          simpl. auto.
        * apply Acc_none.
    - apply Acc_none.
  Qed.
  
  Definition pair_into_nats (p : env * typ) :=
    let (e, T) := p in
    existT (fun _ => nat) (kind_of e T) (num_quantifiers_variables T).

  Definition order p q :=
    lexprod (option nat) (fun _ => nat) (lt_option) (fun _ => lt) 
            (pair_into_nats p) (pair_into_nats q).
  
  Theorem wf_order : well_founded order.
    unfold order.
    apply wf_inverse_image.
    apply wf_lexprod.
    - apply wf_lt_option.
    - intro. auto with arith.
  Qed.

  Lemma num_quantifiers_variables_nonzero :
    forall (T : typ), num_quantifiers_variables T > 0.
    intro. induction T; simpl; auto with arith.
  Qed.
  
  (*
  Lemma type_order_order e : 
    forall (x y : typ), 
      kind_of e x <> None -> kind_of e y <> None ->
      type_lt e x y -> order (e, x) (e, y).
    intros.
    induction H1.
    - remember (kind_of e t1) as k1.
      remember (kind_of e (tarr t1 t2)) as k2.
      destruct k1, k2; try (exfalso; solve [auto]).
      unfold order.
      unfold pair_into_nats. rewrite <- Heqk1, <- Heqk2. simpl.
      assert (k = k0 \/ k < k0).
      { inversion Heqk2. rewrite <- Heqk1 in H2. 
        destruct (kind_of e t2); try (exfalso; solve[auto]).
        inversion H2. assert (k <= max k k1) by auto with arith. 
        destruct H1; auto with arith. }
      destruct H1.
      + rewrite <- H1. apply right_lex. 
        eauto using num_quantifiers_variables_nonzero with arith.
      + apply left_lex. auto.
    - remember (kind_of e t2) as k1.
      remember (kind_of e (tarr t1 t2)) as k2.
      destruct k1, k2; try (exfalso; solve [auto]).
      unfold order.
      unfold pair_into_nats. rewrite <- Heqk1, <- Heqk2. simpl.
      assert (k = k0 \/ k < k0).
      { inversion Heqk2. rewrite <- Heqk1 in H2. 
        destruct (kind_of e t1); try (exfalso; solve[auto]).
        inversion H2. assert (k <= max k1 k) by auto with arith.
        destruct H1; auto with arith. }
      destruct H1.
      + rewrite <- H1. apply right_lex.
        pose (num_quantifiers_variables_nonzero t1).
        omega.
      + apply left_lex. auto.
    - admit.
  Qed.
                             
  Lemma get_kind_S :
    forall (e : env) (i : nat),
      get_kind e (S i) <> None ->
      get_kind e i <> None.
    induction e; eauto.
    - intros. destruct i; eauto; discriminate.
  Qed.
  
  Require Import Correctness.

  Lemma tsubst_kind_of :
    forall t e n t' k,
      kind_of e t' = Some k ->
      kind_of e t <> None ->
      kind_of e (tsubst t n t') <> None.
    induction t; intros.
    - simpl. destruct lt_eq_lt_dec.
      + destruct s; try omega; auto.
        * intro. symmetry in H1. pose (eq_trans H1 H). discriminate.
      + destruct n. omega.
        assert (S n - 1 = n) by omega.
        rewrite H1.
        simpl.
        apply kind_of_correct in H.
        apply kinding_wf_env in H.
        apply bwf_env_complete in H.
        simpl in H0. 
        rewrite H in *.
        apply get_kind_S.
        auto.
    - simpl. simpl in H0. remember (kind_of e t1) as k1. remember (kind_of e t2) as k2.
      destruct k1, k2.
      + assert (H' := H). assert (H'' := H).
        apply (IHt1 e n) in H'. eapply (IHt2 e n) in H''.
        destruct (kind_of e (tsubst t1 n t')), (kind_of e (tsubst t2 n t'));
          try discriminate; intro; auto.
        * intro. pose (eq_trans Heqk2 H1). discriminate.
        * intro. pose (eq_trans Heqk1 H1). discriminate.
      + exfalso. apply H0. auto.
      + exfalso. apply H0. auto.
      + exfalso. apply H0. auto.
    - simpl. specialize (IHt (etvar k e) (S n) (tshift 0 t') k).
      admit.
      (* I know how to prove this! But we would need to duplicate a lot of theorems
       * from Metatheory.v for kind_of! *)
  Qed.

  Lemma tsubst_kind_lt :
    forall e t t' k,
      kind_of e t' = Some k ->
      kind_of e t <> None ->
      lt_option (kind_of e (tsubst t 0 t')) (kind_of e (tall k t)).
    induction t; intros.
    - simpl. destruct (lt_eq_lt_dec n 0).
      + destruct s; try omega.
        rewrite e0. rewrite H. apply (kind_of_correct t' e k) in H.
        apply kinding_wf_env in H.
        apply bwf_env_complete in H. rewrite H. simpl. auto with arith.
      + apply kind_of_correct in H. apply kinding_wf_env in H. apply bwf_env_complete in H.
        unfold kind_of. rewrite H. destruct n; try omega.
        assert (S n - 1 = n) by omega. rewrite H1.
        simpl in H0. rewrite H in *.
        remember (get_kind e n) as kind.
        destruct kind.
        * simpl. auto with arith.
        * apply get_kind_S in H0. exfalso. auto.
    - assert (H' := H). assert (H'' := H).
      apply IHt1 in H'.
      apply IHt2 in H''.
      simpl tsubst.
      remember (kind_of e (tarr t1 t2)).
      destruct o.
      inversion Heqo.
      remember (kind_of e t1) as k1. remember (kind_of e t2) as k2.
      destruct k1, k2; try discriminate; try eauto.
      + simpl.

      
  Fixpoint hereditary_substitution (t : term) (v : nat) (t' : term) (T : typ) :=
    match t with
      | var y =>
        match lt_eq_lt_dec y v with
          | inleft (left _)  => var y
          | inleft (right _) => t'
          | inright _        => var (y - 1)
        end
      | abs T1 t2  => abs T1 (hereditary_substitution t2 (S v) (shift 0 t') T)
      | abs_t T1 t2 => abs_t T1 (hereditary_substitution t2 v (shift_typ 0 t') T)
      | app t1 t2 =>
        let u1 := hereditary_substitution t1 v t' T in
        let u2 := hereditary_substitution t2 v t' T in
        match u1 with
          | (abs T' u1') => hereditary_substitution u1' 0 u2 T'
          | _ => app u1 u2
        end
      | app_t t T' =>
        let u := hereditary_substitution t v t' T in
        match u with
          | abs_t k u' => subst_typ u' 0 T'
          | _ => app_t u T'
        end
    end.

  *)
End part_2.