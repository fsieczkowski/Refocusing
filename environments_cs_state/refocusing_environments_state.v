Require Import Setoid.
Require Export refocusing_signatures_env_state.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.

Module Lang_Prop (R : RED_LANG) : LANG_PROP R.

  Import R.
  Open Scope red_scope.

  Lemma plug_empty : forall c, empty [ c ] = c.
  Proof. auto. Qed.
  Lemma compose_empty : forall c : context, c =  c · empty.
  Proof. apply app_nil_end. Qed.
  Lemma composeC_emptyC : forall Ec : contextC, Ec = Ec ·· emptyC.
  Proof. apply app_nil_end. Qed.
  Lemma plug_compose : forall (E E0 : context) (c : closure), 
    E · E0 [ c ] = E0 [ E [ c ] ].
  Proof. apply fold_left_app. Qed.
  Lemma composeC_compose : forall Ec Ec0,
    contextC_to_context (Ec ·· Ec0) = 
      contextC_to_context Ec · contextC_to_context Ec0.
  Proof. apply map_app. Qed.

  Close Scope red_scope.

End Lang_Prop.

Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.Lang.

  Import R.
  Import Lang.

  Module P := Lang_Prop Lang.
  Import P.
  Hint Resolve plug_empty.

  Open Scope red_scope.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  (** A decomposition function specified in terms of the atomic functions *)
  Inductive dec : closure -> context -> decomp -> Prop :=
  | dec_r : forall c E r
      (DCL : dec_closure c = in_red r),
      dec c E (d_red r E)
  | dec_v : forall c E v d
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v d),
      dec c E d
  | dec_c : forall c c0 E f d
      (DCL : dec_closure c = in_clo c0 f)
      (DEC : dec c0 (f :: E) d),
      dec c E d
  with decctx :  context -> value -> decomp -> Prop :=
  | dc_n : forall v,
      decctx empty v (d_val v)
  | dc_r : forall v f E r
      (DCT : dec_context f v = in_red r),
      decctx (f :: E) v (d_red r E)
  | dc_v : forall v v0 f E d
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 d),
      decctx (f :: E) v d
  | dc_c  : forall v f f0 E c d
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) d),
      decctx (f :: E) v d.

(*  Inductive dec : closure -> context -> decomp -> Prop :=
  | d_r    : forall (c : closure) (E : context) (r : redex)
               (DCL  : dec_closure c = in_red r),
               dec c E (d_red r E)
  | d_v    : forall (c : closure) (E : context) (v : value) (d : decomp)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v d),
               dec c E d
  | d_clo : forall (c c0 : closure) (E : context) (f : frame) (d : decomp)
               (DCL   : dec_closure c = in_clo c0 f)
               (DEC_C : dec c0 (f :: E) d),
               dec c E d
  with decctx :  context -> value -> decomp -> Prop :=
  | dc_val  : forall (v : value), decctx empty v (d_val v)
  | dc_r    : forall (v : value) (f : frame) (E : context) (r : redex)
                (DCT  : dec_context f v = in_red r),
                decctx (f :: E) v (d_red r E)
  | dc_v    : forall (v v0 : value) (f : frame) (E : context) (d : decomp)
                (DCT   : dec_context f v = in_val v0)
                (DEC_E : decctx E v0 d),
                decctx (f :: E) v d
  | dc_clo  : forall (v : value) (f f0 : frame) (E : context) (c : closure) (d : decomp)
                (DCT   : dec_context f v = in_clo c f0)
                (DEC_C : dec c (f0 :: E) d),
                decctx (f :: E) v d.*)

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
  Hint Constructors dec decctx.

  Lemma cl_o_trans : forall c c0 c1, c <| c0 -> c0 <| c1 -> c <| c1.
  Proof with auto.
    induction 2;
    econstructor 2; eauto.
  Qed.

  Ltac isda := intros; simpl in *; try discriminate; auto.

  Lemma plug_le_eq : forall E c c0 
    (PLUG : E [ c0 ] = c),
    c0 <| c \/ (E = empty /\ c = c0).
  Proof with isda.
    induction E; intros...
    destruct (IHE _ _ PLUG) as [H0 | [H1 H0]]; clear IHE; left;
    [eapply cl_o_trans; eauto | subst]; repeat econstructor...
  Qed.

  Lemma cl_c : forall c c0
    (LE_C : c <| c0), 
    exists E, E [ c ] = c0.
  Proof with isda.
    intros; induction LE_C; inversion H; subst.
    exists (f :: nil)...
    destruct IHLE_C as [E PLUG]; exists (E ++ (f :: empty)); 
      unfold plug in *; rewrite fold_left_app; simpl; subst...
  Qed.

  Definition value_one_step (v v0 : value) : Prop := 
    subclosure_one_step (value_to_closure v) (value_to_closure v0).
  Definition value_order := clos_trans_n1 _ value_one_step.
    
  Notation " a <v| b " := (value_order a b) (at level 40) : red_scope.

  Lemma value_order_wf : well_founded value_order.
  Proof.
    apply wf_clos_trans_r; apply wf_inverse_image; apply subclosure_one_step_wf.
  Qed.

  Lemma dec_val : forall v E d
    (DEC : dec (value_to_closure v) E d),
    decctx E v d.
  Proof with isda.
    induction v using (well_founded_ind value_order_wf); intros.
    remember (R.dec_closure (value_to_closure v)) as int_dec;
      assert (DEC_C_OK := dec_closure_correct (value_to_closure v));
        destruct int_dec; rewrite <- Heqint_dec in DEC_C_OK.
    symmetry in DEC_C_OK; contradiction (value_redex _ _ DEC_C_OK).
    apply value_to_closure_injective in DEC_C_OK; inversion DEC; subst; 
      unfold dec_closure in DCL; rewrite DCL in Heqint_dec; 
        inversion Heqint_dec; subst...
    destruct (value_trivial v c (f :: nil)) as [EMP | [v0 V0_EQ]]; simpl...
    subst c; symmetry in DEC_C_OK; assert (V_ORD := scl _ _ _ DEC_C_OK);
      apply (tn1_step _ value_one_step) in V_ORD; change (v0 <v| v) in V_ORD.
    inversion DEC; subst; unfold dec_closure in DCL; rewrite DCL in Heqint_dec;
      inversion Heqint_dec; subst; clear DEC Heqint_dec DCL;
        apply (H _ V_ORD) in DEC0.
    generalize dependent v0; 
      induction f0 using (well_founded_ind frame_order_wf); intros.
    remember (R.dec_context f0 v0) as int_dec;
      assert (DEC_E_OK := R.dec_context_correct f0 v0); destruct int_dec;
        rewrite <- Heqint_dec in DEC_E_OK; rewrite <- DEC_C_OK in DEC_E_OK;
          symmetry in DEC_E_OK.
    contradiction (value_redex _ _ DEC_E_OK).
    clear H H0; apply value_to_closure_injective in DEC_E_OK; subst.
    inversion DEC0; subst; unfold dec_context in DCT;
      rewrite DCT in Heqint_dec; inversion Heqint_dec; subst...
    destruct (value_trivial v c (f :: nil)) as [EMP | [v1 V1_EQ]]; subst...
    inversion DEC0; subst; unfold dec_context in DCT;
      rewrite DCT in Heqint_dec; inversion Heqint_dec; subst; clear Heqint_dec.
    apply H0 with f2 v1...
    destruct (dec_context_clo_next _ _ _ _ DCT)...
    repeat econstructor; eauto.
    apply H...
    repeat econstructor; eauto.
  Qed.

  Lemma val_dec : forall v E d
    (DEC_E : decctx E v d),
    dec (value_to_closure v) E d.
  Proof with isda; eauto.
    induction v using (well_founded_ind value_order_wf); intros.
    remember (R.dec_closure (value_to_closure v)) as int_dec;
      assert (DEC_C_OK := dec_closure_correct (value_to_closure v));
        destruct int_dec; rewrite <- Heqint_dec in DEC_C_OK;
          symmetry in DEC_C_OK.
    contradiction (value_redex _ _ DEC_C_OK).
    apply value_to_closure_injective in DEC_C_OK; subst; econstructor...
    destruct (value_trivial v c (f :: nil)) as [EMP | [v0 V0_EQ]]; subst...
    econstructor 3...
    apply H; [ repeat econstructor | clear Heqint_dec]...
    generalize dependent v0;
      induction f using (well_founded_ind frame_order_wf); intros.
    remember (R.dec_context f v0) as int_dec;
      assert (DEC_E_OK := R.dec_context_correct f v0); destruct int_dec;
        rewrite <- Heqint_dec in DEC_E_OK; rewrite <- DEC_C_OK in DEC_E_OK;
          symmetry in DEC_E_OK.
    contradiction (value_redex _ _ DEC_E_OK).
    clear H H0; apply value_to_closure_injective in DEC_E_OK; subst;
      econstructor...
    destruct (value_trivial v c (f0 :: nil)) as [EMP | [v1 V1_EQ]]; subst...
    econstructor 4...
    apply H.
    repeat econstructor...
    apply H0...
    symmetry in Heqint_dec; destruct (dec_context_clo_next _ _ _ _ Heqint_dec)...
  Qed.

  Module RS : RED_SEM R.Lang with Definition dec := dec.
    Definition dec := dec.
    Hint Constructors clos_trans_n1 subclosure_one_step.
    Hint Unfold closure_order dec.

    Lemma decompose : forall c,
      (exists v, c = value_to_closure v) \/
      (exists r, exists E, c = E [ redex_to_closure r ]).
    Proof with eauto.
      induction c using (well_founded_ind closure_order_wf); intros.
      remember (R.dec_closure c) as int;
        assert (DEC_CL_OK := dec_closure_correct c);
          destruct int; rewrite <- Heqint in DEC_CL_OK...
      subst...
      destruct (H c0) as [[v Hv] | [r [E HrE]]]...
      subst c0; clear Heqint; generalize dependent v;
        induction f using (well_founded_ind frame_order_wf); intros.
      remember (R.dec_context f v) as int; 
        assert (DEC_CT_OK := R.dec_context_correct f v);
          destruct int; rewrite <- Heqint in DEC_CT_OK; 
            rewrite DEC_CL_OK in DEC_CT_OK...
      right; exists r; exists empty...
      destruct (H c0) as [[v0 Hv] | [r [E HrE]]]...
      symmetry in Heqint; 
        destruct (dec_context_clo_next _ _ _ _ Heqint) as [H1 _]; subst c0;
          destruct (H0 f0 H1 v0 DEC_CT_OK) as [[v1 Hv1] | [r [E HrE]]]...
      right; exists r; exists (E · (f0 :: nil)); subst c0;
        rewrite P.plug_compose...
      right; exists r; exists (E · (f :: nil)); subst c0;
        rewrite P.plug_compose...
    Qed.

    Lemma dec_redex_self_e : forall r,
      dec (redex_to_closure r) empty (d_red r empty).
    Proof with isda; eauto.
      intros; remember (R.dec_closure (redex_to_closure r)) as int; destruct int;
        assert (DEC_CL_OK := dec_closure_correct (redex_to_closure r));
          rewrite <- Heqint in DEC_CL_OK; simpl in *.
      apply redex_to_closure_injective in DEC_CL_OK; subst; constructor...
      contradict (value_redex _ _ DEC_CL_OK).
      symmetry in Heqint; assert (CL_T := dec_closure_clo_top _ _ _ Heqint);
        econstructor 3...
      destruct (redex_trivial r c (f :: empty) DEC_CL_OK) as [EMP | [v V_EQ]];
        subst...
      clear CL_T Heqint; generalize dependent v;
        induction f using (well_founded_ind frame_order_wf); intros.
      apply val_dec; remember (R.dec_context f v) as int;
        assert (D_CT_OK := R.dec_context_correct f v);
          rewrite <- Heqint in D_CT_OK; destruct int; simpl in D_CT_OK;
            rewrite DEC_CL_OK in D_CT_OK.
      apply redex_to_closure_injective in D_CT_OK; subst...
      contradiction (value_redex _ _ D_CT_OK).
      econstructor 4...
      destruct (redex_trivial r c (f0 :: empty) D_CT_OK) as [EMP | [v1 V1_EQ]];
        subst...
      symmetry in Heqint; destruct (dec_context_clo_next _ _ _ _ Heqint);
        apply H...
    Qed.

    Lemma dec_redex_self : forall r E, dec (redex_to_closure r) E (d_red r E).
    Proof with isda; eauto.
      intros; assert (RSE := dec_redex_self_e r).
      induction RSE using dec_Ind with
      (P := fun c E0 d (DEC_C : dec c E0 d) => match d with
        | d_val v => True
        | d_red r0 E1 => dec c (E0 · E) (d_red r0 (E1 · E))
      end)
      (P0:= fun E0 v d (DEC_E : decctx E0 v d) => match d with
        | d_val v => True
        | d_red r0 E1 => decctx (E0 · E) v (d_red r0 (E1 · E))
      end); try destruct d...
    Qed.

    Lemma dec_correct : forall c E d, dec c E d -> decomp_to_closure d = E [ c ].
    Proof.
      induction 1 using dec_Ind with
        (P := fun c E d (DEC_C : dec c E d) => decomp_to_closure d = E [ c ])
        (P0:= fun E v d (DEC_E : decctx E v d) => 
          decomp_to_closure d = E [ value_to_closure v ]); 
        simpl; auto; 
          match goal with
            | [ DT: (dec_closure ?t = ?int) |- _ ] => unfold dec_closure in DT;
                assert (hh := R.dec_closure_correct t); rewrite DT in hh
            | [ DC: (dec_context ?ec ?v = ?int) |- _ ] =>
                unfold dec_context in DC;
                  assert (hh := R.dec_context_correct ec v); rewrite DC in hh
          end; try rewrite IHdec; rewrite <- hh; subst; auto.
    Qed.

    Lemma dec_plug_rev : forall E E0 c d
      (DEC : dec c (E · E0) d),
      dec (E [ c ]) E0 d.
    Proof with isda.
      induction E...
      apply IHE; clear IHE; remember (R.dec_closure (atom_plug c a)) as int;
        destruct int; assert (D_CL := dec_closure_correct (atom_plug c a));
          rewrite <- Heqint in D_CL; symmetry in Heqint.
      discriminate (dec_closure_red_empty _ _ Heqint c (a :: nil))...
      discriminate (dec_closure_val_empty _ _ Heqint c (a :: nil))...
      destruct (dec_frame_ord c0 c f a D_CL) as [LT | [GT | [EC EF]]];
        try (subst; eauto; fail).
      contradict (dec_closure_clo_top _ _ _ Heqint _ LT).
      symmetry in D_CL; destruct (frame_det _ _ _ _ GT D_CL) as [v V_EQ];
        subst.
      econstructor 3; eauto; clear Heqint; generalize dependent v;
        induction f using (well_founded_ind frame_order_wf); intros.
      apply val_dec; remember (R.dec_context f v) as int; destruct int; 
        symmetry in Heqint; assert (D_CT := dec_context_correct f v);
          rewrite Heqint in D_CT.
      contradiction (dec_context_red_bot _ _ _ Heqint a).
      contradiction (dec_context_val_bot _ _ _ Heqint a).
      destruct (dec_context_clo_next _ _ _ _ Heqint) as [LT NLT].
      econstructor 4; eauto; rewrite <- D_CL in D_CT.
      destruct (dec_frame_ord _ _ _ _ D_CT) as [LT0 | [GT0 | [EC EF]]];
        try (subst; auto; fail).
      contradiction (NLT a GT).
      symmetry in D_CT; clear NLT;
        destruct (frame_det _ _ _ _ GT0 D_CT) as [v0 V0_EQ]; subst...
    Qed.

    Lemma dec_plug : forall E E0 c d
      (DEC : dec (E [ c ]) E0 d),
      dec c (E · E0) d.
    Proof with isda.
      induction E...
      apply IHE in DEC; clear IHE; inversion DEC; subst; 
        unfold dec_closure in DCL; clear DEC;
          assert (D_CL := dec_closure_correct (atom_plug c a)); 
            rewrite DCL in D_CL.
      discriminate (dec_closure_red_empty _ _ DCL c (a :: nil))...
      discriminate (dec_closure_val_empty _ _ DCL c (a :: empty))...
      destruct (dec_frame_ord c1 c f a D_CL) as [LT | [GT | [EC EF]]]; subst...
      contradiction (dec_closure_clo_top _ _ _ DCL a).
      symmetry in D_CL; destruct (frame_det _ _ _ _ GT D_CL) as [v V_EQ]; 
        subst; clear DCL; generalize dependent v;
          induction f using (well_founded_ind frame_order_wf); intros.
      assert (DV := dec_val _ _ _ DEC0); inversion DV; subst; clear DEC0;
        assert (D_CT := dec_context_correct f v); unfold dec_context in DCT;
          rewrite DCT in D_CT; simpl in D_CT.
      contradiction (dec_context_red_bot _ _ _ DCT a).
      contradiction (dec_context_val_bot _ _ _ DCT a).
      clear DV; rewrite <- D_CL in D_CT.
      destruct (dec_context_clo_next _ _ _ _ DCT) as [LT NLT].
      destruct (dec_frame_ord _ _ _ _ D_CT) as [LT0 | [GT0 | [VE FE]]]; subst...
      contradiction (NLT a).
      symmetry in D_CT; destruct (frame_det _ _ _ _ GT0 D_CT) as [v1 V1_EQ];
        subst; eauto.
    Qed.

    Inductive decempty : closure -> decomp -> Prop :=
    | d_intro : forall c d
        (DEC : dec c empty d),
        decempty c d.

    Inductive iter : decomp -> state -> answer -> Prop :=
    | i_val : forall v G,
        iter (d_val v) G (v, G)
    | i_red : forall r c E E0 G G0 d a
        (CTR : contract r E G = Some (c, E0, G0))
        (DEC : decempty (E0 [c]) d)
        (ITR : iter d G0 a),
        iter (d_red r E) G a.

    Inductive eval : term -> answer -> Prop :=
    | e_intro : forall t d a
        (DEC : decempty (pair t nil) d)
        (ITR : iter d init a),
        eval t a.

    Module P := P.

  End RS.

  Definition dec_closure_correct := R.dec_closure_correct.
  Definition dec_context_correct := R.dec_context_correct.

  Lemma dec_val_self : forall v E d,
    dec (value_to_closure v) E d <-> decctx E v d.
  Proof.
    split; auto using dec_val, val_dec.
  Qed.
  Definition eqP := eqP.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

End RedRefSem.

Module Red_Prop (R : RED_LANG) (RS : RED_REF_SEM(R)) : RED_PROP R RS.

  Module P := Lang_Prop R.
  Import RS.RS.
  Import RS.
  Import R.
  Import P.
  Open Scope red_scope.

  Lemma dec_is_function : forall c d d0,
    decempty c d -> decempty c d0 -> d = d0.
  Proof.
    intros c d d0 DE DE0; inversion_clear DE; inversion_clear DE0.
    refine (dec_Ind 
      (fun c E d (H : dec c E d) => forall d0 (DEC : dec c E d0), d = d0)
      (fun E v d (H : decctx E v d) => forall d0 (DEC : decctx E v d0), d = d0)
      _ _ _ _ _ _ _ c empty d DEC d0 DEC0); intros; simpl; auto; try apply H;
    match goal with
      | [ RD : (dec ?c ?E ?d), DCL : (dec_closure ?c = ?int) |- _ ] => 
          inversion RD; rewrite DCL0 in DCL; inversion DCL
      | [ RC : (decctx (?f :: ?E) ?v ?d), DCT : (dec_context ?f ?v = ?int)
          |- _ ] => inversion RC; rewrite DCT0 in DCT; inversion DCT
      | [ RC : (decctx empty ?v ?d) |- _] => inversion RC
    end; subst; auto.
  Qed.
  Hint Resolve dec_is_function : prop.

  Lemma iter_is_function : forall d G a a0,
    iter d G a -> iter d G a0 -> a = a0.
  Proof with eauto with prop.
    induction 1; intros ITR; inversion ITR; subst...
    rewrite CTR0 in CTR; inversion CTR; subst; apply IHiter;
      cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.

  Lemma eval_is_function : forall t a a0,
    eval t a -> eval t a0 -> a = a0.
  Proof with eauto with prop.
    induction 1; intros; inversion H; subst; cutrewrite (d = d0) in ITR...
  Qed.

  Lemma dec_correct : forall c E d,
    dec c E d -> decomp_to_closure d = E [c].
  Proof.
    induction 1 using RS.dec_Ind with
    (P := fun c E d (H : dec c E d) => decomp_to_closure d = E [c])
    (P0:= fun E v d (H : decctx E v d) =>
      decomp_to_closure d = E [value_to_closure v]); simpl; auto;
    match goal with
      | [ DCL : dec_closure ?cl = ?int |- _ ] => 
          assert (D_CL := dec_closure_correct cl); rewrite DCL in D_CL;
            simpl in D_CL; rewrite <- D_CL
      | [ DCT : dec_context ?f ?v = ?int |- _ ] => 
        assert (D_CT := dec_context_correct f v); rewrite DCT in D_CT;
          simpl in D_CT; rewrite <- D_CT
    end; auto.
  Qed.

  Lemma dec_total : forall c, exists d, decempty c d.
  Proof.
    intro c; destruct (decompose c) as [[v Hv] | [r [E Hp]]]; intros; subst c.
    exists (d_val v); constructor; rewrite dec_val_self; constructor.
    exists (d_red r E); constructor; apply dec_plug_rev;
    rewrite <- P.compose_empty; apply dec_redex_self.
  Qed.

  Lemma unique_decomposition : forall c, 
    (exists v, c = value_to_closure v) \/ 
    (exists r, exists E, c = E [redex_to_closure r] /\
      forall r0 E0, c = E0 [redex_to_closure r0] -> r=r0 /\ E = E0).
  Proof with auto using dec_redex_self.
    intro c; destruct (decompose c) as [[v H] | [r [E H]]]; intros;
      [left; exists v | right; exists r; exists E; split]; auto; intros.
    assert (DE_RE : decempty c (d_red r E)).
    constructor; rewrite H; apply dec_plug_rev; rewrite <- P.compose_empty...
    assert (DE_R0E0 : decempty c (d_red r0 E0)).
    constructor; rewrite H0; apply dec_plug_rev; rewrite <- P.compose_empty...
    assert (hh := dec_is_function _ _ _ DE_RE DE_R0E0); injection hh...
  Qed.

End Red_Prop.

Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM (R)) <: 
  PRE_ABSTRACT_MACHINE (R).

  Module LP := Lang_Prop R.
  Import R.
  Import RS.RS.
  Import RS.

  (** Functions specifying atomic steps of induction on terms and contexts
      -- needed to avoid explicit induction on terms and contexts in 
      construction of the AM *)
  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  (** A decomposition function specified in terms of the atomic functions *)
  Inductive dec : closure -> context -> decomp -> Prop :=
  | dec_r : forall c E r
      (DCL : dec_closure c = in_red r),
      dec c E (d_red r E)
  | dec_v : forall c E v d
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v d),
      dec c E d
  | dec_c : forall c c0 E f d
      (DCL : dec_closure c = in_clo c0 f)
      (DEC : dec c0 (f :: E) d),
      dec c E d
  with decctx :  context -> value -> decomp -> Prop :=
  | dc_n : forall v,
      decctx empty v (d_val v)
  | dc_r : forall v f E r
      (DCT : dec_context f v = in_red r),
      decctx (f :: E) v (d_red r E)
  | dc_v : forall v v0 f E d
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 d),
      decctx (f :: E) v d
  | dc_c  : forall v f f0 E c d
      (DCT : dec_context f v = R.in_clo c f0)
      (DEC : dec c (f0 :: E) d),
      decctx (f :: E) v d.    

  Inductive iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G,
      iter (d_val v) G (v, G)
  | i_red : forall r E E0 c d G G0 a
      (CTR : contract r E G = Some (c, E0, G0))
      (DEC : dec c E0 d)
      (ITR : iter d G0 a),
      iter (d_red r E) G a.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t d a
      (DEC : dec (pair t nil) empty d)
      (ITR : iter d init a),
      eval t a.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Hint Constructors dec decctx iter eval 
    RS.dec RS.decctx RS.iter RS.eval decempty.
  Hint Unfold RS.RS.dec.

  Lemma dec_id_l : forall c E d, RS.RS.dec c E d -> dec c E d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
      (P := fun c E d (H : RS.RS.dec c E d) => dec c E d)
      (P0:= fun E v d (H0 : RS.decctx E v d) => decctx E v d)...
  Qed.
    
  Lemma decctx_id_l : forall E v d, RS.decctx E v d -> decctx E v d.
  Proof with eauto.
    induction 1 using RS.decctx_Ind with
      (P := fun c E d (H : RS.RS.dec c E d) => dec c E d)
      (P0:= fun E v d (H0 : RS.decctx E v d) => decctx E v d)...
  Qed.
  Hint Resolve dec_id_l.

  Lemma dec_id_r : forall c E d, dec c E d -> RS.RS.dec c E d.
  Proof with eauto.
    induction 1 using dec_Ind with 
      (P := fun c E d (H : dec c E d) => RS.RS.dec c E d)
      (P0:= fun E v d (H0 : decctx E v d) => RS.decctx E v d)...
  Qed.
  Hint Resolve dec_id_r.

  Lemma decctx_id_r : forall c E d, decctx c E d -> RS.decctx c E d.
  Proof with eauto.
    induction 1 using decctx_Ind with 
      (P := fun c E d (H : dec c E d) => RS.RS.dec c E d)
      (P0:= fun E v d (H0 : decctx E v d) => RS.decctx E v d)...
  Qed.

  Lemma iterRedPam : forall d G a, RS.RS.iter d G a -> iter d G a.
  Proof with eauto.
    induction 1; auto; econstructor 2; inversion_clear DEC; eauto;
      rewrite LP.compose_empty with (c := E0); auto using dec_plug.
  Qed.

  Lemma evalRedPam : forall t a
    (EV : RS.RS.eval t a),
    eval t a.
  Proof with auto using iterRedPam.
    intros; inversion_clear EV; constructor 1 with d; try inversion_clear DEC...
  Qed.
  Hint Resolve evalRedPam.

  Lemma iterPamRed : forall d G a
    (ITR : iter d G a),
    RS.RS.iter d G a.
  Proof with auto.
    induction 1; auto; econstructor 2; eauto; constructor;
      apply dec_plug_rev; rewrite <- LP.compose_empty...
  Qed.

  Lemma evalPamRed : forall t a
    (EV : eval t a),
    RS.RS.eval t a.
  Proof.
    intros t v H; inversion_clear H; eauto using iterPamRed.
  Qed.
  Hint Resolve evalPamRed.

  Theorem evalPam : forall t v, RS.RS.eval t v <-> eval t v.
  Proof with auto.
    split...
  Qed.

  Lemma dec_val : forall v E d, 
    dec (value_to_closure v) E d <-> decctx E v d.
  Proof.
    split; intros.
    apply decctx_id_l; rewrite <- dec_val_self; apply dec_id_r; auto.
    apply dec_id_l; rewrite dec_val_self; apply decctx_id_r; auto.
  Qed.

End PreAbstractMachine.

Module StagedAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: 
  STAGED_ABSTRACT_MACHINE R.

  Module PAM := PreAbstractMachine R RS.
  Module LP := Lang_Prop R.
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_closure := RS.dec_closure.
  Definition dec_context := RS.dec_context.

  Definition dec_closure_correct := RS.dec_closure_correct.
  Definition dec_context_correct := RS.dec_context_correct.

  Inductive dec : closure -> context -> state -> answer -> Prop :=
  | dec_r : forall c r E G a
      (DCL : dec_closure c = in_red r)
      (ITR : iter (d_red r E) G a),
      dec c E G a
  | dec_v : forall c E v G a
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v G a),
      dec c E G a
  | dec_c : forall c c0 f E G a
      (DCL : dec_closure c = in_clo c0 f)
      (DEC : dec c0 (f :: E) G a),
      dec c E G a
  with decctx : context -> value -> state -> answer -> Prop :=
  | dc_n : forall v G a
      (ITR  : iter (d_val v) G a),
      decctx empty v G a
  | dc_r : forall v f E G a r
      (DCT : dec_context f v = in_red r)
      (ITR : iter (d_red r E) G a),
      decctx (f :: E) v G a
  | dc_v : forall v v0 f E G a
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 G a),
      decctx (f :: E) v G a
  | dc_c : forall v c f f0 E G a
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) G a),
      decctx (f :: E) v G a
  with iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G,
      iter (d_val v) G (v, G)
  | i_red : forall r E E0 c G G0 a
      (CTR : contract r E G = Some (c, E0, G0))
      (DEC : dec c E0 G0 a),
      iter (d_red r E) G a.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind   := Induction for iter Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a
      (DEC : dec (pair t nil) empty init a),
      eval t a.

  Hint Constructors dec decctx iter eval.

  Lemma decPamSam : forall c E d G a
    (DEC : PAM.dec c E d)
    (ITR : iter d G a),
    dec c E G a.
  Proof with eauto.
    intros c E d G a DEC; revert G a; induction DEC using PAM.dec_Ind with
      (P := fun t E d (DEC : PAM.dec t E d) => 
        forall G a (ITR : iter d G a), dec t E G a)
      (P0 := fun E v d (DEC : PAM.decctx E v d) =>
        forall G a (ITR : iter d G a), decctx E v G a)...
  Qed.
  Hint Resolve decPamSam.

  Lemma decctxPamSam : forall E v d G a
    (DEC : PAM.decctx E v d)
    (ITR : iter d G a),
    decctx E v G a.
  Proof with eauto.
    induction 1; intros...
  Qed.

  Lemma iterPamSam : forall d G a
    (ITER : PAM.iter d G a),
    iter d G a.
  Proof.
    induction 1; eauto.
  Qed.
  Hint Resolve iterPamSam.

  Lemma evalPamSam : forall t a
    (EV : PAM.eval t a),
    eval t a.
  Proof with eauto.
    intros; inversion_clear EV...
  Qed.
  Hint Resolve evalPamSam.

  Module P := Red_Prop R RS.

  Lemma decSamPam : forall c E G a d 
    (DEC : dec c E G a)
    (PDEC : PAM.dec c E d),
    PAM.iter d G a.
  Proof with auto.
    intros c E G a d DEC; revert d; induction DEC using dec_Ind with
      (P  := fun t E G a (DEC : dec t E G a) => 
        forall d (PDEC : PAM.dec t E d), PAM.iter d G a)
      (P0 := fun v E G a (DEC_E : decctx v E G a) =>
        forall d (PDEC : PAM.decctx v E d), PAM.iter d G a)
      (P1 := fun d G a (ITR : iter d G a) => PAM.iter d G a); 
      intros; simpl; auto;
        try (try apply IHDEC; inversion PDEC; cbv delta in *; 
          match goal with
            | [ D0 : RS.dec_closure ?cl = ?int, 
                D1 : RS.dec_closure ?cl = ?int0 |- _ ] => 
                  rewrite D0 in D1; inversion D1
            | [ D0 : RS.dec_context ?f ?v = ?int,
                D1 : RS.dec_context ?f ?v = ?int0 |- _ ] => 
                  rewrite D0 in D1; inversion D1
            | [ |- _ ] => idtac
          end; subst)...
    destruct(P.dec_total (plug c E0)) as [d H0]; inversion_clear H0.
    apply RS.RS.dec_plug in DEC0; rewrite <- LP.compose_empty in DEC0; eauto.
  Qed.
  Hint Resolve decSamPam.

  Lemma decctxSamPam : forall E v G a d 
    (DEC : decctx E v G a)
    (PDEC : PAM.decctx E v d),
    PAM.iter d G a.
  Proof with eauto.
    induction 1; intros; inversion_clear PDEC; unfold dec_context in *; 
      unfold PAM.dec_context in *; 
        try (rewrite DCT0 in DCT; inversion DCT; subst)...
    inversion_clear ITR...
    inversion_clear ITR; destruct (P.dec_total (plug c E1)) as [dd H0]; 
      inversion_clear H0; apply RS.RS.dec_plug in DEC0; 
        rewrite <- LP.compose_empty in DEC0...
  Qed.

  Lemma evalSamPam : forall t v
    (EV : eval t v),
    PAM.eval t v.
  Proof with eauto.
    intros t v EV; inversion_clear EV;
      destruct (P.dec_total (pair t nil)) as [d H]; inversion_clear H...
  Qed.
  Hint Resolve evalSamPam.

  Theorem evalSam : forall t a,
    RS.RS.eval t a <-> eval t a.
  Proof with auto.
    intros t v; rewrite PAM.evalPam; split; intros...
  Qed.

  Lemma dec_val : forall E v G a, 
    dec (value_to_closure v) E G a <-> decctx E v G a.
  Proof.
    intros; destruct (P.dec_total (plug (value_to_closure v) E)) as [d H0];
      inversion_clear H0; apply RS.RS.dec_plug in DEC; 
        rewrite <- LP.compose_empty in DEC.
    split; intro.
    apply decctxPamSam with d; eauto; rewrite <- PAM.dec_val; eauto.
    apply decPamSam with d; eauto; apply PAM.dec_id_l in DEC;
      rewrite PAM.dec_val in DEC; eauto using decctxSamPam.
  Qed.

End StagedAbstractMachine.

Module EvalApplyMachine (R : RED_LANG) (RS : RED_REF_SEM R) <:
  EVAL_APPLY_MACHINE R.

  Module SAM := StagedAbstractMachine R RS.
  Import R.
  Import RS.RS.
  Import RS.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  Inductive dec : closure -> context -> state -> answer -> Prop :=
  | dec_r : forall c c0 E E0 r G G0 a
      (DCL : dec_closure c = in_red r)
      (CTR : contract r E G = Some (c0, E0, G0))
      (DEC : dec c0 E0 G0 a),
      dec c E G a
  | dec_v : forall c E v G a
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v G a),
      dec c E G a
  | dec_c : forall c c0 f E G a
      (DCL : dec_closure c = in_clo c0 f) 
      (DEC : dec c0 (f :: E) G a),
      dec c E G a
  with decctx : context -> value -> state -> answer -> Prop :=
  | dc_n : forall v G,
      decctx empty v G (v, G)
  | dc_r : forall v f E E0 G G0 r c a
      (DCT : dec_context f v = in_red r)
      (CTR : contract r E G = Some (c, E0, G0))
      (DEC : dec c E0 G0 a),
      decctx (f :: E) v G a
  | dc_v : forall v v0 f E G a
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 G a),
      decctx (f :: E) v G a
  | dc_c : forall v f f0 E c G a
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) G a),
      decctx (f :: E) v G a.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a
      (DEC : dec (pair t nil) empty init a),
      eval t a.

  Hint Constructors dec decctx eval.

  Lemma decSamEam : forall c E G a
    (DEC : SAM.dec c E G a),
    dec c E G a.
  Proof with eauto.
    induction 1 using SAM.dec_Ind with
      (P := fun c E G a (H:SAM.dec c E G a) => dec c E G a)
      (P0:= fun E v G a (H:SAM.decctx E v G a) => decctx E v G a)
      (P1:= fun d G a (H:SAM.iter d G a) => 
        match d with
          | R.d_val v' => a = (v', G)
          | R.d_red r E => forall c E0 G0
              (CTR : contract r E G = Some (c, E0, G0)),
              dec c E0 G0 a
        end);
      simpl; intros; try inversion ITR; try subst; eauto; congruence.
  Qed.

  Lemma decctxSamEam : forall E v G a
    (DEC : SAM.decctx E v G a),
    decctx E v G a.
  Proof with eauto using decSamEam.
    induction 1; try inversion_clear ITR...
  Qed.

  Lemma evalSamEam : forall t a
    (EV : SAM.eval t a),
    eval t a.
  Proof.
    intros; inversion_clear EV; auto using decSamEam.
  Qed.
  Hint Resolve evalSamEam.

  Lemma decEamSam : forall c E G a
    (DEC : dec c E G a),
    SAM.dec c E G a.
  Proof with eauto.
    induction 1 using dec_Ind with
      (P := fun t E G a (H:dec t E G a) => SAM.dec t E G a)
      (P0:= fun v E G a (H:decctx v E G a) => SAM.decctx v E G a);
      intros; simpl...
  Qed.

  Lemma decctxEamSam : forall E v G a
    (DEC : decctx E v G a),
    SAM.decctx E v G a.
  Proof.
    induction 1; try inversion_clear ITR; eauto using decEamSam.
  Qed.
  
  Lemma evalEamSam : forall t a
    (EV : eval t a),
    SAM.eval t a.
  Proof.
    intros; inversion_clear EV; auto using decEamSam.
  Qed.
  Hint Resolve evalEamSam.

  Theorem evalEam : forall t a,
    RS.RS.eval t a <-> eval t a.
  Proof with auto.
    intros t v; rewrite SAM.evalSam; split...
  Qed.

  Lemma dec_val : forall E v G a, 
    dec (value_to_closure v) E G a <-> decctx E v G a.
  Proof.
    split; intro.
    apply decctxSamEam; rewrite <- SAM.dec_val; apply decEamSam; auto.
    apply decSamEam; rewrite SAM.dec_val; apply decctxEamSam; auto.
  Qed.

End EvalApplyMachine.

Module EAMachineC (Lang : RED_LANG) (RS : RED_REF_SEM Lang) <:
  EVAL_APPLY_MACHINE_C Lang.

  Module EAM := EvalApplyMachine Lang RS.
  Import Lang.
  Import RS.RS.
  Import RS.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  Definition eqP := eqP.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive dec : closureC -> contextC -> stateC -> answerC -> Prop :=
  | dec_r : forall c c0 E E0 EE G G0 GG cc r a
      (DCL : dec_closure (closureC_to_closure c) = in_red r)
      (CTR : contract r (contextC_to_context E) (stateC_to_state G)
        = Some (cc, EE, GG))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (c0, E0, G0))
      (DEC : dec c0 E0 G0 a),
      dec c E G a
  | dec_v : forall c E vv v G a
      (DCL : dec_closure (closureC_to_closure c) = in_val vv)
      (TOC : proj1_sig (closure_val _ _ DCL) = v)
      (DEC : decctx E v G a),
      dec c E G a
  with decctx : contextC -> valueC -> stateC -> answerC -> Prop :=
  | dc_n : forall v G,
      decctx emptyC v G (v, G)
  | dc_r : forall v f E E0 G G0 c0 c EE GG r a
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context E) (stateC_to_state G)
        = Some (c, EE, GG))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (c0, E0, G0))
      (DEC : dec c0 E0 G0 a),
      decctx (f :: E) v G a
  | dc_v : forall v v0 vv f E G a
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_val vv)
      (TOC : proj1_sig (context_val _ _ _ DCT) = v0)
      (DEC : decctx E v0 G a),
      decctx (f :: E) v G a
  | dc_c : forall v f f0 ff E G c cC a
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_clo c ff)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, f0))
      (DEC : dec cC (f0 :: E) G a),
      decctx (f :: E) v G a.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answerC -> Prop :=
  | e_intro : forall t a
      (DEC : dec (pairC t nil) emptyC initC a),
      eval t a.

  Hint Constructors dec decctx eval.

  Lemma decEamEamc : forall cC EC GC aC
    (DEC : EAM.dec (closureC_to_closure cC) (contextC_to_context EC)
      (stateC_to_state GC) (answerC_to_answer aC)),
    dec cC EC GC aC.
  Proof with eauto.
    intros; refine (EAM.dec_Ind
      (fun c E G a (DEC : EAM.dec c E G a) => forall cC EC GC aC
        (EQC : c = closureC_to_closure cC)
        (EQE : E = contextC_to_context EC)
        (EQS : G = stateC_to_state GC)
        (EQV : a = answerC_to_answer aC),
        dec cC EC GC aC)
      (fun E v G a (DEC : EAM.decctx E v G a) => forall EC vC GC aC
        (EQE : E = contextC_to_context EC)
        (EQV : v = valueC_to_value vC)
        (EQS : G = stateC_to_state GC)
        (EQA : a = answerC_to_answer aC),
        decctx EC vC GC aC)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    intros; simpl in *; subst...
    (* DCL -> RED *)
    remember (closure_red _ _ _ _ _ _ _ DCL CTR) as clr;
      destruct clr as [[[cC1 EC1] GC1] [EQC [EQE EQG]]];
        eapply dec_r with _ _ _ _ _ _ _ DCL CTR; eauto; rewrite <- Heqclr; simpl...
    (* DCL -> VAL *)
    remember (closure_val _ _ DCL) as clv; destruct clv as [vC1 EQV];
      eapply dec_v with _ _ DCL; try (rewrite <- Heqclv; simpl)...
    (* DCL -> CLO *)
    assert (hh := closureC_only_empty (cC0) c0 (f :: empty)); 
      unfold only_empty in hh.
    assert (ht := dec_closure_correct (closureC_to_closure (cC0))); 
      unfold EAM.dec_closure in DCL; rewrite DCL in ht; simpl in *; 
        apply hh in ht; discriminate.
    (* EMP *)
    destruct aC0 as [vC0 GC1]; inversion EQA as [[EQV EQG]];
    apply valueC_to_value_injective in EQV; destruct EC0; inversion EQE; 
      apply stateC_to_state_injective in EQG; subst...
    (* DCT -> RED *)
    destruct EC0; inversion EQE; subst; clear EQE.
    remember (context_red _ _ _ _ _ _ _ _ DCT CTR) as ctr;
      destruct ctr as [[[cC1 EC1] GC1] [EQC [EQE EQG]]];
        eapply dc_r with _ _ _ _ _ _ _ DCT CTR; eauto; rewrite <- Heqctr; simpl...
    (* DCT -> VAL *)
    destruct EC0; inversion EQE; subst; clear EQE.
    remember (context_val _ _ _ DCT) as ctv; destruct ctv as [vC2 EQV];
      eapply dc_v with _ _ DCT; eauto.
    rewrite <- Heqctv; simpl...
    (* DCT -> CLO *)
    destruct EC0; inversion EQE; subst; clear EQE.
    remember (context_clo _ _ _ _ DCT) as ctc; 
      destruct ctc as [[cC1 fC1] [EQC EQF]]; eapply dc_c with _ _ _ _ DCT; eauto;
        try rewrite <- Heqctc; simpl...
    apply H; auto; simpl; f_equal...
  Qed.

  Lemma decctxEamEamc : forall EC vC GC aC
    (DEC : EAM.decctx (contextC_to_context EC) (valueC_to_value vC)
      (stateC_to_state GC) (answerC_to_answer aC)),
    decctx EC vC GC aC.
  Proof with eauto using decEamEamc.
    intros; remember (answerC_to_answer aC) as a; generalize dependent aC;
      remember (stateC_to_state GC) as G; generalize dependent GC;
        remember (valueC_to_value vC) as v; generalize dependent vC; 
          remember (contextC_to_context EC) as E; generalize dependent EC;
            induction DEC; intros; destruct EC; inversion HeqE;
              subst; clear HeqE.
    destruct aC as [vC0 GC0]; inversion Heqa as [[EQV EQG]]; clear Heqa;
      apply valueC_to_value_injective in EQV;
        apply stateC_to_state_injective in EQG; subst...
    remember (context_red _ _ _ _ _ _ _ _ DCT CTR) as ctr; 
      destruct ctr as [[[cC0 EC0] GC0] [EQC [EQE EQG]]];
        eapply dc_r with _ _ _ _ _ _ _ DCT CTR; try rewrite <- Heqctr;
          simpl; clear Heqctr; subst...
    remember (context_val _ _ _ DCT) as ctv; destruct ctv as [vC1 EQV];
      eapply dc_v with _ _ DCT...
    rewrite <- Heqctv; simpl...
    remember (context_clo _ _ _ _ DCT) as ctc; 
      destruct ctc as [[cC1 fC1] [EQC EQF]]; eapply dc_c with _ _ _ _ DCT; auto;
        try rewrite <- Heqctc; simpl; clear Heqctc; subst...
  Qed.

  Lemma evalEamEamc : forall t a
    (EV : EAM.eval t (answerC_to_answer a)),
    eval t a.
  Proof.
    intros; inversion_clear EV;
      cutrewrite (pair t nil = closureC_to_closure (pairC t nil)) in DEC.
    constructor; apply decEamEamc; rewrite initC_init; auto.
    rewrite pairC_pair; auto.
  Qed.

  Lemma decEamcEam : forall cC EC GC aC
    (DEC : dec cC EC GC aC),
    EAM.dec (closureC_to_closure cC) (contextC_to_context EC)
      (stateC_to_state GC) (answerC_to_answer aC).
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun cC EC GC aC (DEC : dec cC EC GC aC) =>
      EAM.dec (closureC_to_closure cC) (contextC_to_context EC)
        (stateC_to_state GC) (answerC_to_answer aC))
    (P0:= fun EC vC GC aC (DEC : decctx EC vC GC aC) =>
      EAM.decctx (contextC_to_context EC) (valueC_to_value vC)
        (stateC_to_state GC) (answerC_to_answer aC)); simpl...
    (* Case 1 *)
    remember (closure_red _ _ _ _ _ _ _ DCL CTR) as CL_R;
      destruct CL_R as [[[cC0 EC0] GC0] [EQC [EQE EQG]]]; simpl in *;
        inversion TOC; clear TOC HeqCL_R; subst; econstructor...
    (* Case 2 *)
    remember (closure_val _ _ DCL) as CL_V; destruct CL_V as [vC0 UF];
      clear HeqCL_V; simpl in *; subst...
    (* Case 3 *)
    remember (context_red _ _ _ _ _ _ _ _ DCT CTR) as CT_R; 
      destruct CT_R as [[[cC0 EC0] GC0] [EQC [EQE EQG]]]; inversion TOC; 
        clear HeqCT_R TOC; subst; econstructor...
    (* Case 4 *)
    remember (context_val _ _ _ DCT) as CT_V; destruct CT_V as [vC2 UF];
      clear HeqCT_V; simpl in *; subst...
    (* Case 5 *)
    remember (context_clo _ _ c _ DCT) as CT_C;
      destruct CT_C as [[cC0 fC1] [UF0 UF1]]; inversion TOC; 
        clear TOC HeqCT_C; subst; econstructor 4...
  Qed.

  Lemma decctxEamcEam : forall EC vC GC aC
    (DEC : decctx EC vC GC aC),
    EAM.decctx (contextC_to_context EC) (valueC_to_value vC)
      (stateC_to_state GC) (answerC_to_answer aC).
  Proof with eauto using decEamcEam.
    induction 1; simpl...
    remember (context_red _ _ _ _ _ _ _ _ DCT CTR) as CT_R; 
      destruct CT_R as [[[cC0 EC0] GC0] [EQC [EQE EQG]]]; inversion TOC; 
        clear HeqCT_R TOC; subst; econstructor...
    remember (context_val _ _ _ DCT) as CT_V; destruct CT_V as [vC2 UF];
      clear HeqCT_V; simpl in *; subst...
    remember (context_clo _ _ c _ DCT) as CT_C;
      destruct CT_C as [[cC0 fC1] [UF0 UF1]]; inversion TOC; 
        clear TOC HeqCT_C; subst; econstructor 4...
    change (EAM.dec (closureC_to_closure cC) (contextC_to_context (f0 :: E))
      (stateC_to_state G) (answerC_to_answer a))...
  Qed.

  Lemma evalEamcEam : forall t a
    (EV : eval t a),
    EAM.eval t (answerC_to_answer a).
  Proof.
    intros; inversion_clear EV; constructor; 
      cutrewrite (pair t nil = closureC_to_closure (pairC t nil));
        try cutrewrite (empty = contextC_to_context emptyC);
          try rewrite <- initC_init; auto using decEamcEam.
    rewrite pairC_pair; auto.
  Qed.

  Theorem evalUeam : forall t a,
    RS.RS.eval t (answerC_to_answer a) <-> eval t a.
  Proof with auto.
    intros; rewrite EAM.evalEam; split; eauto using evalEamEamc, evalEamcEam.
  Qed.

  Lemma dec_val : forall E v G a,
    dec (valueC_to_closureC v) E G a <-> decctx E v G a.
  Proof.
    split; intro.
    apply decctxEamEamc; rewrite <- EAM.dec_val;
      rewrite valueC_to_closure_commutes; apply decEamcEam; auto.
    apply decEamEamc; rewrite <- valueC_to_closure_commutes; 
      rewrite EAM.dec_val; apply decctxEamcEam; auto.
  Qed.

End EAMachineC.

Module UnfoldedEAMachine (Lang : RED_LANG) (RS : RED_REF_SEM Lang) <:
  UNFOLDED_EVAL_APPLY_MACHINE Lang.

  Module EAMC := EAMachineC Lang RS.
  Import Lang.
  Import RS.RS.
  Import RS.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  Definition eqP := eqP.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive dec : term -> envC -> contextC -> stateC -> answerC -> Prop :=
  | dec_r_t : forall t t0 sC sC0 EC EC0 GC GC0 a EE GG r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, EE, GG))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t0, sC0))
      (DEC : dec t0 sC0 EC0 GC0 a),
      dec t sC EC GC a
  | dec_r_v : forall t sC EC EC0 GC GC0 v a EE GG r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, EE, GG))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v)
      (DEC : decctx EC0 v GC0 a),
      dec t sC EC GC a
  | dec_v   : forall t sC EC GC v vC a
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (TOC : proj1_sig (closure_val _ _ DCL) = vC)
      (DEC : decctx EC vC GC a),
      dec t sC EC GC a
  with decctx : contextC -> valueC -> stateC -> answerC -> Prop :=
  | dc_val : forall vC GC,
      decctx emptyC vC GC (vC, GC)
  | dc_r_t : forall fC EC EC0 GC GC0 vC aC t sC E G r c cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC))
      (DEC : dec t sC  EC0 GC0 aC),
      decctx (fC :: EC) vC GC aC
  | dc_r_v : forall fC EC EC0 vC vC0 GC GC0 aC cC E G c r
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC0)
      (DEC : decctx EC0 vC0 GC0 aC),
      decctx (fC :: EC) vC GC aC
  | dc_v   : forall fC EC vC GC vC0 aC v
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v)
      (TOC : proj1_sig (context_val _ _ _ DCT) = vC0)
      (DEC : decctx EC vC0 GC aC),
      decctx (fC :: EC) vC GC aC
  | dc_c_t : forall fC fC0 EC GC vC aC t sC c f cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC))
      (DEC : dec t sC (fC0 :: EC) GC aC),
      decctx (fC :: EC) vC GC aC
  | dc_c_v : forall fC fC0 EC GC vC vC0 aC c f cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC0)
      (DEC : decctx (fC0 :: EC) vC0 GC aC),
      decctx (fC :: EC) vC GC aC.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answerC -> Prop :=
  | e_intro : forall t v
      (DEC : dec t nil emptyC initC v),
      eval t v.

  Hint Constructors dec decctx eval.

  Lemma decEamcUeam : forall t sC EC GC aC
    (DEC : EAMC.dec (pairC t sC) EC GC aC),
    dec t sC EC GC aC.
  Proof with eauto.
    intros; change (match inl valueC (t, sC) with
                      | inl (t, s) => dec t s EC GC aC
                      | inr v0 => decctx EC v0 GC aC
                    end); rewrite <- dec_pairC.
    induction DEC using EAMC.dec_Ind with
      (P := fun c E G a (DEC : EAMC.dec c E G a) => 
        match proj1_sig (closureC_dec c) with
          | inl (t, s) => dec t s E G a
          | inr v0 => decctx E v0 G a
        end)
      (P0:= fun E v G a (DCTX : EAMC.decctx E v G a) => decctx E v G a)...
    (* Case 1 *)
    remember (closureC_dec c) as p.
    destruct p as [[[tt ssC] | vC] HH]; simpl in *.
    generalize dependent DCL; rewrite HH; intros.
    remember (proj1_sig (closureC_dec c0)) as qq; destruct qq as [[tr er] | vr].
    econstructor...
    eapply dec_r_v...
    cbv delta in DCL;
      assert (ht := dec_closure_correct (closureC_to_closure c)); 
        rewrite DCL in ht; simpl in ht.
    rewrite HH in ht; rewrite <- valueC_to_closure_commutes in ht; 
      symmetry in ht; contradiction (value_redex _ _ ht).
    (* Case 2 *)
    remember (closureC_dec c) as p.
    destruct p as [[[tt ssC] | vC] HH]; simpl in *.
    generalize dependent DCL; rewrite HH; intros.
    econstructor 3...
    cbv delta in DCL;
      assert (ht := dec_closure_correct (closureC_to_closure c)); 
        rewrite DCL in ht; simpl in ht.
    rewrite HH in ht; rewrite <- valueC_to_closure_commutes in ht;
      symmetry in ht; apply value_to_closure_injective in ht.
    remember (EAMC.closure_val _ _ DCL) as qq; destruct qq as [vT HT]; 
      simpl in TOC; rewrite HT in ht; apply valueC_to_value_injective in ht; 
        subst vT v...
    (* Case 3 *)
    remember (closureC_dec c0) as qq; destruct qq as [[[tt ss] | vv] HH]; 
      simpl in *; [econstructor | econstructor 3]... 
    rewrite <- Heqqq...
    rewrite <- Heqqq...
    (* Case 4 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; 
      simpl in *; [econstructor 5 | econstructor 6]...
    rewrite <- Heqqq...
    rewrite <- Heqqq...
  Qed.

  Lemma evalEamUeam : forall t a 
    (EV : EAMC.eval t a),
    eval t a.
  Proof.
    intros; inversion_clear EV; auto using decEamcUeam.
  Qed.

  Lemma decUeamEam : forall t sC EC GC aC
    (DEC_U : dec t sC EC GC aC),
    EAMC.dec (pairC t sC) EC GC aC.
  Proof with eauto.
    induction 1 using dec_Ind with
      (P := fun t sC EC GC aC (DEC : dec t sC EC GC aC) => 
        EAMC.dec (pairC t sC) EC GC aC)
      (P0:= fun EC vC GC aC (DEC : decctx EC vC GC aC) => 
        EAMC.decctx EC vC GC aC)...
    (* Case 1 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNF; econstructor... 
    rewrite HH; subst tt ss...
    (* Case 2 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNF; econstructor...
    rewrite HH; subst vv...
    rewrite EAMC.dec_val...
    (* Case 3 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; 
      simpl in *; inversion UNF; econstructor... 
    rewrite HH; subst tt ss...
    (* Case 4 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNF; econstructor... 
    rewrite HH; subst vv...
    rewrite EAMC.dec_val...
    (* Case 5 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; 
      simpl in *; inversion UNF; econstructor 4...
    rewrite HH; subst tt ss...
    (* Case 6 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNF; econstructor 4... 
    rewrite HH; subst vv...
    rewrite EAMC.dec_val...
   Qed.

  Lemma evalUeamEam : forall t a
    (EV : eval t a),
    EAMC.eval t a.
  Proof.
    intros; inversion_clear EV; auto using decUeamEam.
  Qed.

  Theorem evalUeam : forall t a,
    RS.RS.eval t (answerC_to_answer a) <-> eval t a.
  Proof with auto.
    intros; rewrite EAMC.evalUeam; split; eauto using evalEamUeam, evalUeamEam.
  Qed.

End UnfoldedEAMachine.

Module ProperEAMachine (Lang : RED_LANG) (SEM : RED_REF_SEM Lang) <:
  PROPER_EA_MACHINE Lang.

  Module UEAM := UnfoldedEAMachine Lang SEM.
  Import Lang.
  Import SEM.
  Import RS.
  Module P := Lang_Prop Lang.
  Import P.
  Open Scope red_scope.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  Definition eqP := eqP.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> envC -> contextC -> stateC -> configuration
  | c_apply : contextC -> valueC -> stateC -> configuration
  | c_final : answerC -> configuration.
  Notation " '<<' t '>>' " := (c_init t) : eam_scope.
  Notation " '<<' t , s , E , G '>>' " := (c_eval t s E G) : eam_scope.
  Notation " '<<' E , v , G '>>' " := (c_apply E v G) : eam_scope.
  Notation " '<<' vC , GC '>>' " := (c_final (vC, GC)) : eam_scope.
  Open Scope red_scope.
  Open Scope eam_scope.

  Reserved Notation " a '|>' b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      << t >> |> << t, nil, emptyC, initC >>
  | t_redt : forall t t0 sC sC0 EC EC0 GC GC0 E G r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t0, sC0)),
      << t, sC, EC, GC >> |> << t0, sC0, EC0, GC0 >>
  | t_redv : forall t sC EC EC0 GC GC0 E G r c cC v
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v),
      << t, sC, EC, GC >> |> << EC0, v, GC0 >>
  | t_val  : forall t sC EC GC v vC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (TOC : proj1_sig (closure_val _ _ DCL) = vC),
      << t, sC, EC, GC >> |> << EC, vC, GC >>
  | t_cfin : forall v G,
      << emptyC, v, G >> |> << v, G >>
  | t_credt: forall f v r c t sC EC EC0 GC GC0 E G cC
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
      << f :: EC, v, GC >> |> << t, sC, EC0, GC0 >>
  | t_credv: forall f v v0 r c EC EC0 GC GC0 E G cC
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v0),
      << f :: EC, v, GC >> |> << EC0, v0, GC0 >>
  | t_cval : forall vC vC0 fC v0 EC GC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v0)
      (TOC : proj1_sig (context_val _ _ _ DCT) = vC0),
      << fC :: EC, vC, GC >> |> << EC, vC0, GC >>
  | t_cct  : forall fC fC0 vC t sC c f EC GC cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
      << fC :: EC, vC, GC >> |> << t, sC, fC0 :: EC, GC >>
  | t_ccv  : forall fC fC0 vC vC0 c f EC GC cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC0),
      << fC :: EC, vC, GC >> |> << fC0 :: EC, vC0, GC >>
  where " a '|>' b " := (transition a b) : eam_scope.

  Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answerC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := term.
    Definition value := answerC.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.

    Definition trans_close := clos_trans_1n _ transition.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall (t : term) (v : value),
        trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a '|>+' b " := (AM.trans_close a b) (at level 40, no associativity).
  Hint Constructors transition AM.eval clos_trans_1n.
  Hint Unfold AM.transition AM.trans_close.

  Lemma decEamTrans : forall t sC EC GC aC
    (DEC : UEAM.dec t sC EC GC aC),
    << t, sC, EC, GC >> |>+ c_final aC .
  Proof with eauto.
    induction 1 using UEAM.dec_Ind with
      (P := fun t sC EC GC aC (DEC : UEAM.dec t sC EC GC aC) => 
        << t, sC, EC, GC >> |>+ c_final aC)
      (P0:= fun EC vC GC aC (DEC : UEAM.decctx EC vC GC aC) =>
        << EC, vC, GC >> |>+ c_final aC);
      eauto; (econstructor 2; [idtac | eauto])...
  Qed.
  Hint Resolve decEamTrans.

  Lemma evalEamMachine : forall t a
    (EV : UEAM.eval t a),
    AM.eval t a.
  Proof with eauto.
    intros; inversion_clear EV; constructor; econstructor 2...
    apply decEamTrans...
  Qed.
  Hint Resolve evalEamMachine.

  Lemma transDecEam : forall t sC EC GC GC0 vC
    (TRAN_CL : << t, sC, EC, GC >> |>+ << vC, GC0 >>),
    UEAM.dec t sC EC GC (vC, GC0).
  Proof with eauto.
    intros; refine (clos_trans_1n_ind _ transition
    (fun c c0 =>match c, c0 with
      | << t, sC, EC, GC >>, << vC, GC0 >> => UEAM.dec t sC EC GC (vC, GC0)
      | << EC, vC, GC >>, << vC0, GC0 >>   => UEAM.decctx EC vC GC (vC0, GC0)
      | _, _ => True
    end)
    _ _ _ _ TRAN_CL); intros; auto.
    (* Case 1 *)
    generalize H; clear H; case x; case y; simpl; intros; try inversion t2;
      subst; auto; inversion_clear H; constructor 1; auto.
    (* Case 2 *)
    generalize H H0 H1; clear H H0 H1; case x; case y; case z; simpl; auto;
      intros; inversion H; destruct a; subst...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecEam.

  Lemma evalMachineEam : forall t a
    (EV : AM.eval t a),
    UEAM.eval t a.
  Proof with eauto.
    intros; destruct a; inversion_clear EV; inversion_clear H; 
      inversion H0; subst...
  Qed.
  Hint Resolve evalMachineEam.

  Theorem eval_apply_correct : forall t a,
    RS.eval t (answerC_to_answer a) <-> AM.eval t a.
  Proof with auto.
    intros; rewrite UEAM.evalUeam; split...
  Qed.

  Close Scope eam_scope.
  Close Scope red_scope.

End ProperEAMachine.

Module PushEnterMachine (Lang : RED_LANG) (Sem : PE_REF_SEM Lang) <:
  PUSH_ENTER_MACHINE Lang.

  Module UEAM := UnfoldedEAMachine Lang Sem.Red_Sem.
  Import Lang.
  Import Sem.
  Import Red_Sem.
  Import RS.
  Module P := Lang_Prop Lang.
  Import P.
  Open Scope red_scope.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  Definition eqP := eqP.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Open Scope red_scope.

  Inductive dec : term -> envC -> contextC -> stateC -> answerC -> Prop :=
  | dec_r   : forall t t0 sC sC0 EC EC0 GC GC0 E G r c a
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNF : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR)
        = (pairC t0 sC0, EC0, GC0))
      (DEC : dec t0 sC0 EC0 GC0 a),
      dec t sC EC GC a
  | dec_v_e : forall t sC v vC GC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNF : proj1_sig (closure_val _ _ DCL) = vC),
      dec t sC emptyC GC (vC, GC)
  | dec_v_r : forall t t0 sC sC0 EC EC0 GC GC0 fC vC aC v r c E G
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR)
        = (pairC t0 sC0, EC0, GC0))
      (DEC : dec t0 sC0 EC0 GC0 aC),
      dec t sC (fC :: EC) GC aC
  | dec_v_c  : forall t t0 sC sC0 vC aC fC fC0 EC GC v c f
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (UNC : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0))
      (DEC : dec t0 sC0 (fC0 :: EC) GC aC),
      dec t sC (fC :: EC) GC aC.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : term -> answerC -> Prop :=
  | e_intro : forall t a
      (DEC : dec t nil emptyC initC a),
      eval t a.

  Hint Constructors dec eval.

  Lemma decUeamPem : forall t sC EC GC aC
    (DEC : UEAM.dec t sC EC GC aC),
    dec t sC EC GC aC.
  Proof with eauto.
    induction 1 using UEAM.dec_Ind with
    (P := fun t sC EC GC aC (DEC : UEAM.dec t sC EC GC aC) =>
      dec t sC EC GC aC)
    (P0:= fun EC vC GC aC (DEC : UEAM.decctx EC vC GC aC) =>
      match EC with
        | nil => aC = (vC, GC)
        | (fC :: EC0) => forall int 
            (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = int),
            match int with
              | in_red r => forall c E G t0 sC0 EC1 GC1
                  (DCT0 : dec_context (frameC_to_frame fC) (valueC_to_value vC)
                    = in_red r)
                  (CTR : contract r (contextC_to_context EC0) (stateC_to_state GC)
                    = Some (c, E, G))
                  (UNF : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT0 CTR) 
                    = (pairC t0 sC0, EC1, GC1)),
                  dec t0 sC0 EC1 GC1 aC
              | in_clo c fc => forall t0 sC0 fC0
                (DCT0 : dec_context (frameC_to_frame fC) (valueC_to_value vC)
                  = in_clo c fc)
                (UNF : proj1_sig (context_clo _ _ _ _ DCT0) 
                  = (pairC t0 sC0, fC0)),
                dec t0 sC0 (fC0 :: EC0) GC aC
              | in_val v => False
            end
      end); intros; simpl...
    (* Case 1 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; generalize dependent DCL; rewrite HH; intros; 
        inversion UNF; subst tt ss...
    (* Case 2 *)
    contradiction (closureC_dec_not_right _ _ UNF).
    (* Case 3 *)
    destruct EC; simpl in *; subst; simpl in *...
    inversion DEC; subst; simpl in *;
      remember (proj1_sig (UEAM.closure_val (pairC t sC) v DCL)) as vC;
        symmetry in HeqvC; cbv delta in DCT; unfold dec_context in IHDEC;
          assert (HDEC_U := IHDEC _ DCT); simpl in *...
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; generalize dependent DCT; rewrite HH; intros; inversion UNF; 
        subst tt ss...
    contradiction (closureC_dec_not_right _ _ UNF).
    contradiction (dec_context_not_val _ _ _ DCT).
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; generalize dependent DCT; rewrite HH; intros; inversion UNF;
        subst tt ss...
    contradiction (closureC_dec_not_right _ _ UNF).
    (* Case 4 *)
    destruct int; intros; simpl in *...
    cbv delta in DCT; cbv delta in DCT0; rewrite DCT in DCT0; inversion DCT0;
      subst; clear DCT0.
    destruct (UEAM.context_red  _ _ _ _ _ _ _ _ DCT CTR); 
      destruct (context_red _ _ _ _ _ _ _ _ DCT1 CTR0);
        simpl in *; rewrite CTR in CTR0; inversion CTR0; subst; clear CTR0.
    destruct e as [EQC1 [EQE1 EQG1]]; destruct e0 as [EQC2 [EQE2 EQG2]];
      subst c0 E0 G0; apply closureC_to_closure_injective in EQC2; 
        apply contextC_to_context_injective in EQE2;
          apply stateC_to_state_injective in EQG2; subst...
    remember (closureC_dec (pairC t0 sC0)) as qq; destruct qq 
      as [[[tt ss] | vv] QQ]; simpl in *; inversion UNF; clear Heqqq;
        apply pairC_injective in QQ; destruct QQ; subst...
    contradiction (dec_context_not_val _ _ _ DCT0).
    cbv delta in DCT; cbv delta in DCT0; rewrite DCT in DCT0; discriminate.
    (* Case 5 *)
    contradiction (closureC_dec_not_right _ _ UNF).
    (* Case 6 *)
    contradiction (dec_context_not_val _ _ _ DCT).
    (* Case 7 *)
    destruct int; intros; simpl in *.
    cbv delta in DCT; cbv delta in DCT0; rewrite DCT in DCT0; discriminate.
    contradiction (dec_context_not_val _ _ _ DCT0).
    cbv delta in DCT; cbv delta in DCT0; rewrite DCT in DCT0; inversion DCT0; 
      destruct (context_clo fC vC c0 f0 DCT1);
        destruct (UEAM.context_clo fC vC c f DCT);
          simpl in *; subst; clear DCT0.
    destruct y; destruct y0; subst; apply frameC_to_frame_injective in H2;
      apply closureC_to_closure_injective in H1; 
        remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] QQ];
          simpl in *; inversion UNF; subst tt ss; clear Heqqq; subst cC;
            apply pairC_injective in QQ; inversion QQ; subst...
    (* Case 8 *)
    contradiction (closureC_dec_not_right _ _ UNF).
  Qed.

  Lemma evalUeamPem : forall t a
    (EV : UEAM.eval t a),
    eval t a.
  Proof.
    intros; inversion_clear EV; auto using decUeamPem.
  Qed.

  Lemma decPemUeam : forall t sC EC GC aC
    (DEC : dec t sC EC GC aC),
    UEAM.dec t sC EC GC aC.
  Proof with eauto using dec_pairC.
    induction 1 using dec_Ind...
  Qed.

  Lemma evalPemUeam : forall t a
    (EV : eval t a),
    UEAM.eval t a.
  Proof.
    intros; inversion_clear EV; auto using decPemUeam.
  Qed.

  Theorem evalPem : forall t a,
    RS.eval t (answerC_to_answer a) <-> eval t a.
  Proof.
    intros; rewrite UEAM.evalUeam; split; auto using evalUeamPem, evalPemUeam.
  Qed.

End PushEnterMachine.

Module ProperPEMachine (Lang : RED_LANG) (Sem : PE_REF_SEM Lang) <:
  PROPER_PE_MACHINE Lang.

  Module PEM := PushEnterMachine Lang Sem.
  Import Lang.
  Import Sem.
  Import Red_Sem.
  Import RS.
  Module P := Lang_Prop Lang.
  Import P.
  Open Scope red_scope.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  Definition eqP := eqP.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> envC -> contextC -> stateC -> configuration
  | c_final : answerC -> configuration.

  Notation " '<<' t '>>' " := (c_init t) : pem_scope.
  Notation " '<<' t , s , E , G '>>' " := (c_eval t s E G) : pem_scope.
  Notation " '<<' vC , GC '>>' " := (c_final (vC, GC)) : pem_scope.

  Open Scope red_scope.
  Open Scope pem_scope.

  Reserved Notation " a '|>' b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      << t >> |> << t, nil, emptyC, initC >>
  | t_red  : forall t t0 sC sC0 EC EC0 GC GC0 E G r c
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNF : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR)
        = (pairC t0 sC0, EC0, GC0)),
      << t, sC, EC, GC >> |> << t0, sC0, EC0, GC0 >>
  | t_cval : forall t sC v vC GC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNF : proj1_sig (closure_val _ _ DCL) = vC),
      << t, sC, emptyC, GC >> |> << vC, GC >>
  | t_cred : forall t t0 sC sC0 fC EC EC0 GC GC0 E G vC v r c
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR)
        = (pairC t0 sC0, EC0, GC0)),
      << t, sC, fC :: EC, GC >> |> << t0, sC0, EC0, GC0 >>
  | t_crec : forall t t0 sC sC0 fC fC0 EC GC vC v c f
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (UNC : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0)),
      << t, sC, fC :: EC, GC >> |> << t0, sC0, fC0 :: EC, GC >>
  where " c '|>' c0 " := (transition c c0) : pem_scope.

  Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answerC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := term.
    Definition value := answerC.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.

    Definition trans_close := clos_trans_1n _ transition.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall (t : term) (v : value),
        trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Hint Constructors transition clos_trans_1n AM.eval.
  Hint Unfold AM.transition AM.trans_close.
  Notation " a '|>+' b " := (AM.trans_close a b) (at level 40, no associativity).

  Lemma decPemTrans : forall t sC EC GC GC0 vC
    (DEC : PEM.dec t sC EC GC (vC, GC0)),
    << t, sC, EC, GC >> |>+ << vC, GC0 >>.
  Proof with eauto.
    induction 1; eauto; (econstructor 2; [idtac | eauto])...
  Qed.
  Hint Resolve decPemTrans.

  Lemma evalPemMachine : forall t a
    (EV : PEM.eval t a),
    AM.eval t a.
  Proof with eauto.
    intros; inversion_clear EV; constructor; econstructor 2...
    destruct a; apply decPemTrans...
  Qed.
  Hint Resolve evalPemMachine.

  Lemma transDecPem : forall t sC EC vC GC GC0
    (TCL : << t, sC, EC, GC >> |>+ << vC, GC0 >>),
    PEM.dec t sC EC GC (vC, GC0).
  Proof with eauto.
    intros t sC EC vC GC GC0 TCL; refine (clos_trans_1n_ind _ transition
    (fun c c0 => match c, c0 with
      | << t, sC, EC, GC >>, << vC, GC0 >> => PEM.dec t sC EC GC (vC, GC0)
      | _, _ => True
    end) _ _ _ _ TCL); intros...
    generalize H; clear H; case x; case y; simpl; intros; 
      try inversion t2; subst; auto; inversion_clear H; econstructor 2...
    generalize H H0 H1; clear H H0 H1; case x; case y; case z; simpl;
      auto; intros; inversion H; destruct a; subst...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecPem.

  Lemma evalMachinePem : forall t a
    (EV : AM.eval t a),
    PEM.eval t a.
  Proof.
    intros; destruct a; inversion_clear EV; inversion_clear H; inversion H0;
      subst; auto.
  Qed.
  Hint Resolve evalMachinePem.

  Theorem push_enter_correct : forall t a,
    RS.eval t (answerC_to_answer a) <-> AM.eval t a.
  Proof.
    intros; rewrite PEM.evalPem; split; auto.
  Qed.

End ProperPEMachine.
