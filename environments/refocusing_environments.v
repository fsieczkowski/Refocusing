Require Import Setoid.
Require Export refocusing_signatures_env.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.

Module Lang_Prop (R : RED_LANG) : LANG_PROP R.

  Import R.
  Notation " E · E0 " := (compose E E0) (at level 40) : red_scope.
  Notation " E × E0 " := (composeC E E0) (at level 40) : red_scope.
  Notation " E [ c ] " := (plug c E) (at level 50) : red_scope.
  Open Scope red_scope.

  Lemma plug_empty : forall c, empty [ c ] = c.
  Proof. auto. Qed.
  Lemma compose_empty : forall c : context, c =  c · empty.
  Proof. apply app_nil_end. Qed.
  Lemma composeC_emptyC : forall Ec : contextC, Ec = Ec × emptyC.
  Proof. apply app_nil_end. Qed.
  Lemma plug_compose : forall (E E0 : context) (c : closure), E · E0 [ c ] = E0 [ E [ c ] ].
  Proof. apply fold_left_app. Qed.
  Lemma composeC_compose : forall Ec Ec0, contextC_to_context (Ec × Ec0) = contextC_to_context Ec · contextC_to_context Ec0.
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

  Inductive dec : closure -> context -> decomp -> Prop :=
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
                decctx (f :: E) v d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
  Hint Constructors dec decctx.

  Lemma cl_o_trans : forall c c0 c1, c <| c0 -> c0 <| c1 -> c <| c1.
  Proof with auto.
    induction 2;
    econstructor 2; eauto.
  Qed.

  Ltac isda := intros; simpl in *; try discriminate; auto.

  Lemma plug_le_eq : forall E c c0 (PLUG : E [ c0 ] = c), c0 <| c \/ (E = empty /\ c = c0).
  Proof with isda.
    induction E; intros...
    destruct (IHE _ _ PLUG) as [H0 | [H1 H0]]; clear IHE; left;
    [eapply cl_o_trans; eauto | subst]; repeat econstructor...
  Qed.

  Lemma cl_c : forall c c0 (LE_C : c <| c0), exists E, E [ c ] = c0.
  Proof with isda.
    intros; induction LE_C; inversion H; subst.
    exists (f :: nil)...
    destruct IHLE_C as [E PLUG].
    exists (E ++ (f :: empty)); unfold plug in *; rewrite fold_left_app; simpl; subst...
  Qed.

  Definition value_one_step (v v0 : value) : Prop := subclosure_one_step (value_to_closure v) (value_to_closure v0).
  Definition value_order := clos_trans_n1 _ value_one_step.
    
  Notation " a <v| b " := (value_order a b) (at level 40) : red_scope.

  Lemma value_order_wf : well_founded value_order.
  Proof.
    apply wf_clos_trans_r; apply wf_inverse_image; apply subclosure_one_step_wf.
  Qed.

    Lemma dec_val : forall v E d (DEC : dec (value_to_closure v) E d), decctx E v d.
    Proof with isda.
      induction v using (well_founded_ind value_order_wf); intros.
      remember (R.dec_closure (value_to_closure v)) as int_dec; assert (DEC_C_OK := dec_closure_correct (value_to_closure v));
      destruct int_dec; rewrite <- Heqint_dec in DEC_C_OK.
      symmetry in DEC_C_OK; contradiction (value_redex _ _ DEC_C_OK).
      apply value_to_closure_injective in DEC_C_OK; inversion DEC; subst; unfold dec_closure in DCL;
      rewrite DCL in Heqint_dec; inversion Heqint_dec; subst...
      destruct (value_trivial v c (f :: nil)) as [EMP | [v0 V0_EQ]]; simpl...
      subst c; symmetry in DEC_C_OK; assert (V_ORD := scl _ _ _ DEC_C_OK);
      apply (tn1_step _ value_one_step) in V_ORD; change (v0 <v| v) in V_ORD.
      inversion DEC; subst; unfold dec_closure in DCL; rewrite DCL in Heqint_dec; inversion Heqint_dec; subst;
      clear DEC Heqint_dec DCL; apply (H _ V_ORD) in DEC_C.
      generalize dependent v0; induction f0 using (well_founded_ind frame_order_wf); intros.
      remember (R.dec_context f0 v0) as int_dec; assert (DEC_E_OK := R.dec_context_correct f0 v0);
      destruct int_dec; rewrite <- Heqint_dec in DEC_E_OK; rewrite <- DEC_C_OK in DEC_E_OK; symmetry in DEC_E_OK.
      contradiction (value_redex _ _ DEC_E_OK).
      clear H H0; apply value_to_closure_injective in DEC_E_OK; subst.
      inversion DEC_C; subst; unfold dec_context in DCT; rewrite DCT in Heqint_dec; inversion Heqint_dec; subst...
      destruct (value_trivial v c (f :: nil)) as [EMP | [v1 V1_EQ]]; subst...
      inversion DEC_C; subst; unfold dec_context in DCT; rewrite DCT in Heqint_dec; inversion Heqint_dec; subst;
      clear Heqint_dec.
      apply H0 with f2 v1...
      destruct (dec_context_clo_next _ _ _ _ DCT)...
      repeat econstructor; eauto.
      apply H...
      repeat econstructor; eauto.
    Qed.

    Lemma val_dec : forall v E d (DEC_E : decctx E v d), dec (value_to_closure v) E d.
    Proof with isda; eauto.
      induction v using (well_founded_ind value_order_wf); intros.
      remember (R.dec_closure (value_to_closure v)) as int_dec; assert (DEC_C_OK := dec_closure_correct (value_to_closure v));
      destruct int_dec; rewrite <- Heqint_dec in DEC_C_OK; symmetry in DEC_C_OK.
      contradiction (value_redex _ _ DEC_C_OK).
      apply value_to_closure_injective in DEC_C_OK; subst; econstructor...
      destruct (value_trivial v c (f :: nil)) as [EMP | [v0 V0_EQ]]; subst...
      econstructor 3...
      apply H; [ repeat econstructor | clear Heqint_dec]...
      generalize dependent v0; induction f using (well_founded_ind frame_order_wf); intros.
      remember (R.dec_context f v0) as int_dec; assert (DEC_E_OK := R.dec_context_correct f v0);
      destruct int_dec; rewrite <- Heqint_dec in DEC_E_OK; rewrite <- DEC_C_OK in DEC_E_OK; symmetry in DEC_E_OK.
      contradiction (value_redex _ _ DEC_E_OK).
      clear H H0; apply value_to_closure_injective in DEC_E_OK; subst; econstructor...
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

    Lemma decompose : forall c, (exists v, c = value_to_closure v) \/ (exists r, exists E, c = E [ redex_to_closure r ]).
    Proof with eauto.
      induction c using (well_founded_ind closure_order_wf); intros.
      remember (R.dec_closure c) as int; assert (DEC_CL_OK := dec_closure_correct c);
      destruct int; rewrite <- Heqint in DEC_CL_OK...
      subst...
      destruct (H c0) as [[v Hv] | [r [E HrE]]]...
      subst c0; clear Heqint; generalize dependent v; induction f using (well_founded_ind frame_order_wf); intros.
      remember (R.dec_context f v) as int; assert (DEC_CT_OK := R.dec_context_correct f v);
      destruct int; rewrite <- Heqint in DEC_CT_OK; rewrite DEC_CL_OK in DEC_CT_OK...
      right; exists r; exists empty...
      destruct (H c0) as [[v0 Hv] | [r [E HrE]]]...
      symmetry in Heqint; destruct (dec_context_clo_next _ _ _ _ Heqint) as [H1 _].
      subst c0; destruct (H0 f0 H1 v0 DEC_CT_OK) as [[v1 Hv1] | [r [E HrE]]]...
      right; exists r; exists (E · (f0 :: nil)); 
      subst c0; rewrite P.plug_compose...
      right; exists r; exists (E · (f :: nil));
      subst c0; rewrite P.plug_compose...
    Qed.

    Lemma dec_redex_self_e : forall r, dec (redex_to_closure r) empty (d_red r empty).
    Proof with isda; eauto.
      intros; remember (R.dec_closure (redex_to_closure r)) as int; destruct int;
      assert (DEC_CL_OK := dec_closure_correct (redex_to_closure r)); rewrite <- Heqint in DEC_CL_OK; simpl in *.
      apply redex_to_closure_injective in DEC_CL_OK; subst; constructor...
      contradict (value_redex _ _ DEC_CL_OK).
      symmetry in Heqint; assert (CL_T := dec_closure_clo_top _ _ _ Heqint); econstructor 3...
      destruct (redex_trivial r c (f :: empty) DEC_CL_OK) as [EMP | [v V_EQ]]; subst...
      clear CL_T Heqint.
      generalize dependent v; induction f using (well_founded_ind frame_order_wf); intros.
      apply val_dec.
      remember (R.dec_context f v) as int; assert (D_CT_OK := R.dec_context_correct f v);
      rewrite <- Heqint in D_CT_OK; destruct int; simpl in D_CT_OK; rewrite DEC_CL_OK in D_CT_OK.
      apply redex_to_closure_injective in D_CT_OK; subst...
      contradiction (value_redex _ _ D_CT_OK).
      econstructor 4...
      destruct (redex_trivial r c (f0 :: empty) D_CT_OK) as [EMP | [v1 V1_EQ]]; subst...
      symmetry in Heqint; destruct (dec_context_clo_next _ _ _ _ Heqint); apply H...
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
      (P0:= fun E v d (DEC_E : decctx E v d) => decomp_to_closure d = E [ value_to_closure v ]); 
      simpl; auto; match goal with
      | [ DT: (dec_closure ?t = ?int) |- _ ] => unfold dec_closure in DT; assert (hh := R.dec_closure_correct t); rewrite DT in hh
      | [ DC: (dec_context ?ec ?v = ?int) |- _ ] => unfold dec_context in DC; assert (hh := R.dec_context_correct ec v); rewrite DC in hh
      end; try rewrite IHdec; rewrite <- hh; subst; auto.
    Qed.

    Lemma dec_plug_rev : forall E E0 c d, dec c (E · E0) d -> dec (E [ c ]) E0 d.
    Proof with isda.
      induction E...
      apply IHE; clear IHE; remember (R.dec_closure (atom_plug c a)) as int; destruct int;
      assert (D_CL := dec_closure_correct (atom_plug c a)); rewrite <- Heqint in D_CL; symmetry in Heqint.
      discriminate (dec_closure_red_empty _ _ Heqint c (a :: nil)); reflexivity.
      discriminate (dec_closure_val_empty _ _ Heqint c (a :: nil))...
      destruct (dec_frame_ord c0 c f a D_CL) as [LT | [GT | [EC EF]]]; try (subst; econstructor 3; eauto; fail).
      contradict (dec_closure_clo_top _ _ _ Heqint _ LT).
      symmetry in D_CL; destruct (frame_det _ _ _ _ GT D_CL) as [v V_EQ]; subst.
      econstructor 3; eauto.
      clear Heqint; generalize dependent v; induction f using (well_founded_ind frame_order_wf); intros.
      apply val_dec.
      remember (R.dec_context f v) as int; destruct int; symmetry in Heqint;
      assert (D_CT := dec_context_correct f v); rewrite Heqint in D_CT.
      contradiction (dec_context_red_bot _ _ _ Heqint a).
      contradiction (dec_context_val_bot _ _ _ Heqint a).
      destruct (dec_context_clo_next _ _ _ _ Heqint) as [LT NLT].
      econstructor 4; eauto; rewrite <- D_CL in D_CT.
      destruct (dec_frame_ord _ _ _ _ D_CT) as [LT0 | [GT0 | [EC EF]]]; try (subst; auto; fail).
      contradiction (NLT a GT).
      symmetry in D_CT; clear NLT; destruct (frame_det _ _ _ _ GT0 D_CT) as [v0 V0_EQ]; subst...
    Qed.

    Lemma dec_plug : forall E E0 c d (DEC : dec (E [ c ]) E0 d), dec c (E · E0) d.
    Proof with isda.
      induction E...
      apply IHE in DEC; clear IHE; inversion DEC; subst; unfold dec_closure in DCL; clear DEC;
      assert (D_CL := dec_closure_correct (atom_plug c a)); rewrite DCL in D_CL.
      discriminate (dec_closure_red_empty _ _ DCL c (a :: nil)); reflexivity.
      discriminate (dec_closure_val_empty _ _ DCL c (a :: empty))...
      destruct (dec_frame_ord c1 c f a D_CL) as [LT | [GT | [EC EF]]]; subst...
      contradiction (dec_closure_clo_top _ _ _ DCL a).
      symmetry in D_CL; destruct (frame_det _ _ _ _ GT D_CL) as [v V_EQ]; subst.
      clear DCL; generalize dependent v; induction f using (well_founded_ind frame_order_wf); intros.
      assert (DV := dec_val _ _ _ DEC_C); inversion DV; subst; clear DEC_C;
      assert (D_CT := dec_context_correct f v); unfold dec_context in DCT; rewrite DCT in D_CT; simpl in D_CT.
      contradiction (dec_context_red_bot _ _ _ DCT a).
      contradiction (dec_context_val_bot _ _ _ DCT a).
      clear DV; rewrite <- D_CL in D_CT.
      destruct (dec_context_clo_next _ _ _ _ DCT) as [LT NLT].
      destruct (dec_frame_ord _ _ _ _ D_CT) as [LT0 | [GT0 | [VE FE]]]; subst...
      contradiction (NLT a).
      symmetry in D_CT; destruct (frame_det _ _ _ _ GT0 D_CT) as [v1 V1_EQ]; subst; eauto.
    Qed.

    Inductive decempty : closure -> decomp -> Prop :=
    | d_intro : forall c d (DEC : dec c empty d), decempty c d.

    Inductive iter : decomp -> value -> Prop :=
    | i_val : forall v, iter (d_val v) v
    | i_red : forall r c E d v 
                (CONTR : contract r = Some c)
                (DEMP  : decempty (E [ c ]) d)
                (ITER  : iter d v),
                iter (d_red r E) v.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall t d v
                  (DEMP : decempty (pair t nil) d)
                  (ITER : iter d v),
                  eval t v.

    Module P := P.

  End RS.

  Definition dec_closure_correct := R.dec_closure_correct.
  Definition dec_context_correct := R.dec_context_correct.

  Lemma dec_val_self : forall v E d, dec (value_to_closure v) E d <-> decctx E v d.
  Proof.
    split; [apply dec_val | apply val_dec]; auto.
  Qed.
  Definition dcl := dcl.
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

  Lemma dec_is_function : forall c d d0, decempty c d -> decempty c d0 -> d = d0.
  Proof.
    intros c d d0 DE DE0; inversion_clear DE; inversion_clear DE0.
    refine (dec_Ind (fun c E d (H : dec c E d) => forall d0 (DEC : dec c E d0), d = d0)
    (fun E v d (H : decctx E v d) => forall d0 (DCTX : decctx E v d0),  d = d0)
    _ _ _ _ _ _ _ c empty d DEC d0 DEC0); intros; simpl; auto; try apply H; match goal with
    | [ RD : (dec ?c ?E ?d), DCL : (dec_closure ?c = ?int) |- _ ] => inversion RD; rewrite DCL0 in DCL; inversion DCL
    | [ RC : (decctx (?f :: ?E) ?v ?d), DCT : (dec_context ?f ?v = ?int) |- _ ] => inversion RC; rewrite DCT0 in DCT; inversion DCT
    | [ RC : (decctx empty ?v ?d) |- _] => inversion RC
    end; subst; auto.
  Qed.
  Hint Resolve dec_is_function : prop.

  Lemma iter_is_function : forall d v v0, iter d v -> iter d v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros.
    inversion H...
    inversion H0; subst; rewrite CONTR0 in CONTR; inversion CONTR; subst;
    apply IHiter; cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.

  Lemma eval_is_function : forall t v v0, eval t v -> eval t v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros; inversion H; subst; cutrewrite (d = d0) in ITER...
  Qed.

  Lemma dec_correct : forall c E d, dec c E d -> decomp_to_closure d = E [c].
  Proof.
    induction 1 using RS.dec_Ind with
    (P := fun c E d (H : dec c E d) => decomp_to_closure d = E [c])
    (P0:= fun E v d (H : decctx E v d) => decomp_to_closure d = E [value_to_closure v]); simpl; auto;
    match goal with
    | [ DCL : dec_closure ?cl = ?int |- _ ] => assert (D_CL := dec_closure_correct cl); rewrite DCL in D_CL; simpl in D_CL; rewrite <- D_CL
    | [ DCT : dec_context ?f ?v = ?int |- _ ] => assert (D_CT := dec_context_correct f v); rewrite DCT in D_CT; simpl in D_CT; rewrite <- D_CT
    end; auto.
  Qed.

  Lemma dec_total : forall c, exists d, decempty c d.
  Proof.
    intro c; destruct (decompose c) as [[v Hv] | [r [E Hp]]]; intros; subst c.
    exists (d_val v); constructor; rewrite dec_val_self; constructor.
    exists (d_red r E); constructor; apply dec_plug_rev;
    rewrite <- P.compose_empty; apply dec_redex_self.
  Qed.

  Lemma unique_decomposition : forall c, (exists v, c = value_to_closure v) \/ 
      (exists r, exists E, c = E [redex_to_closure r] /\
	  forall r0 E0, c = E0 [redex_to_closure r0] -> r=r0 /\ E = E0).
  Proof.
    intro c; destruct (decompose c) as [[v H] | [r [E H]]]; intros;
    [left; exists v | right; exists r; exists E; split]; auto; intros.
    assert (DE_RE : decempty c (d_red r E)).
    constructor; rewrite H; apply dec_plug_rev; rewrite <- P.compose_empty; apply dec_redex_self.
    assert (DE_R0E0 : decempty c (d_red r0 E0)).
    constructor; rewrite H0; apply dec_plug_rev; rewrite <- P.compose_empty; apply dec_redex_self.
    assert (hh := dec_is_function _ _ _ DE_RE DE_R0E0); injection hh; intros; auto.
  Qed.

End Red_Prop.

Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM (R)) <: PRE_ABSTRACT_MACHINE (R).

  Module LP := Lang_Prop R.
  Import R.
  Import RS.RS.
  Import RS.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  (** A decomposition relation specified in terms of the atomic functions above *)
  Inductive dec : closure -> context -> decomp -> Prop :=
  | d_r    : forall (c : closure) (E : context) (r : redex)
               (DCL  : dec_closure c = in_red r),
               dec c E (d_red r E)
  | d_v    : forall (c : closure) (E : context) (v : value) (d : decomp)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v d),
               dec c E d
  | d_clo  : forall (c c0 : closure) (E : context) (f : frame) (d : decomp)
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
                (DCT   : dec_context f v = R.in_clo c f0)
                (DEC_C : dec c (f0 :: E) d),
                decctx (f :: E) v d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall (v : value), iter (d_val v) v
  | i_red : forall (r : redex) (c : closure) (E : context) (d : decomp) (v : value)
              (CONTR  : contract r = Some c)
              (DEC    : dec c E d)
              (R_ITER : iter d v),
              iter (d_red r E) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (d : decomp) (v : value)
                (DEC  : dec (pair t nil) empty d)
                (ITER : iter d v),
                eval t v.

  Hint Constructors dec decctx iter eval RS.dec RS.decctx RS.iter.
  Hint Unfold RS.RS.dec.

  Lemma dec_id_l : forall c E d, RS.RS.dec c E d -> dec c E d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
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

  Lemma decctx_id_l : forall E v d, RS.decctx E v d -> decctx E v d.
  Proof with eauto.
    induction 1 using RS.decctx_Ind with 
    (P := fun c E d (H : RS.RS.dec c E d) => dec c E d)
    (P0:= fun E v d (H0 : RS.decctx E v d) => decctx E v d)...
  Qed.

  Lemma decctx_id_r : forall E v d, decctx E v d -> RS.decctx E v d.
  Proof with eauto.
    induction 1 using decctx_Ind with 
    (P := fun c E d (H : dec c E d) => RS.RS.dec c E d)
    (P0:= fun E v d (H0 : decctx E v d) => RS.decctx E v d)...
  Qed.

  Lemma iterRedPam : forall d v, RS.RS.iter d v -> iter d v.
  Proof with eauto.
    induction 1; auto; econstructor 2; inversion_clear D_EM; eauto;
    rewrite LP.compose_empty with (c := E); auto using dec_plug.
  Qed.

  Lemma evalRedPam : forall (t : term) (v : value), RS.RS.eval t v -> eval t v.
  Proof with auto.
    intros t v H; inversion_clear H; constructor 1 with d; [inversion_clear D_EM | apply iterRedPam]...
  Qed.
  Hint Resolve evalRedPam.

  Lemma iterPamRed : forall d v (ITER : iter d v), RS.RS.iter d v.
  Proof with auto.
    induction 1; auto; econstructor 2; eauto; constructor;
    apply dec_plug_rev; rewrite <- LP.compose_empty...
  Qed.

  Lemma evalPamRed : forall (t : term) (v : value), eval t v -> RS.RS.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor 1 with d; [ constructor | apply iterPamRed]; auto.
  Qed.
  Hint Resolve evalPamRed.

  Theorem evalPam : forall (t : term) (v : value), RS.RS.eval t v <-> eval t v.
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

  Inductive dec : closure -> context -> value -> Prop :=
  | d_dec  : forall (c : closure) (E : context) (r : redex) (v : value)
               (DCL   : dec_closure c = in_red r)
               (ITER  : iter (d_red r E) v),
               dec c E v
  | d_v    : forall (c : closure) (E : context) (v v0 : R.value)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v v0),
               dec c E v0
  | d_clo  : forall (c c0 : closure) (f : frame) (E : context) (v : value)
               (DCL   : dec_closure c = in_clo c0 f)
               (DEC_C : dec c0 (f :: E) v),
               dec c E v
  with decctx : context -> value -> value -> Prop :=
  | dc_end  : forall (v v0 : value)
               (ITER  : iter (d_val v) v0),
               decctx empty v v0
  | dc_dec  : forall (v v0 : value) (f : frame) (E : context) (r : redex)
               (DCT   : dec_context f v = in_red r)
               (ITER  : iter (d_red r E) v0),
               decctx (f :: E) v v0
  | dc_val  : forall (v v0 v1 : value) (f : frame) (E : context)
               (DCT   : dec_context f v = in_val v0)
               (DEC_E : decctx E v0 v1),
               decctx (f :: E) v v1
  | dc_term : forall (v v0 : value) (c : closure) (f f0 : frame) (E : context)
               (DCT   : dec_context f v = in_clo c f0)
               (DEC_C : dec c (f0 :: E) v0),
               decctx (f :: E) v v0
  with iter : decomp -> value -> Prop :=
  | i_val : forall (v : value), iter (d_val v) v
  | i_red : forall (r : redex) (E : context) (c : closure) (v : value)
               (CONTR : contract r = Some c)
               (DEC_C : dec c E v),
               iter (d_red r E) v.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value), dec (pair t nil) empty v -> eval t v.

  Hint Constructors dec decctx iter eval.

  Lemma decPamSam : forall c E d,
    PAM.dec c E d -> forall (v : value), iter d v -> dec c E v.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P := fun t c d (H:PAM.dec t c d) => forall v, iter d v -> dec t c v)
    (P0 := fun c v d (H:PAM.decctx c v d) => forall v', iter d v' -> decctx c v v')...
  Qed.
  Hint Resolve decPamSam.

  Lemma decctxPamSam : forall E v d v0
    (DEC : PAM.decctx E v d)
    (ITR : iter d v0),
    decctx E v v0.
  Proof with eauto.
    induction 1; intros...
  Qed.

  Lemma iterPamSam : forall d v (ITER : PAM.iter d v), iter d v.
  Proof with eauto.
    induction 1...
  Qed.
  Hint Resolve iterPamSam.

  Lemma evalPamSam : forall (t : term) (v : value), PAM.eval t v -> eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H...
  Qed.
  Hint Resolve evalPamSam.

  Module P := Red_Prop R RS.

  Lemma decSamPam : forall c E v (DEC : dec c E v) d (PDEC : PAM.dec c E d), PAM.iter d v.
  Proof with auto.
    induction 1 using dec_Ind with
    (P  := fun t c v (DEC : dec t c v) => forall d, PAM.dec t c d -> PAM.iter d v)
    (P0 := fun v c v' (DEC_E : decctx v c v') => forall d, PAM.decctx v c d -> PAM.iter d v')
    (P1 := fun d v (ITER : iter d v) => PAM.iter d v); intros; simpl; auto;
    try (try apply IHDEC; inversion H; cbv delta in *; match goal with
    | [ D0 : RS.dec_closure ?cl = ?int, D1 : RS.dec_closure ?cl = ?int0 |- _ ] => rewrite D0 in D1; inversion D1
    | [ D0 : RS.dec_context ?f ?v = ?int, D1 : RS.dec_context ?f ?v = ?int0 |- _ ] => rewrite D0 in D1; inversion D1
    | [ |- _ ] => idtac
    end; subst)...
    destruct(P.dec_total (plug c E)) as [d H0]; inversion_clear H0.
    apply RS.RS.dec_plug in DEC0; rewrite <- LP.compose_empty in DEC0; eauto.
  Qed.
  Hint Resolve decSamPam.

  Lemma decctxSamPam : forall E v v0 d 
    (DEC : decctx E v v0)
    (PDEC : PAM.decctx E v d),
    PAM.iter d v0.
  Proof with eauto.
    induction 1; intros; inversion_clear PDEC; unfold dec_context in *; 
      unfold PAM.dec_context in *;
        try (rewrite DCT0 in DCT; inversion DCT; subst)...
    inversion_clear ITER...
    inversion_clear ITER; destruct (P.dec_total (plug c E)) as [dd H0]; 
      inversion_clear H0; apply RS.RS.dec_plug in DEC; 
        rewrite <- LP.compose_empty in DEC...
  Qed.

  Lemma evalSamPam : forall (t : term) (v : value), eval t v -> PAM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; destruct (P.dec_total (pair t nil)) as [d H]; inversion_clear H...
  Qed.
  Hint Resolve evalSamPam.

  Theorem evalSam : forall (t : term) (v : value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros t v; rewrite PAM.evalPam; split; intros...
  Qed.

  Lemma dec_val : forall E v v0, 
    dec (value_to_closure v) E v0 <-> decctx E v v0.
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

Module EvalApplyMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: EVAL_APPLY_MACHINE R.

  Module SAM := StagedAbstractMachine R RS.
  Import R.
  Import RS.RS.
  Import RS.

  Definition dec_closure := dec_closure.
  Definition dec_context := dec_context.

  Definition dec_closure_correct := dec_closure_correct.
  Definition dec_context_correct := dec_context_correct.

  Inductive dec : closure -> context -> value -> Prop :=
  | d_d_r  : forall (c c0 : closure) (E : context) (r : redex) (v : value)
               (DCL   : dec_closure c = in_red r)
               (CONTR : contract r = Some c0)
               (DEC_C : dec c0 E v),
               dec c E v
  | d_v    : forall (c : closure) (E : context) (v v0 : value)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v v0),
               dec c E v0
  | d_clo  : forall (c c0 : closure) (f : frame) (E : context) (v : value)
               (DCL   : dec_closure c = in_clo c0 f) 
               (DEC_C : dec c0 (f :: E) v),
               dec c E v
  with decctx : context -> value -> value -> Prop :=
  | dc_end : forall (v : value), decctx empty v v
  | dc_red : forall (v v0 : value) (f : frame) (E : context) (r : redex) (c : closure)
               (DCT   : dec_context f v = in_red r)
               (CONTR : contract r = Some c)
               (DEC_C : dec c E v0),
               decctx (f :: E) v v0
  | dc_rec : forall (v v0 v1 : value) (f : frame) (E : context)
               (DCT   : dec_context f v = in_val v0)
               (DEC_E : decctx E v0 v1),
               decctx (f :: E) v v1
  | dc_clo : forall (v v0 : value) (f f0 : frame) (E : context) (c : closure)
               (DCT   : dec_context f v = in_clo c f0)
               (DEC_C : dec c (f0 :: E) v0),
               decctx (f :: E) v v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value), dec (pair t nil) empty v -> eval t v.

  Hint Constructors dec decctx eval.

  Lemma decSamEam : forall c E v (DEC_S : SAM.dec c E v), dec c E v.
  Proof with eauto.
    induction 1 using SAM.dec_Ind with
    (P := fun c E v (H:SAM.dec c E v) => dec c E v)
    (P0:= fun E v v' (H:SAM.decctx E v v') => decctx E v v')
    (P1:= fun d v (H:SAM.iter d v) => match d with
                                        | R.d_val v' => decctx empty v v'
                                        | R.d_red r E => forall c,
                                                         contract r = Some c -> dec c E v
                                      end);
    simpl; intros; try inversion ITER; subst; eauto; congruence.
  Qed.

  Lemma decctxSamEam : forall E v v0
    (DEC : SAM.decctx E v v0),
    decctx E v v0.
  Proof with eauto using decSamEam.
    induction 1; try inversion_clear ITER...
  Qed.

  Lemma evalSamEam : forall (t : term) (v : value), SAM.eval t v -> eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decSamEam; auto.
  Qed.
  Hint Resolve evalSamEam.

  Lemma decEamSam : forall c E v (DEC : dec c E v), SAM.dec c E v.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun t c v (H:dec t c v) => SAM.dec t c v)
    (P0:= fun v c v' (H:decctx v c v') => SAM.decctx v c v'); intros; simpl...
  Qed.

  Lemma decctxEamSam : forall E v v0
    (DEC : decctx E v v0),
    SAM.decctx E v v0.
  Proof.
    induction 1; try inversion_clear ITER; eauto using decEamSam.
  Qed.

  Lemma evalEamSam : forall (t : term) (v : value), eval t v -> SAM.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamSam; auto.
  Qed.
  Hint Resolve evalEamSam.

  Theorem evalEam : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros t v; rewrite SAM.evalSam; split...
  Qed.

  Lemma dec_val : forall E v v0, 
    dec (value_to_closure v) E v0 <-> decctx E v v0.
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

  Definition dcl := dcl.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive dec : closureC -> contextC -> valueC -> Prop :=
  | d_d_r  : forall (c c0 : closureC) (cc : closure) (E : contextC) (ofc : option frameC) (r : redex) (v : valueC)
               (DCL   : dec_closure (closureC_to_closure c) = in_red r)
               (CONTR : contract r = Some cc)
               (TO_C  : proj1_sig (closure_red _ _ _ DCL CONTR) = (c0, ofc))
               (DEC_C : dec c0 (opt_to_list ofc ++ E) v),
               dec c E v
  | d_v    : forall (c : closureC) (E : contextC) (vv : value) (v v0 : valueC)
               (DCL   : dec_closure (closureC_to_closure c) = in_val vv)
               (TO_C  : proj1_sig (closure_val _ _ DCL) = v)
               (DEC_E : decctx E v v0),
               dec c E v0
(*  | d_clo  : forall (c c0 : closureC) (cc : closure) (f : frame) (fC : frameC) (E : contextC) (v : valueC)
               (DCL   : dec_closure c = in_clo cc f)
               (TO_C  : closure_val
               (DEC_C : dec c0 (f :: E) v),
               dec c E v*)
  with decctx : contextC -> valueC -> valueC -> Prop :=
  | dc_end : forall (v : valueC), decctx emptyC v v
  | dc_red : forall (v v0 : valueC) (f : frameC) (E : contextC) (r : redex) (c : closure) (cC : closureC) (ofc : option frameC)
               (DCT   : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
               (CONTR : contract r = Some c)
               (TO_C  : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, ofc))
               (DEC_C : dec cC (opt_to_list ofc ++ E) v0),
               decctx (f :: E) v v0
  | dc_rec : forall (v v0 v1 : valueC) (vv : value) (f : frameC) (E : contextC)
               (DCT   : dec_context (frameC_to_frame f) (valueC_to_value v) = in_val vv)
               (TO_C  : proj1_sig (context_val _ _ _ DCT) = v0)
               (DEC_E : decctx E v0 v1),
               decctx (f :: E) v v1
  | dc_clo : forall (v v0 : valueC) (f f0 : frameC) (ff : frame) (E : contextC) (c : closure) (cC : closureC)
               (DCT   : dec_context (frameC_to_frame f) (valueC_to_value v) = in_clo c ff)
               (TO_C  : proj1_sig (context_clo _ _ _ _ DCT) = (cC, f0))
               (DEC_C : dec cC (f0 :: E) v0),
               decctx (f :: E) v v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall (t : term) (v : valueC), dec (pairC t nil) emptyC v -> eval t v.
  Hint Constructors dec decctx eval.

  Lemma decEamEamc : forall cC EC vC, EAM.dec (closureC_to_closure cC) (contextC_to_context EC) (valueC_to_value vC) -> dec cC EC vC.
  Proof with eauto.
    intros.
    cutrewrite (EC = opt_to_list None ++ EC); auto.
    refine (EAM.dec_Ind
      (fun c E v (DEC_EAM : EAM.dec c E v) => forall cC ofC EC vC
        (OK : dcl c cC ofC)
        (E_EQ : E = contextC_to_context EC)
        (V_EQ : v = valueC_to_value vC),
        dec cC (opt_to_list ofC ++ EC) vC)
      (fun E v v0 (DCTX_EAM : EAM.decctx E v v0) => forall EC vC vC0
        (E_EQ : E = contextC_to_context EC)
        (V_EQ : v = valueC_to_value vC)
        (V_EQ0: v0 = valueC_to_value vC0),
        decctx EC vC vC0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); intros; simpl in *; subst...
    (* Case 1 *)
    destruct ofC; simpl in OK; cbv delta in DCL.
    rewrite OK in DCL; discriminate.
    simpl; subst c.
    assert (TO_C : proj1_sig (closure_red _ _ _ DCL CONTR) = proj1_sig (closure_red _ _ _ DCL CONTR)) by auto.
    destruct (closure_red _ _ _ DCL CONTR) as [[cC1 ofC1] UF] in TO_C at 2; simpl in *...
    (* Case 2 *)
    destruct ofC; cbv in OK; cbv delta in DCL.
    rewrite DCL in OK; discriminate.
    simpl; subst c.
    assert (TO_C : proj1_sig (closure_val _ _ DCL) = proj1_sig (closure_val _ _ DCL)); auto.
    destruct (closure_val _ _ DCL) as [vC1 UF] in TO_C at 2; simpl in *...
    (* Case 3 *)
    destruct ofC; cbv in OK; cbv delta in DCL; simpl.
    rewrite DCL in OK; inversion OK; subst; clear OK; simpl.
    cutrewrite (f0 :: EC0 = opt_to_list None ++ f0 :: EC0); auto.
    apply H0; simpl...
    subst.
    assert (hh := closureC_only_empty (cC0) c0 (f :: empty)); unfold only_empty in hh.
    assert (ht := dec_closure_correct (closureC_to_closure (cC0))); rewrite DCL in ht; simpl in *; apply hh in ht; discriminate.
    (* Case 4 *)
    apply valueC_to_value_injective in V_EQ0; cutrewrite (empty = contextC_to_context emptyC) in E_EQ; auto;
    apply contextC_to_context_injective in E_EQ; subst...
    (* Case 5 *)
    destruct EC0; inversion E_EQ; subst; clear E_EQ;
    assert (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = proj1_sig (context_red _ _ _ _ DCT CONTR)); auto.
    destruct (context_red _ _ _ _ DCT CONTR) as [[cC0 fC0] UF] in UNFOLD at 2; simpl in UNFOLD...
    (* Case 6 *)
    destruct EC0; inversion E_EQ; subst; clear E_EQ; 
    assert (UNFOLD : proj1_sig (context_val _ _ _ DCT) = proj1_sig (context_val _ _ _ DCT)); auto.
    destruct (context_val _ _ _ DCT) as [vC2 UF] in UNFOLD at 2; simpl in UNFOLD...
    (* Case 7 *)
    destruct EC0; inversion E_EQ; subst; clear E_EQ;
    assert (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = proj1_sig (context_clo _ _ _ _ DCT)); auto.
    destruct (context_clo _ _ _ _ DCT) as [[cC0 fC0] [UF0 UF1]] in UNFOLD at 2; simpl in UNFOLD. 
    subst; assert (H_UF := H0 cC0 None); simpl in *...
  Qed.
  
  Lemma decctxEamEamc : forall EC vC vC0,
    EAM.decctx (contextC_to_context EC) (valueC_to_value vC) (valueC_to_value vC0) ->
    decctx EC vC vC0.
  Proof with eauto using decEamEamc.
     intros; remember (contextC_to_context EC) as E;
      remember (valueC_to_value vC) as v; remember(valueC_to_value vC0) as v0;
        generalize dependent vC; generalize dependent vC0; generalize dependent EC;
        induction H; intros; destruct EC; inversion HeqE; subst; clear HeqE.
    apply valueC_to_value_injective in Heqv; subst...
    (* Red *)
    remember (context_red _ _ _ _ DCT CONTR) as ctr; 
      destruct ctr as [[cC0 ofC] DCL]; apply dc_red with _ _ _ _ DCT CONTR;
        try rewrite <- Heqctr; simpl; clear Heqctr; subst...
    destruct ofC; simpl in *; subst...
    inversion_clear DEC_C; cbv delta in DCL0; rewrite DCL0 in DCL; inversion DCL;
      subst...
    (* Val *)
    remember (context_val _ _ _ DCT) as ctv; destruct ctv as [vC1 EQV];
      apply dc_rec with _ _ DCT...
    rewrite <- Heqctv; simpl...
    (* Clo *)
    remember (context_clo _ _ _ _ DCT) as ctc; 
      destruct ctc as [[cC1 fC1] [EQC EQF]]; apply dc_clo with _ _ _ _ DCT; auto;
        try rewrite <- Heqctc; simpl; clear Heqctc; subst...
  Qed.

  Lemma evalEamEamc : forall t v, EAM.eval t (valueC_to_value v) -> eval t v.
  Proof.
    intros t v H; inversion_clear H; cutrewrite (pair t nil = closureC_to_closure (pairC t nil)) in H0; auto using decEamEamc.
    rewrite pairC_pair; auto.
  Qed.

  Lemma decEamcEam : forall cC EC vC (DEC_U : dec cC EC vC), EAM.dec (closureC_to_closure cC) (contextC_to_context EC) (valueC_to_value vC).
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun cC EC vC (DEC_U : dec cC EC vC) => EAM.dec (closureC_to_closure cC) (contextC_to_context EC) (valueC_to_value vC))
    (P0:= fun EC vC vC0 (DECC_U : decctx EC vC vC0) => EAM.decctx (contextC_to_context EC) (valueC_to_value vC) (valueC_to_value vC0))...
    (* Case 1 *)
    remember (closure_red _ _ cc DCL CONTR) as CL_R; destruct CL_R as [[cC0 ofC] UF]; simpl in *; inversion TO_C; subst; 
    clear TO_C HeqCL_R; econstructor...
    destruct ofc; simpl in *; try rewrite <- RS_RFL_CL in UF; subst...
    (* Case 2 *)
    remember (closure_val _ vv DCL) as CL_V; destruct CL_V as [vC0 UF]; clear HeqCL_V; simpl in *; subst...
    (* Case 3 *)
    remember (context_red _ _ r c DCT CONTR) as CT_R; destruct CT_R as [[cC0 ofC] UF]; inversion TO_C; clear HeqCT_R TO_C; 
    subst; econstructor...
    destruct ofc; simpl in *; try rewrite <- RS_RFL_CL in UF; subst...
    (* Case 4 *)
    remember (context_val _ _ _ DCT) as CT_V; destruct CT_V as [vC2 UF]; clear HeqCT_V; simpl in *; subst...
    (* Case 5 *)
    remember (context_clo _ _ c _ DCT) as CT_C; destruct CT_C as [[cC0 fC1] [UF0 UF1]]; inversion TO_C; clear TO_C HeqCT_C; subst;
    econstructor 4...
  Qed.

 Lemma decctxEamcEam : forall EC vC vC0
    (DEC : decctx EC vC vC0),
    EAM.decctx (contextC_to_context EC) (valueC_to_value vC)
      (valueC_to_value vC0).
  Proof with eauto using decEamcEam.
    induction 1...
    remember (context_red _ _ _ _ DCT CONTR) as CT_R; 
      destruct CT_R as [[cC0 ofC] DCL]; inversion TO_C;
        clear HeqCT_R TO_C; subst; econstructor...
    destruct ofc; simpl in *; subst...
    econstructor 3...
    change (EAM.dec (closureC_to_closure cC) 
      (contextC_to_context (f0 :: E)) (valueC_to_value v0))...
    remember (context_val _ _ _ DCT) as CT_V; destruct CT_V as [vC2 UF];
      clear HeqCT_V; simpl in *; subst...
    remember (context_clo _ _ c _ DCT) as CT_C;
      destruct CT_C as [[cC0 fC1] [UF0 UF1]]; inversion TO_C;
        clear TO_C HeqCT_C; subst; econstructor 4...
    change (EAM.dec (closureC_to_closure cC) (contextC_to_context (f0 :: E))
      (valueC_to_value v0))...
  Qed.

  Lemma evalEamcEam : forall t v, eval t v -> EAM.eval t (valueC_to_value v).
  Proof.
    intros t v H; inversion_clear H; constructor; cutrewrite (pair t nil = closureC_to_closure (pairC t nil));
    try cutrewrite (empty = contextC_to_context emptyC); auto using decEamcEam.
    rewrite pairC_pair; auto.
  Qed.

  Theorem evalUeam : forall t v, RS.RS.eval t (valueC_to_value v) <-> eval t v.
  Proof with auto.
    intros; rewrite EAM.evalEam; split; eauto using evalEamEamc, evalEamcEam.
  Qed.

  Lemma dec_val : forall E v v0, 
    dec (valueC_to_closureC v) E v0 <-> decctx E v v0.
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

  Definition dcl := dcl.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive dec : term -> envC -> contextC -> valueC -> Prop :=
  | d_r_t : forall t t0 sC sC0 EC front v r c cC
            (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
            (CONTR  : contract r = Some c)
            (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, front))
            (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t0, sC0))
            (DEC_C  : dec t0 sC0 (opt_to_list front ++ EC) v),
            dec t sC EC v
  | d_r_v : forall t sC EC front v v0 r c cC
            (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
            (CONTR  : contract r = Some c)
            (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, front))
            (UNFOLD : proj1_sig (closureC_dec cC) = inr _ v0)
            (DEC_C  : decctx (opt_to_list front ++ EC) v0 v),
            dec t sC EC v
  | d_v   : forall t sC EC v vC v0
            (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
            (TO_C   : proj1_sig (closure_val _ _ DCL) = vC)
            (DEC_E  : decctx EC vC v0),
            dec t sC EC v0
  with decctx : contextC -> valueC -> valueC -> Prop :=
  | dc_val : forall vC, decctx emptyC vC vC
  | dc_r_t : forall fC EC vC vC0 t sC front r c cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
             (CONTR  : contract r = Some c)
             (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, front))
             (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC))
             (DEC_C  : dec t sC (opt_to_list front ++ EC) vC0),
             decctx (fC :: EC) vC vC0
  | dc_r_v : forall fC EC vC vC0 vC1 front r c cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
             (CONTR  : contract r = Some c)
             (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, front))
             (UNFOLD : proj1_sig (closureC_dec cC) = inr _ vC1)
             (DEC_C  : decctx (opt_to_list front ++ EC) vC1 vC0),
             decctx (fC :: EC) vC vC0
  | dc_v   : forall fC EC vC vC0 vC1 v
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v)
             (TO_C   : proj1_sig (context_val _ _ _ DCT) = vC0)
             (DEC_E  : decctx EC vC0 vC1),
             decctx (fC :: EC) vC vC1
  | dc_c_t : forall fC fC0 EC vC vC0 t sC c f cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
             (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
             (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC))
             (DEC_C  : dec t sC (fC0 :: EC) vC0),
             decctx (fC :: EC) vC vC0             
  | dc_c_v : forall fC fC0 EC vC vC0 vC1 c f cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
             (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
             (UNFOLD : proj1_sig (closureC_dec cC) = inr _ vC1)
             (DEC_C  : decctx (fC0 :: EC) vC1 vC0),
             decctx (fC :: EC) vC vC0.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall t v, dec t nil emptyC v -> eval t v.

  Hint Constructors dec decctx eval.

  Lemma decEamUeam : forall t sC EC vC (DEC_EAM : EAMC.dec (pairC t sC) EC vC), dec t sC EC vC.
  Proof with eauto.
    intros; change (match inl valueC (t, sC) with
      | inl (t, s) => dec t s EC vC
      | inr v0 => decctx EC v0 vC
      end); rewrite <- dec_pairC.
    induction DEC_EAM using EAMC.dec_Ind with
    (P := fun c E v (DEC_EAM : EAMC.dec c E v) => match proj1_sig (closureC_dec c) with
      | inl (t, s) => dec t s E v
      | inr v0 => decctx E v0 v
      end)
    (P0:= fun E v v0 (DCTX_EAM : EAMC.decctx E v v0) => decctx E v v0)...
    (* Case 1 *)
    remember (closureC_dec c) as p.
    destruct p as [[[tt ssC] | vC] HH]; simpl in *.
    generalize dependent DCL; rewrite HH; intros.
    remember (proj1_sig (closureC_dec c0)) as qq; destruct qq as [[tr er] | vr].
    econstructor...
    econstructor 2...
    cbv delta in DCL; assert (ht := dec_closure_correct (closureC_to_closure c)); rewrite DCL in ht; simpl in ht.
    rewrite HH in ht; rewrite <- valueC_to_closure_commutes in ht; symmetry in ht; contradiction (value_redex _ _ ht).
    (* Case 2 *)
    remember (closureC_dec c) as p.
    destruct p as [[[tt ssC] | vC] HH]; simpl in *.
    generalize dependent DCL; rewrite HH; intros.
    econstructor 3...
    cbv delta in DCL; assert (ht := dec_closure_correct (closureC_to_closure c)); rewrite DCL in ht; simpl in ht.
    rewrite HH in ht; rewrite <- valueC_to_closure_commutes in ht; symmetry in ht.
    apply value_to_closure_injective in ht.
    remember (EAMC.closure_val _ _ DCL) as qq; destruct qq as [vT HT]; simpl in TO_C.
    rewrite HT in ht; apply valueC_to_value_injective in ht; subst vT; subst v...
    (* Case 3 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; simpl in *;
    [econstructor | econstructor 3]...
    rewrite <- Heqqq; simpl; reflexivity.
    rewrite <- Heqqq; simpl; reflexivity.
    (* Case 4 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; simpl in *;
    [econstructor 5 | econstructor 6]...
    rewrite <- Heqqq; simpl; reflexivity.
    rewrite <- Heqqq; simpl; reflexivity.
  Qed.

  Lemma evalEamUeam : forall t v, EAMC.eval t v -> eval t v.
  Proof.
    intros t v H; inversion_clear H; auto using decEamUeam.
  Qed.

  Lemma decUeamEam : forall t sC EC vC (DEC_U : dec t sC EC vC), EAMC.dec (pairC t sC) EC vC.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun t sC EC vC (DEC_U : dec t sC EC vC) => EAMC.dec (pairC t sC) EC vC)
    (P0:= fun EC vC vC0 (DECC_U : decctx EC vC vC0) => EAMC.decctx EC vC vC0)...
    (* Case 1 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNFOLD; econstructor... 
    rewrite HH; subst tt ss...
    (* Case 2 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNFOLD; econstructor...
    rewrite HH; subst vv...
    rewrite EAMC.dec_val...
    (* Case 3 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNFOLD; econstructor...
    rewrite HH; subst tt ss...
    (* Case 4 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNFOLD; econstructor...
    rewrite HH; subst vv...
    rewrite EAMC.dec_val...
    (* Case 5 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNFOLD; econstructor 4...
    rewrite HH; subst tt ss...
    (* Case 6 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH];
      simpl in *; inversion UNFOLD; econstructor 4...
    rewrite HH; subst vv...
    rewrite EAMC.dec_val...
   Qed.

  Lemma evalUeamEam : forall t v, eval t v -> EAMC.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; auto using decUeamEam.
  Qed.

  Theorem evalUeam : forall t v, RS.RS.eval t (valueC_to_value v) <-> eval t v.
  Proof with auto.
    intros; rewrite EAMC.evalUeam; split; eauto using evalEamUeam, evalUeamEam.
  Qed.

End UnfoldedEAMachine.

Module ProperEAMachine (Lang : RED_LANG) (SEM : RED_REF_SEM Lang) <: PROPER_EA_MACHINE Lang.

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

  Definition dcl := dcl.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> envC -> contextC -> configuration
  | c_apply : contextC -> valueC -> configuration
  | c_final : valueC -> configuration.
  Notation " <<i t >> " := (c_init t) : eam_scope.
  Notation " << t , s , E >> " := (c_eval t s E) : eam_scope.
  Notation " << E , v >> " := (c_apply E v) : eam_scope.
  Notation " <<f v >> " := (c_final v) : eam_scope.
  Open Scope red_scope.
  Open Scope eam_scope.

  Reserved Notation " a → b " (at level 40, no associativity).
  
(*  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t, <<i t >> → << t, nil, emptyC >>
  | t_red  : forall t t0 sC sC0 E ofC r c
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (closure_red _ _ _ DCL CONTR) = (t0, sC0, ofC)),
               << t, sC, E>> → << t0, sC0, opt_to_list ofC × E >>
  | t_val  : forall t sC E v vC
  	       (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNFOLD : proj1_sig (closure_val _ _ DCL) = vC),
               << t, sC, E >> → << E, vC >>
  | t_cfin : forall v, << emptyC, v >> → <<f v >>
  | t_cred : forall f v r c t sC ofC E
               (DCT    : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = (t, sC, ofC)),
               << f :: E, v >> → << t, sC, opt_to_list ofC × E >>
  | t_cval : forall vC vC0 fC v0 E
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v0)
               (UNFOLD : proj1_sig (context_val _ _ _ DCT) = vC0),
               << fC :: E, vC >> → << E, vC0 >>
  | t_cterm: forall fC fC0 vC t sC c f E
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = (t, sC, fC0)),
               << fC :: E, vC >> → << t, sC, fC0 :: E >>
  where " a → b " := (transition a b).*)

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t, <<i t >> → << t, nil, emptyC >>
  | t_redt : forall t t0 sC sC0 E ofC r c cC
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t0, sC0)),
               << t, sC, E>> → << t0, sC0, opt_to_list ofC × E >>
  | t_redv : forall t sC E ofC r c cC v
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inr _ v),
               << t, sC, E>> → << opt_to_list ofC × E, v >>
  | t_val  : forall t sC E v vC
  	       (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (TO_C   : proj1_sig (closure_val _ _ DCL) = vC),
               << t, sC, E >> → << E, vC >>
  | t_cfin : forall v, << emptyC, v >> → <<f v >>
  | t_credt: forall f v r c t sC ofC E cC
               (DCT    : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
               << f :: E, v >> → << t, sC, opt_to_list ofC × E >>
  | t_credv: forall f v v0 r c ofC E cC
               (DCT    : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inr _ v0),
               << f :: E, v >> → << opt_to_list ofC × E, v0 >>
  | t_cval : forall vC vC0 fC v0 E
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v0)
               (TO_C   : proj1_sig (context_val _ _ _ DCT) = vC0),
               << fC :: E, vC >> → << E, vC0 >>
  | t_cct  : forall fC fC0 vC t sC c f E cC
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
               (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
               << fC :: E, vC >> → << t, sC, fC0 :: E >>
  | t_ccv  : forall fC fC0 vC vC0 c f E cC
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
               (UNFOLD : proj1_sig (closureC_dec cC) = inr _ vC0),
               << fC :: E, vC >> → << fC0 :: E, vC0 >>
  where " a → b " := (transition a b).

  Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := valueC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := term.
    Definition value := valueC.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.

    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
    | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).
  Hint Constructors transition AM.trans_close AM.eval.
  Hint Unfold AM.transition.

  Lemma decEamTrans : forall t sC EC vC (DEC : UEAM.dec t sC EC vC),
    << t, sC, EC >> →+ <<f vC >>.
  Proof with eauto.
    induction 1 using UEAM.dec_Ind with
    (P := fun t sC EC vC (DEC : UEAM.dec t sC EC vC) => << t, sC, EC >> →+ <<f vC >>)
    (P0:= fun EC vC vC0 (DEC_E : UEAM.decctx EC vC vC0) =>  << EC, vC >> →+ <<f vC0 >>); eauto;
    (econstructor 2; [idtac | eauto]; econstructor)...
  Qed.
  Hint Resolve decEamTrans.

  Lemma evalEamMachine : forall t v, UEAM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H...
  Qed.
  Hint Resolve evalEamMachine.

  Lemma transDecEam : forall t sC EC vC (TRAN_CL : << t, sC, EC >> →+ <<f vC >>), UEAM.dec t sC EC vC.
  Proof with eauto.
    intros; refine (AM.trans_close_ind
    (fun c c0 =>match c, c0 with
      | << t, sC, EC >>, <<f vC >> => UEAM.dec t sC EC vC
      | << EC, vC >>, <<f vC0 >>   => UEAM.decctx EC vC vC0
      | _, _ => True
    end)
    _ _ _ _ TRAN_CL); intros; auto.
    (* Case 1 *)
    generalize H; clear H; case c0; case c1; simpl; intros; try inversion t2; subst; auto;
    inversion_clear H; constructor 1; auto.
    (* Case 2 *)
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl; auto; intros; inversion H; subst...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecEam.

  Lemma evalMachineEam : forall t v, AM.eval t v -> UEAM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor; inversion_clear H0; inversion H; subst...
  Qed.
  Hint Resolve evalMachineEam.

  Theorem eval_apply_correct : forall t v, RS.eval t (valueC_to_value v) <-> AM.eval t v.
  Proof with auto.
    intros t v; rewrite UEAM.evalUeam; split...
  Qed.

  Close Scope eam_scope.
  Close Scope red_scope.

End ProperEAMachine.

Module PushEnterMachine (Lang : RED_LANG) (Sem : PE_REF_SEM Lang) <: PUSH_ENTER_MACHINE Lang.

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

  Definition dcl := dcl.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Open Scope red_scope.

(*  Inductive dec : term -> envC -> contextC -> valueC -> Prop :=
  | dec_r    : forall t t0 sC sC0 ofC E r c v
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
                 (CONTR  : contract r = Some c)
                 (UNFOLD : proj1_sig (closure_red _ _ _ DCL CONTR) = (t0, sC0, ofC))
                 (DEC    : dec t0 sC0 (opt_to_list ofC × E) v),
                 dec t sC E v
  | dec_val  : forall t sC v vC
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNFOLD : proj1_sig (closure_val _ _ DCL) = vC),
                 dec t sC emptyC vC
  | dec_v_r  : forall t t0 sC sC0 E ofC fC vC vC0 v r c
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
                 (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
                 (CONTR  : contract r = Some c)
                 (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = (t0, sC0, ofC))
                 (DEC    : dec t0 sC0 (opt_to_list ofC × E) vC0),
                 dec t sC (fC :: E) vC0
  | dec_v_c  : forall t t0 sC sC0 vC vC0 fC fC0 E v c f
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
                 (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
                 (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = (t0, sC0, fC0))
                 (DEC    : dec t0 sC0 (fC0 :: E) vC0),
                 dec t sC (fC :: E) vC0.*)

  Inductive dec : term -> envC -> contextC -> valueC -> Prop :=
  | dec_r    : forall t t0 sC sC0 ofC E r c v
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
                 (CONTR  : contract r = Some c)
                 (UNFOLD : proj1_sig (closure_red _ _ _ DCL CONTR) = (pairC t0 sC0, ofC))
                 (DEC    : dec t0 sC0 (opt_to_list ofC × E) v),
                 dec t sC E v
  | dec_val  : forall t sC v vC
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNFOLD : proj1_sig (closure_val _ _ DCL) = vC),
                 dec t sC emptyC vC
  | dec_v_r  : forall t t0 sC sC0 E ofC fC vC vC0 v r c
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
                 (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
                 (CONTR  : contract r = Some c)
                 (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = (pairC t0 sC0, ofC))
                 (DEC    : dec t0 sC0 (opt_to_list ofC × E) vC0),
                 dec t sC (fC :: E) vC0
  | dec_v_c  : forall t t0 sC sC0 vC vC0 fC fC0 E v c f
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
                 (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
                 (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0))
                 (DEC    : dec t0 sC0 (fC0 :: E) vC0),
                 dec t sC (fC :: E) vC0.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall t v, dec t nil emptyC v -> eval t v.

  Hint Constructors dec eval.

  Lemma decUeamPem : forall t sC EC vC (DEC_U : UEAM.dec t sC EC vC), dec t sC EC vC.
  Proof with eauto.
    induction 1 using UEAM.dec_Ind with
    (P := fun t sC EC vC (DEC_C : UEAM.dec t sC EC vC) => dec t sC EC vC)
    (P0:= fun EC vC vC0 (DEC_E : UEAM.decctx EC vC vC0) =>
      match EC with
      | nil => vC = vC0
      | (fC :: EC0) => forall int (DECT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = int),
        match int with
        | in_red r => forall c t0 sC0 ofC
            (DCT0 : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
            (CONTR : contract r = Some c)
            (UNFOLD : proj1_sig (context_red _ _ _ _ DCT0 CONTR) = (pairC t0 sC0, ofC)),
            dec t0 sC0 (opt_to_list ofC × EC0) vC0
        | in_clo c fc => forall t0 sC0 fC0
            (DCT0 : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c fc)
            (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT0) = (pairC t0 sC0, fC0)),
            dec t0 sC0 (fC0 :: EC0) vC0
        | in_val v => False
        end
      end); intros; simpl...
    (* Case 1 *)
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; simpl in *;
    generalize dependent DCL; rewrite HH; intros; inversion UNFOLD; subst tt ss...
    (* Case 2 *)
    contradiction (closureC_dec_not_right _ _ UNFOLD).
    (* Case 3 *)
    destruct EC; simpl in *; subst; simpl in *...
    inversion DEC_E; subst; simpl in *;
    remember (proj1_sig (UEAM.closure_val (pairC t sC) v DCL)) as vC; symmetry in HeqvC;
    cbv delta in DCT; unfold dec_context in IHDEC_U; assert (HDEC_U := IHDEC_U _ DCT); simpl in *...
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; simpl in *;
    generalize dependent DCT; rewrite HH; intros; inversion UNFOLD; subst tt ss...
    contradiction (closureC_dec_not_right _ _ UNFOLD).
    contradiction (dec_context_not_val _ _ _ DCT).
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] HH]; simpl in *;
    generalize dependent DCT; rewrite HH; intros; inversion UNFOLD; subst tt ss...
    contradiction (closureC_dec_not_right _ _ UNFOLD).
    (* Case 4 *)
    destruct int; intros; simpl in *...
    cbv delta in DCT; cbv delta in DECT; rewrite DCT in DECT; inversion DECT; subst; clear DECT.
    destruct (UEAM.context_red fC vC r0 c DCT CONTR); destruct (context_red fC vC r0 c0 DCT0 CONTR0);
    simpl in *; rewrite CONTR in CONTR0; inversion CONTR0; subst; clear CONTR0;
    destruct front; destruct ofC; simpl in *.
    rewrite y0 in y; inversion y.
    apply closureC_to_closure_injective in H0; apply frameC_to_frame_injective in H1;
    rewrite <- H0 in UNFOLD; rewrite dec_pairC in UNFOLD; inversion UNFOLD; subst...
    subst c0.
    assert (RED := dec_closure_correct (closureC_to_closure (pairC t0 sC0))).
    rewrite y in RED; simpl in RED.
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] QQ]; simpl in *;
    inversion UNFOLD; subst tt ss; clear Heqqq; subst cC.
    assert (HH := closureC_only_empty (pairC t0 sC0) (closureC_to_closure (pairC t sC)) (frameC_to_frame f :: empty));
    simpl in HH; apply HH in RED; discriminate.
    subst c0.
    assert (RED := dec_closure_correct (closureC_to_closure (pairC t sC))).
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] QQ]; simpl in *;
    inversion UNFOLD; subst tt ss; clear Heqqq; subst cC.
    rewrite y0 in RED; simpl in RED.
    assert (HH := closureC_only_empty (pairC t sC) (closureC_to_closure (pairC t0 sC0)) (frameC_to_frame f :: empty));
    simpl in HH; apply HH in RED; discriminate.
    subst c0; apply closureC_to_closure_injective in y0;
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] QQ]; simpl in *;
    inversion UNFOLD; subst tt ss; clear Heqqq; subst cC.
    apply pairC_injective in QQ; inversion QQ; subst...
    contradiction (dec_context_not_val _ _ _ DECT).
    cbv delta in DCT; cbv delta in DECT; rewrite DCT in DECT; discriminate.
    (* Case 5 *)
    contradiction (closureC_dec_not_right _ _ UNFOLD).
    (* Case 6 *)
    contradiction (dec_context_not_val _ _ _ DCT).
    (* Case 7 *)
    destruct int; intros; simpl in *.
    cbv delta in DCT; cbv delta in DECT; rewrite DCT in DECT; discriminate.
    contradiction (dec_context_not_val _ _ _ DECT).
    cbv delta in DCT; cbv delta in DECT; rewrite DCT in DECT; inversion DECT; 
    destruct (context_clo fC vC c0 f0 DCT0); destruct (UEAM.context_clo fC vC c f DCT);
    simpl in *; subst; clear DECT.
    destruct y; destruct y0; subst; apply frameC_to_frame_injective in H2; apply closureC_to_closure_injective in H1;
    remember (closureC_dec cC) as qq; destruct qq as [[[tt ss] | vv] QQ]; simpl in *;
    inversion UNFOLD; subst tt ss; clear Heqqq; subst cC; apply pairC_injective in QQ; inversion QQ; subst...
    (* Case 8 *)
    contradiction (closureC_dec_not_right _ _ UNFOLD).
  Qed.

  Lemma evalUeamPem : forall t v, UEAM.eval t v -> eval t v.
  Proof.
    intros t v H; inversion_clear H; auto using decUeamPem.
  Qed.

  Lemma decPemUeam : forall t sC EC vC (DEC : dec t sC EC vC), UEAM.dec t sC EC vC.
  Proof with eauto using dec_pairC.
    induction 1 using dec_Ind...
  Qed.

  Lemma evalPemUeam : forall t v, eval t v -> UEAM.eval t v.
  Proof.
    intros t v H; inversion_clear H; auto using decPemUeam.
  Qed.

  Theorem evalPem : forall t v, RS.eval t (valueC_to_value v) <-> eval t v.
  Proof.
    intros t v; rewrite UEAM.evalUeam; split; auto using evalUeamPem, evalPemUeam.
  Qed.

End PushEnterMachine.

Module ProperPEMachine (Lang : RED_LANG) (Sem : PE_REF_SEM Lang) <: PROPER_PE_MACHINE Lang.

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

  Definition dcl := dcl.
  Definition closure_red := closure_red.
  Definition closure_val := closure_val.
  Definition context_red := context_red.
  Definition context_val := context_val.
  Definition context_clo := context_clo.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> envC -> contextC -> configuration
  | c_final : valueC -> configuration.

  Notation " <<i t >> " := (c_init t) : pem_scope.
  Notation " << t , s , E >> " := (c_eval t s E) : pem_scope.
  Notation " <<f v >> " := (c_final v) : pem_scope.

  Open Scope red_scope.
  Open Scope pem_scope.

  Reserved Notation " a → b " (at level 40, no associativity).

(*  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t, <<i t >> → << t, nil, emptyC >>
  | t_red  : forall t t0 sC sC0 ofC E r c
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (closure_red _ _ _ DCL CONTR) = (t0, sC0, ofC)),
               << t, sC, E >> → << t0, sC0, opt_to_list ofC × E >>
  | t_cval : forall t sC v vC
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNFOLD : proj1_sig (closure_val _ _ DCL) = vC),
               << t, sC, emptyC >> → <<f vC >>
  | t_cred : forall t t0 sC sC0 fC ofC E vC v r c
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = (t0, sC0, ofC)),
               << t, sC, fC :: E >> → << t0, sC0, opt_to_list ofC × E >>
  | t_crec : forall t t0 sC sC0 fC fC0 E vC v c f
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = (t0, sC0, fC0)),
               << t, sC, fC :: E >> → << t0, sC0, fC0 :: E >>
  where " c → c0 " := (transition c c0).*)
  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t, <<i t >> → << t, nil, emptyC >>
  | t_red  : forall t t0 sC sC0 ofC E r c
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (closure_red _ _ _ DCL CONTR) = (pairC t0 sC0, ofC)),
               << t, sC, E >> → << t0, sC0, opt_to_list ofC × E >>
  | t_cval : forall t sC v vC
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNFOLD : proj1_sig (closure_val _ _ DCL) = vC),
               << t, sC, emptyC >> → <<f vC >>
  | t_cred : forall t t0 sC sC0 fC ofC E vC v r c
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = (pairC t0 sC0, ofC)),
               << t, sC, fC :: E >> → << t0, sC0, opt_to_list ofC × E >>
  | t_crec : forall t t0 sC sC0 fC fC0 E vC v c f
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0)),
               << t, sC, fC :: E >> → << t0, sC0, fC0 :: E >>
  where " c → c0 " := (transition c c0).

    Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := valueC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := term.
    Definition value := valueC.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.

    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
    | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall t v (TCL : trans_close (c_init t) (c_final v)), eval t v.

  End AM.

  Hint Constructors transition AM.trans_close AM.eval.
  Hint Unfold AM.transition.
  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).

  Lemma decPemTrans : forall t sC EC vC (DEC : PEM.dec t sC EC vC),
    << t, sC, EC >> →+ <<f vC >>.
  Proof with eauto.
    induction 1; eauto; (econstructor 2; [idtac | eauto]); eauto.
  Qed.
  Hint Resolve decPemTrans.

  Lemma evalPemMachine : forall t v, PEM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H...
  Qed.
  Hint Resolve evalPemMachine.

  Lemma transDecPem : forall t sC EC vC (TCL : << t, sC, EC >> →+ <<f vC >>), PEM.dec t sC EC vC.
  Proof with eauto.
    intros t sC EC vC TCL; refine (AM.trans_close_ind
    (fun c c0 => match c, c0 with
      | << t, sC, EC >>, <<f vC >> => PEM.dec t sC EC vC
      | _, _ => True
    end) _ _ _ _ TCL); intros...
    generalize H; clear H; case c0; case c1; simpl; intros; try inversion t2; subst; auto; inversion_clear H; econstructor 2...
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl; auto; intros; inversion H; subst...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecPem.

  Lemma evalMachinePem : forall t v, AM.eval t v -> PEM.eval t v.
  Proof.
    intros t v H; constructor; inversion_clear H; inversion H0; subst; inversion H; subst; auto.
  Qed.
  Hint Resolve evalMachinePem.

  Theorem push_enter_correct : forall t v, RS.eval t (valueC_to_value v) <-> AM.eval t v.
  Proof.
    intros t v; rewrite (PEM.evalPem); split; auto.
  Qed.

End ProperPEMachine.
