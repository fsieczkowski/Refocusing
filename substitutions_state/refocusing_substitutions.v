Require Import Setoid.
Require Export refocusing_signatures.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.

Module Lang_Prop (R : RED_LANG) : LANG_PROP R.

  Import R.
  Open Scope red_scope.

  Lemma plug_empty : forall t, [] [ t ] = t.
  Proof.
    intros; simpl; auto.
  Qed.
  Hint Resolve plug_empty : prop.

  Lemma compose_empty : forall E, E = E · [].
  Proof.
    apply app_nil_end.
  Qed.
  Hint Resolve compose_empty : prop.

  Lemma plug_compose : forall E E0 t, E · E0 [ t ] = E0 [ E [ t ] ].
  Proof.
    apply fold_left_app.
  Qed.
  Hint Resolve plug_compose : prop.

  Close Scope red_scope.

End Lang_Prop.

Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.R.

  Module P := Lang_Prop R.R.
  Import P.
  Import R.R.
  Import R.

  Definition dec_term    := dec_term.
  Definition dec_context := dec_context.
  Inductive dec : term -> context -> decomp -> Prop :=
  | d_dec  : forall t E r
               (DT  : dec_term t = in_red r),
               dec t E (d_red r E)
  | d_v    : forall t E v d
               (DT  : dec_term t = in_val v)
               (R_C : decctx v E d),
               dec t E d
  | d_term : forall t t0 E f d
               (DT  : dec_term t = in_term t0 f)
               (R_T : dec t0 (f :: E) d),
               dec t E d
  with decctx : value -> context -> decomp -> Prop :=
  | dc_end  : forall v, decctx v [] (d_val v)
  | dc_dec  : forall v f E r
                (DC  : dec_context f v = in_red r),
                decctx v (f :: E) (d_red r E)
  | dc_val  : forall v v0 f E d
                (DC  : dec_context f v = in_val v0)
                (R_C : decctx v0 E d),
                decctx v (f :: E) d
  | dc_term : forall v f f0 E t d
                (DC  : dec_context f v = in_term t f0)
                (R_T : dec t (f0 :: E) d),
                decctx v (f :: E) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
    
  Notation " a <| b " := (subterm_order a b) (at level 40).
  Notation " a <: b " := (frame_order a b) (at level 40).

  Lemma sto_trans : forall t t0 t1, t <| t0 -> t0 <| t1 -> t <| t1.
  Proof with auto.
    induction 2; econstructor 2; eauto.
  Qed.

  Lemma plug_le_eq : forall E t t0, E [ t0 ] = t ->
    t0 <| t \/ (E = [] /\ t = t0).
  Proof with auto.
    induction E; intros; simpl in *; auto.
    left; destruct (IHE _ _ H) as [H0 | [H1 H0]]; clear IHE;
      [eapply sto_trans |]; unfold subterm_order;
        eauto using subterm_one_step, clos_trans_n1.
  Qed.

  Lemma st_c : forall t0 t1, t0 <| t1 -> exists E, E [t0] = t1.
  Proof with auto.
    intros; induction H; inversion H; subst.
    exists (f :: nil); simpl; auto.
    destruct IHclos_trans_n1 as [E H1].
    exists (E · (f :: nil)); rewrite plug_compose; simpl; subst...
  Qed.

  Definition value_one_step v v0 :=
    subterm_one_step (value_to_term v) (value_to_term v0).
  Definition value_order := clos_trans_n1 _ value_one_step.
    
  Notation " a <v| b " := (value_order a b) (at level 40).
    
  Lemma wf_vo : well_founded value_order.
  Proof.
    apply wf_clos_trans_r; apply wf_inverse_image; apply R.wf_st1.
  Qed.

  Lemma dec_val : forall v E d
    (HD : dec (value_to_term v) E d),
    decctx v E d.
  Proof with eauto.
    induction v as [? HInd] using (well_founded_ind wf_vo); intros.
    remember (R.dec_term (value_to_term v)) as id;
      assert (hh := dec_term_correct (value_to_term v));
        destruct id; rewrite <- Heqid in hh; symmetry in hh.
    (* red *)
    contradiction (value_redex hh).
    (* val *)
    apply value_to_term_injective in hh; inversion HD; subst;
      unfold dec_term in DT; rewrite DT in Heqid; inversion Heqid; subst...
    (* term *)
    edestruct (@value_trivial v t (f :: nil)) as [HV | [v0 HT]]; simpl;
      [rewrite hh; reflexivity | discriminate | subst].
    assert (ht := tn1_step _ value_one_step _ _ (st_1 hh));
      change (v0 <v| v) in ht.
    inversion HD; subst; unfold dec_term in DT; rewrite DT in Heqid;
      inversion Heqid; subst; clear HD Heqid DT.
    assert (HDC := HInd _ ht _ _ R_T); clear ht R_T.
    generalize dependent v0.
    induction f0 as [? HIndC] using (well_founded_ind wf_eco); intros.
    remember (R.dec_context f0 v0) as id;
      assert (hc := dec_context_correct f0 v0); destruct id;
        rewrite <- Heqid in hc; rewrite <- hh in hc; symmetry in hc.
    (* - red *)
    contradiction (value_redex hc).
    (* - val *)
    apply value_to_term_injective in hc; subst; clear HIndC HInd.
    inversion HDC; subst; unfold dec_context in DC; rewrite DC in Heqid;
      inversion Heqid; subst...
    (* - term *)
    destruct (@value_trivial v t (f :: nil)) as [HD | [v1 HT]]; simpl;
      [rewrite hc; reflexivity | discriminate | subst].
    inversion HDC; subst; unfold dec_context in DC; rewrite DC in Heqid;
      inversion Heqid; subst; clear Heqid HDC.
    apply HIndC with f2 v1; [destruct (dec_context_term_next DC) | |]...
    apply HInd; unfold value_order, value_one_step;
      eauto using clos_trans_n1, subterm_one_step.
  Qed.

  Lemma val_dec : forall v c d
    (HDC : decctx v c d),
    dec (R.R.value_to_term v) c d.
  Proof with eauto using clos_trans_n1, subterm_one_step.
    induction v as [? HIndV] using (well_founded_ind wf_vo); intros.
    remember (R.dec_term (value_to_term v)) as id;
      assert (hh := dec_term_correct (value_to_term v));
        destruct id; rewrite <- Heqid in hh; symmetry in hh.
    (* red *)
    contradiction (value_redex hh).
    (* val *)
    apply value_to_term_injective in hh; subst; eapply d_v...
    (* term *)
    destruct (@value_trivial v t (f :: nil)) as [HD | [v0 HT]]; simpl;
      [ rewrite hh; reflexivity | discriminate | subst; eapply d_term ]...
    apply HIndV; [unfold value_order, value_one_step | clear Heqid]...
    generalize dependent v0; induction f as [? HIndC] using
      (well_founded_ind wf_eco); intros.
    remember (R.dec_context f v0) as id; assert (hc:= dec_context_correct f v0);
      destruct id; rewrite <- Heqid in hc; rewrite <- hh in hc; symmetry in hc.
    (* - red *)
    contradiction (value_redex hc).
    (* - val *)
    clear HIndV HIndC; apply value_to_term_injective in hc; subst;
      eapply dc_val...
    (* - term *)
    destruct (@value_trivial v t (f0 :: nil)) as [HD | [v1 HT]]; simpl;
      [rewrite hc; reflexivity | discriminate | subst; eapply dc_term]...
    apply HIndV; [unfold value_order, value_one_step |]...
    apply HIndC; [| assumption].
    symmetry in Heqid; destruct (dec_context_term_next Heqid)...
  Qed.

  Module RS : RED_SEM R.R with Definition dec := dec.
    Definition dec := dec.
    Module P := P.

    Lemma decompose : forall t, (exists v, t = value_to_term v) \/
      (exists r, exists E, E [ redex_to_term r ] = t).
    Proof with eauto using clos_trans_n1, subterm_one_step.
      induction t as [? HInd] using (well_founded_ind wf_sto); intros.
      remember (R.dec_term t) as id; assert (hh := dec_term_correct t);
        destruct id; rewrite <- Heqid in hh.
      (* red *)
      right; exists r; exists []; assumption.
      (* val *)
      left; exists v; symmetry; assumption.
      (* term *)
      destruct (HInd t0) as [[v Hv] | [r [c Hrc]]];
        [unfold subterm_order | subst t0 |]...
      (* - val *)
      clear Heqid; generalize dependent v; induction f as [? HIndC]
        using (well_founded_ind wf_eco); intros; subst.
      remember (R.dec_context f v) as id; assert (ht:= dec_context_correct f v);
        destruct id; rewrite <- Heqid in ht.
      (* -- red *)
      right; exists r; exists []; assumption.
      (* -- val *)
      left; exists v0; symmetry; assumption.
      (* -- term *)
      destruct (HInd t) as [[v0 Hv] | [r [c Hrc]]];
        [unfold subterm_order | subst |]...
      (* --- val *)
      symmetry in Heqid; destruct (dec_context_term_next Heqid) as [HLeF _].
      destruct (HIndC _ HLeF v0 ht) as [[v1 Hv1] | [r [E HRE]]]...
      (* --- red *)
      right; exists r; exists (c · (f0 :: nil)); rewrite plug_compose; subst...
      (* - red *)
      right; exists r; exists (c · (f :: nil)); rewrite plug_compose; subst...
    Qed.

    Lemma dec_redex_self_e : forall r, dec (redex_to_term r) [] (d_red r []).
    Proof with eauto.
      intros; remember (dec_term (redex_to_term r)) as id; destruct id;
        assert (hh := dec_term_correct (redex_to_term r));
          unfold dec_term in Heqid; rewrite <- Heqid in hh; simpl in hh.
      (* red *)
      apply redex_to_term_injective in hh; subst; apply d_dec...
      (* val *)
      contradiction (value_redex hh).
      (* term *)
      symmetry in Heqid; assert (HF:= dec_term_term_top Heqid); eapply d_term...
      destruct (@redex_trivial _ _ (f :: []) hh) as [H1 | [v H1]];
        [ discriminate | subst t]; clear HF Heqid.
      generalize dependent v; revert f; induction f as [? HInd]
        using (well_founded_ind R.wf_eco); intros.
      apply val_dec.
      remember (R.dec_context f v) as id;
        assert (ht := dec_context_correct f v); rewrite <- Heqid in ht;
          destruct id; simpl in ht; rewrite hh in ht.
      (* - red *)
      apply redex_to_term_injective in ht; subst; apply dc_dec...
      (* - val *)
      contradiction (value_redex ht).
      (* - term *)
      eapply dc_term...
      destruct (@redex_trivial r t (f0 :: []) ht) as [H4 | [v1 H4]];
        [ discriminate | subst ].
      symmetry in Heqid; destruct (dec_context_term_next Heqid); apply HInd...
    Qed.

    Lemma dec_redex_self : forall r E, dec (redex_to_term r) E (d_red r E).
    Proof with eauto.
      intros; assert (hh := dec_redex_self_e r).
      induction hh using dec_Ind with
        (P := fun t E0 d (HDec : dec t E0 d) =>
          match d with
            | d_val v => True
            | d_red r' E1 => dec t (E0 · E) (d_red r' (E1 · E))
          end)
        (P0:= fun v E0 d (HDecE : decctx v E0 d) =>
          match d with
            | d_val v => True
            | d_red r' E1 => decctx v (E0 · E) (d_red r' (E1 · E))
          end); try destruct d; auto;
        [ apply d_dec | eapply d_v | eapply d_term |
          apply dc_dec | eapply dc_val | eapply dc_term ]...
    Qed.

    Lemma dec_correct : forall t E d, dec t E d -> decomp_to_term d = E [ t ].
    Proof.
      induction 1 using dec_Ind with
        (P := fun t E d (HDec : dec t E d) => decomp_to_term d = E [ t ])
        (P0:= fun v E d (HDecE : decctx v E d) =>
          decomp_to_term d = E [ value_to_term v ]);
        simpl; auto;
          match goal with
            | [ DT: (dec_term ?t = ?int) |- _ ] => unfold dec_term in DT;
              assert (hh := R.dec_term_correct t); rewrite DT in hh
            | [ DC: (dec_context ?ec ?v = ?int) |- _ ] =>
              unfold dec_context in DC;
                assert (hh := R.dec_context_correct ec v); rewrite DC in hh
          end; try rewrite IHdec; rewrite <- hh; subst; auto.
    Qed.

    Lemma dec_plug_rev : forall E E0 t d
      (HDEC : dec t (E · E0) d),
      dec (E [ t ]) E0 d.
    Proof with auto.
      induction E; intros; simpl; auto.
      apply IHE; clear IHE; remember (R.dec_term (a a[ t ])) as id; destruct id;
        assert (hh := dec_term_correct (a a[t])); rewrite <- Heqid in hh;
          symmetry in Heqid.
      (* red *)
      discriminate (dec_term_red_empty Heqid) with t (a :: []); reflexivity.
      (* val *)
      discriminate (dec_term_val_empty Heqid) with t (a :: nil); reflexivity.
      (* term *)
      destruct (dec_ec_ord hh) as [HLeF | [HLeF | [H0 H1]]];
        [contradiction (dec_term_term_top Heqid HLeF) | |
          subst; eapply d_term; eauto].
      symmetry in hh; destruct (elem_context_det HLeF hh) as [v HT]; subst t0;
        eapply d_term; eauto.
      clear Heqid; generalize dependent v; generalize dependent f.
      induction f as [? HInd] using (well_founded_ind wf_eco); intros;
        apply val_dec.
      remember (R.dec_context f v) as id; destruct id; symmetry in Heqid;
        assert (ht := dec_context_correct f v); rewrite Heqid in ht.
      (* red *)
      contradiction (dec_context_red_bot Heqid) with a.
      (* val *)
      contradiction (dec_context_val_bot Heqid) with a.
      (* term *)
      destruct (dec_context_term_next Heqid) as [HLeF0 HLeT].
      eapply dc_term; eauto; rewrite <- hh in ht.
      destruct (dec_ec_ord ht) as [H4 | [H4 | [H4 H5]]];
        try (subst; auto; fail).
      contradiction (HLeT _ HLeF).
      symmetry in ht; clear HLeT; destruct (elem_context_det H4 ht) as [v0 H5];
        subst t0; apply HInd; auto.
    Qed.

    Lemma dec_plug : forall E E0 t d
      (HDec : dec (E [ t ]) E0 d),
      dec t (E · E0) d.
    Proof with auto.
      induction E; intros; simpl; auto.
      apply IHE in HDec; clear IHE; inversion HDec; subst;
        assert (hh := R.dec_term_correct (R.R.atom_plug t a));
          unfold dec_term in DT; clear HDec; rewrite DT in hh;
            symmetry in hh.
      (* red *)
      discriminate (dec_term_red_empty DT) with t (a :: []); reflexivity.
      (* val *)
      discriminate (dec_term_val_empty DT) with t (a :: []); reflexivity.
      (* term *)
      destruct (dec_ec_ord hh) as [H2 | [H2 | [H2 H3]]];
        [| contradiction (dec_term_term_top DT) with a | subst; assumption].
      destruct (elem_context_det H2 hh) as [v H3]; subst t1.
      clear DT; generalize dependent v; generalize dependent f.
      induction f as [? HInd] using (well_founded_ind R.wf_eco); intros.
      assert (H0 := dec_val _ _ _ R_T); inversion H0; subst; clear R_T;
        assert (ht := R.dec_context_correct f v); unfold dec_context in DC;
          rewrite DC in ht; simpl in ht.
      contradiction (dec_context_red_bot DC) with a.
      contradiction (dec_context_val_bot DC) with a.
      clear H0; rewrite <- hh in ht.
      destruct (dec_context_term_next DC).
      destruct (dec_ec_ord ht) as [hq | [hq | [hq hw]]];
        [ contradiction (H0 a) | | subst; auto].
      symmetry in ht; destruct (elem_context_det hq ht) as [v1 h4]; subst t0.
      eapply HInd; eauto.
    Qed.

    Inductive decempty : term -> decomp -> Prop :=
    | d_intro : forall (t : term) (d : decomp) (DEC : dec t [] d), decempty t d.

    Inductive iter : decomp -> state -> answer -> Prop :=
    | i_val : forall v G, iter (d_val v) G (v, G)
    | i_red : forall r G G0 t E d a
                (CONTR : contract r G = Some (t, G0))
                (D_EM  : decempty (E [ t ]) d)
                (R_IT  : iter d G0 a),
                iter (d_red r E) G a.

    Inductive eval : term -> answer -> Prop :=
    | e_intro : forall t d a
                  (D_EM : decempty t d)
                  (ITER : iter d init a),
                  eval t a.

  End RS.

  Definition dec_term_correct    := dec_term_correct.
  Definition dec_context_correct := dec_context_correct.

  Lemma dec_val_self : forall v c d, dec (value_to_term v) c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec]; auto.
  Qed.

  Close Scope red_scope.

End RedRefSem.

Module Red_Prop (R : RED_LANG) (RS : RED_REF_SEM(R)) : RED_PROP R RS.

  Module LP := Lang_Prop R.
  Import LP.
  Import RS.RS.
  Import RS.
  Import R.
  Open Scope red_scope.

  Lemma dec_is_function : forall t d d0, decempty t d -> decempty t d0 -> d = d0.
  Proof.
    intros t d d0 DE DE0; inversion_clear DE; inversion_clear DE0.
    refine (dec_Ind
      (fun t E d (HDec : dec t E d) => forall d0 (DEC : dec t E d0), d = d0)
      (fun c v d (HDec : decctx c v d) =>
        forall d0 (DCTX : RS.decctx c v d0),  d = d0)
      _ _ _ _ _ _ _ t [] d DEC d0 DEC0); intros; simpl; auto; try apply HDec;
    match goal with
      | [ RD : (dec ?t ?c ?d), DT : (dec_term ?t = ?int) |- _ ] =>
        inversion RD; rewrite DT0 in DT; inversion DT
      | [ RC : (decctx ?v (?ec :: ?c) ?d), DC : (dec_context ?ec ?v = ?int) |- _ ] =>
        inversion RC; rewrite DC0 in DC; inversion DC
      | [ RC : (RS.decctx ?v R.empty ?d) |- _] => inversion RC
    end; subst; auto.
  Qed.
  Hint Resolve dec_is_function : prop.

  Lemma iter_is_function : forall d G a a0, iter d G a -> iter d G a0 -> a = a0.
  Proof with eauto with prop.
    induction 1; intros.
    inversion H...
    inversion H0; subst; rewrite CONTR0 in CONTR; inversion CONTR; subst;
    apply IHiter; cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.

  Lemma eval_is_function : forall t a a0, eval t a -> eval t a0 -> a = a0.
  Proof with eauto with prop.
    induction 1; intros; inversion H; subst; cutrewrite (d = d0) in ITER...
  Qed.

  Lemma dec_correct : forall t E d, dec t E d -> decomp_to_term d = E [ t ].
  Proof.
    induction 1 using dec_Ind with
      (P := fun t E d (HDec  : dec t E d) =>
        decomp_to_term d = E [ t ])
      (P0:= fun v E d (HDecE : decctx v E d) =>
        decomp_to_term d = E [value_to_term v]); simpl; auto;
      try (assert (hh := RS.dec_term_correct t); rewrite DT in hh; simpl in hh;
        try rewrite IHdec; subst; auto);
      assert (hh := RS.dec_context_correct f v); rewrite DC in hh; simpl in hh;
        try rewrite IHdec; try (contradiction hh); rewrite <- hh; auto.
  Qed.

  Lemma dec_total : forall t, exists d, decempty t d.
  Proof.
    intro t; destruct (decompose t) as [[v Hv] | [r [c Hp]]]; intros; subst t.
    exists (d_val v); constructor; rewrite dec_val_self; constructor.
    exists (d_red r c); constructor; apply dec_plug_rev;
      rewrite <- compose_empty; apply dec_redex_self.
  Qed.

  Lemma unique_decomposition : forall t, (exists v, t = value_to_term v) \/ 
      (exists r, exists E, E [redex_to_term r] = t /\ 
	  forall r0 E0, E0 [redex_to_term r0] = t -> r = r0 /\ E = E0).
  Proof.
    intro t; destruct (decompose t) as [[v H] | [r [E H]]]; intros;
      [left; exists v | right; exists r; exists E]; auto; split; auto; intros.
    assert (decempty t (d_red r E)).
      constructor; rewrite <- H; apply dec_plug_rev; rewrite <- compose_empty;
        apply dec_redex_self.
    assert (decempty t (d_red r0 E0)).
    constructor; rewrite <- H0; apply dec_plug_rev; rewrite <- compose_empty;
      apply dec_redex_self.
    assert (hh := dec_is_function _ _ _ H1 H2); injection hh; intros; auto.
  Qed.

End Red_Prop.

Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM (R)) <: PRE_ABSTRACT_MACHINE (R).
  Import RS.
  Import R.
  Module LP := Lang_Prop R.
  Import LP.

  Open Scope red_scope.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term := dec_term.
  Definition dec_context := dec_context.

  Definition dec_term_correct := dec_term_correct.
  Definition dec_context_correct := dec_context_correct.

  Inductive dec : term -> context -> decomp -> Prop :=
  | d_dec  : forall t E r
               (DT  : dec_term t = in_red r),
               dec t E (d_red r E)
  | d_v    : forall t E v d
               (DT  : dec_term t = in_val v)
               (R_C : decctx v E d),
               dec t E d
  | d_term : forall t t0 E f d
               (DT  : dec_term t = in_term t0 f)
               (R_T : dec t0 (f :: E) d),
               dec t E d
  with decctx : value -> context -> decomp -> Prop :=
  | dc_end  : forall v, decctx v [] (d_val v)
  | dc_dec  : forall v f E r
                (DC  : dec_context f v = in_red r),
                decctx v (f :: E) (d_red r E)
  | dc_val  : forall v v0 f E d
                (DC  : dec_context f v = in_val v0)
                (R_C : decctx v0 E d),
                decctx v (f :: E) d
  | dc_term : forall v f f0 E t d
                (DC  : dec_context f v = in_term t f0)
                (R_T : dec t (f0 :: E) d),
                decctx v (f :: E) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G, iter (d_val v) G (v, G)
  | i_red : forall r G G0 t E d a
              (CONTR  : contract r G = Some (t, G0))
              (DEC    : dec t E d)
              (R_ITER : iter d G0 a),
              iter (d_red r E) G a.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t d a
                (DEC  : dec t [] d)
                (ITER : iter d init a),
                eval t a.

  Lemma dec_id_l : forall t c d, RS.RS.dec t c d -> dec t c d.
  Proof.
    induction 1 using RS.dec_Ind with 
      (P := fun t c d (H : RS.RS.dec t c d) => dec t c d)
      (P0:= fun v c d (H0 : RS.decctx v c d) => decctx v c d);
      eauto using dec, decctx.
  Qed.
  Hint Resolve dec_id_l.

  Lemma dec_id_r : forall t c d, dec t c d -> RS.RS.dec t c d.
  Proof.
    induction 1 using dec_Ind with 
    (P := fun t c d (H : dec t c d) => RS.RS.dec t c d)
    (P0:= fun v c d (H0 : decctx v c d) => RS.decctx v c d);
    unfold RS.RS.dec; eauto using RS.decctx, RS.dec.
  Qed.
  Hint Resolve dec_id_r.

  Lemma iterRedPam : forall d G a, RS.RS.iter d G a -> iter d G a.
  Proof with auto.
    induction 1; [ apply i_val | eapply i_red; eauto; inversion_clear D_EM].
    rewrite compose_empty at 1; apply dec_id_l; apply RS.RS.dec_plug...
  Qed.

  Lemma evalRedPam : forall t a, RS.RS.eval t a -> eval t a.
  Proof with auto.
    intros t v H; inversion_clear H; apply e_intro with d;
      [inversion_clear D_EM | apply iterRedPam]...
  Qed.
  Hint Resolve evalRedPam.

  Lemma iterPamRed : forall d G a, iter d G a -> RS.RS.iter d G a.
  Proof with auto.
    induction 1; [constructor | econstructor 2; eauto; constructor];
      apply RS.RS.dec_plug_rev; rewrite <- compose_empty...
  Qed.

  Lemma evalPamRed : forall t a, eval t a -> RS.RS.eval t a.
  Proof.
    intros t v H; inversion_clear H; constructor 1 with d;
      [ constructor | apply iterPamRed]; auto.
  Qed.
  Hint Resolve evalPamRed.

  Theorem evalPam : forall t a, RS.RS.eval t a <-> eval t a.
  Proof with auto.
    split...
  Qed.

End PreAbstractMachine.

Module StagedAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: STAGED_ABSTRACT_MACHINE R.

  Module PAM := PreAbstractMachine R RS.
  Module LP := Lang_Prop R.
  Import LP.
  Import RS.
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term    := dec_term.
  Definition dec_context := dec_context.

  Definition dec_term_correct    := dec_term_correct.
  Definition dec_context_correct := dec_context_correct.

  Open Scope red_scope.

  Inductive dec : term -> context -> state -> answer -> Prop :=
  | d_dec  : forall t E r G a
               (DT   : dec_term t = in_red r)
               (R_IT : iter (d_red r E) G a),
               dec t E G a
  | d_v    : forall t E v G a
               (DT   : dec_term t = in_val v)
               (R_C  : decctx v E G a),
               dec t E G a
  | d_many : forall t t0 f E G a
               (DT   : dec_term t = in_term t0 f)
               (R_T  : dec t0 (f :: E) G a),
               dec t E G a
  with decctx : value -> context -> state -> answer -> Prop :=
  | dc_end  : forall v G a
               (IT_V : iter (d_val v) G a),
               decctx v [] G a
  | dc_dec  : forall v f E r G a
               (DC   : dec_context f v = in_red r)
               (R_IT : iter (d_red r E) G a),
               decctx v (f :: E) G a
  | dc_val  : forall v v0 f E G a
               (DC   : dec_context f v = in_val v0)
               (R_C  : decctx v0 E G a),
               decctx v (f :: E) G a
  | dc_term : forall v t f f0 E G a
               (DC   : dec_context f v = in_term t f0)
               (R_T  : dec t (f0 :: E) G a),
               decctx v (f :: E) G a
  with iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G, iter (d_val v) G (v, G)
  | i_red : forall r E G G0 t a
               (CONTR: contract r G = Some (t, G0))
               (R_T  : dec t E G0 a),
               iter (d_red r E) G a.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a, dec t [] init a -> eval t a.

  Lemma decPamSam : forall t E d
    (HDec : PAM.dec t E d)
    G a
    (HItr : iter d G a),
    dec t E G a.
  Proof with eauto using dec, decctx.
    induction 1 using PAM.dec_Ind with
    (P := fun t E d (HDec : PAM.dec t E d) =>
      forall G a, iter d G a -> dec t E G a)
    (P0 := fun E v d (HDec : PAM.decctx E v d) =>
      forall G a, iter d G a -> decctx E v G a);
    intros; simpl...
  Qed.
  Hint Resolve decPamSam.

  Lemma iterPamSam : forall d G a, PAM.iter d G a -> iter d G a.
  Proof with eauto using iter.
    induction 1...
  Qed.
  Hint Resolve iterPamSam.

  Lemma evalPamSam : forall t a, PAM.eval t a -> eval t a.
  Proof with eauto using eval.
    intros t v H; inversion_clear H...
  Qed.
  Hint Resolve evalPamSam.

  Module P := Red_Prop R RS.

  Lemma decSamPam : forall t E G a
    (HDec  : dec t E G a)
    d
    (HPDec : PAM.dec t E d),
    PAM.iter d G a.
  Proof with eauto using PAM.iter.
    induction 1 using dec_Ind with
      (P  := fun t E G a (HDec : dec t E G a) =>
        forall d (HPDec : PAM.dec t E d), PAM.iter d G a)
      (P0 := fun v E G a (HDec : decctx v E G a) =>
        forall d (HPDec : PAM.decctx v E d), PAM.iter d G a)
      (P1 := fun d G a (HDec : iter d G a) => PAM.iter d G a); intros; simpl...
    (* Case 1 *)
    change (PAM.dec_term t = R.in_red r) in DT;
      inversion HPDec; rewrite DT0 in DT; inversion DT; subst...
    (* Case 2 *)
    apply IHHDec; change (PAM.dec_term t = R.in_val v) in DT;
      inversion HPDec; subst; rewrite DT0 in DT; inversion DT; subst...
    (* Case 3 *)
    apply IHHDec; change (PAM.dec_term t = R.in_term t0 f) in DT;
      inversion HPDec; subst; rewrite DT0 in DT; inversion DT; subst...
    (* Case 4 *)
    inversion HPDec; subst...
    (* Case 5 *)
    change (PAM.dec_context f v = R.in_red r) in DC;
      inversion HPDec; subst; rewrite DC0 in DC; inversion DC; subst...
    (* Case 5 *)
    apply IHHDec; change (PAM.dec_context f v = R.in_val v0) in DC;
      clear IHHDec; inversion HPDec; rewrite DC0 in DC; inversion DC; subst...
    (* Case 6 *)
    apply IHHDec; change (PAM.dec_context f v = R.in_term t f0) in DC;
      inversion HPDec; subst; rewrite DC0 in DC; inversion DC; subst...
    (* Case 7 *)
    destruct(P.dec_total (E [ t ])) as [d HDecE]; inversion_clear HDecE.
    apply RS.dec_plug in DEC; rewrite <- LP.compose_empty in DEC...
  Qed.
  Hint Resolve decSamPam.

  Lemma evalSamPam : forall t a, eval t a -> PAM.eval t a.
  Proof with eauto using PAM.eval.
    intros t v H; inversion_clear H; destruct (P.dec_total t) as [d HDec];
      inversion_clear HDec...
  Qed.
  Hint Resolve evalSamPam.

  Theorem evalSam : forall t a, RS.eval t a <-> eval t a.
  Proof with auto.
    intros t v; rewrite PAM.evalPam; split; intros...
  Qed.

End StagedAbstractMachine.

Module EvalApplyMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: EVAL_APPLY_MACHINE R.

  Module SAM := StagedAbstractMachine R RS.
  Module LP := Lang_Prop R.
  Import LP.
  Import RS.
  Import R.

  Definition dec_term    := dec_term.
  Definition dec_context := dec_context.

  Definition dec_term_correct    := dec_term_correct.
  Definition dec_context_correct := dec_context_correct.

  Open Scope red_scope.

  Inductive dec : term -> context -> state -> answer -> Prop :=
  | d_d_r  : forall t t0 E r G G0 a
               (DT    : dec_term t = in_red r)
               (CONTR : contract r G = Some (t0, G0))
               (R_T   : dec t0 E G0 a),
               dec t E G a
  | d_v    : forall t v E G a
               (DT    : dec_term t = in_val v)
               (R_C   : decctx v E G a),
               dec t E G a
  | d_term : forall t t0 f E G a
               (DT    : dec_term t = R.in_term t0 f) 
               (R_T   : dec t0 (f :: E) G a),
               dec t E G a
  with decctx : value -> context -> state -> answer -> Prop :=
  | dc_end : forall v G, decctx v [] G (v, G)
  | dc_red : forall v f E r G G0 t a
               (DC    : dec_context f v = in_red r)
               (CONTR : contract r G = Some (t, G0))
               (R_T   : dec t E G0 a),
               decctx v (f :: E) G a
  | dc_rec : forall v v0 f E G a
               (DC    : dec_context f v = in_val v0)
               (R_C   : decctx v0 E G a),
               decctx v (f :: E) G a
  | dc_trm : forall v f f0 E G t a
               (DC    : dec_context f v = in_term t f0)
               (R_T   : dec t (f0 :: E) G a),
               decctx v (f :: E) G a.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a, dec t [] init a -> eval t a.

  Lemma decSamEam : forall t E G a
    (HSDec : SAM.dec t E G a),
    dec t E G a.
  Proof with eauto using dec, decctx.
    induction 1 using SAM.dec_Ind with
      (P := fun t E G a (HSDec : SAM.dec t E G a) => dec t E G a)
      (P0:= fun v E G a (HSDec : SAM.decctx v E G a) => decctx v E G a)
      (P1:= fun d G a (HSDec : SAM.iter d G a) =>
        match d with
          | d_val v => decctx v [] G a
          | d_red r E => forall t G0 (HCTR : contract r G = Some (t, G0)),
              dec t E G0 a
        end); simpl; intros; try inversion_clear R_IT...
    rewrite CONTR in HCTR; inversion HCTR; subst...
  Qed.

  Lemma evalSamEam : forall t a, SAM.eval t a -> eval t a.
  Proof.
    intros t a H; inversion_clear H; auto using eval, decSamEam.
  Qed.
  Hint Resolve evalSamEam.

  Lemma decEamSam : forall t E G a, dec t E G a -> SAM.dec t E G a.
  Proof with eauto using SAM.dec, SAM.decctx, SAM.iter.
    induction 1 using dec_Ind with
      (P := fun t E G a (HDec : dec t E G a) => SAM.dec t E G a)
      (P0:= fun v E G a (HDec : decctx v E G a) => SAM.decctx v E G a);
      intros; simpl...
  Qed.

  Lemma evalEamSam : forall t a, eval t a -> SAM.eval t a.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamSam; auto.
  Qed.
  Hint Resolve evalEamSam.

  Theorem evalEam : forall t a, RS.eval t a <-> eval t a.
  Proof with auto.
    intros t v; rewrite SAM.evalSam; split...
  Qed.

End EvalApplyMachine.

Module ProperEAMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: PROPER_EA_MACHINE R.

  Module EAM := EvalApplyMachine R RS.
  Module LP := Lang_Prop R.
  Import LP.
  Import RS.
  Import R.

  Open Scope red_scope.

  Definition dec_term    := dec_term.
  Definition dec_context := dec_context.

  Definition dec_term_correct    := dec_term_correct.
  Definition dec_context_correct := dec_context_correct.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> context -> state -> configuration
  | c_apply : context -> value -> state -> configuration
  | c_final : answer -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      c_init t → c_eval t [] init
  | t_red  : forall t t0 G G0 r E
      (DT    : dec_term t = in_red r)
      (CONTR : contract r G = Some (t0, G0)),
      c_eval t E G → c_eval t0 E G0
  | t_val  : forall t v E G
      (DT    : dec_term t = in_val v),
      c_eval t E G → c_apply E v G
  | t_term : forall t t0 f E G
      (DT    : dec_term t = R.in_term t0 f),
      c_eval t E G → c_eval t0 (f :: E) G
  | t_cfin : forall v G,
      c_apply [] v G → c_final (v, G)
  | t_cred : forall v t f E G G0 r
      (DC    : dec_context f v = in_red r)
      (CONTR : contract r G = Some (t, G0)),
      c_apply (f :: E) v G → c_eval t E G0
  | t_cval : forall v v0 f E G
      (DC    : dec_context f v = in_val v0),
      c_apply (f :: E) v G → c_apply E v0 G
  | t_cterm: forall v t f f0 E G
      (DC    : dec_context f v = in_term t f0),
      c_apply (f :: E) v G → c_eval t (f0 :: E) G
  where " a → b " := (transition a b).

  Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answer
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term   := term.
    Definition value := answer.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.

    Inductive trans_close : configuration -> configuration -> Prop :=
    | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
    | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall t a, trans_close (c_init t) (c_final a) -> eval t a.

  End AM.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).

  Lemma decEamTrans : forall t E G a, EAM.dec t E G a ->
    (c_eval t E G) →+ (c_final a).
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
      (P := fun t E G a (HDec : EAM.dec t E G a) =>
        (c_eval t E G) →+ (c_final a))
      (P0:= fun v E G a (HDec : EAM.decctx v E G a) =>
        (c_apply E v G) →+ (c_final a));
      intros; simpl; auto;
        try (constructor; constructor; auto; fail);
          econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve decEamTrans.

  Lemma evalEamMachine : forall t a, EAM.eval t a -> AM.eval t a.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor;
      econstructor 2; eauto; constructor.
  Qed.
  Hint Resolve evalEamMachine.

  Lemma transDecEam : forall t E G a,
    (c_eval t E G) →+ (c_final a) -> EAM.dec t E G a.
  Proof with eauto using EAM.dec, EAM.decctx.
    intros t E G a X.
    refine (@AM.trans_close_ind
    (fun c c0 => match c, c0 with
      | c_eval t E G, c_final a => EAM.dec t E G a
      | c_apply E v G, c_final a => EAM.decctx v E G a
      | _, _ => True
    end)
    _ _ (c_eval t E G) (c_final a) X); intros; auto.
    (* Case 1 *)
    revert H; case c0; case c1; simpl; intros; try inversion t2; subst; auto;
      inversion_clear H; constructor 1; auto.
    (* Case 2 *)
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl; auto;
      intros; inversion H; subst...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecEam.

  Lemma evalMachineEam : forall t a, AM.eval t a -> EAM.eval t a.
  Proof with auto.
    intros t v H; inversion_clear H; constructor; inversion_clear H0;
      inversion H; subst...
  Qed.
  Hint Resolve evalMachineEam.

  Theorem eval_apply_correct : forall t a, RS.RS.eval t a <-> AM.eval t a.
  Proof with auto.
    intros t a; rewrite EAM.evalEam; split...
  Qed.

End ProperEAMachine.

Module PushEnterMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PUSH_ENTER_MACHINE R.

  Module EAM := EvalApplyMachine R PRS.Red_Sem.
  Module PR := Red_Prop R PRS.Red_Sem.
  Module LP := Lang_Prop R.
  Import LP.
  Import PRS.
  Import R.

  Open Scope red_scope.

  Definition dec_term    := Red_Sem.dec_term.
  Definition dec_context := Red_Sem.dec_context.
  Definition dec_context_not_val := dec_context_not_val.
  Definition dec_context_correct := Red_Sem.dec_context_correct.
  Definition dec_term_correct    := Red_Sem.dec_term_correct.
  Definition dec_term_value      := dec_term_value.

  Inductive dec : term -> context -> state -> answer -> Prop :=
  | dec_r    : forall t t0 E r G G0 a
                 (DT    : dec_term t = in_red r)
                 (CONTR : R.contract r G = Some (t0, G0))
                 (R_T   : dec t0 E G0 a),
                 dec t E G a
  | dec_val  : forall t G v
                 (DT    : dec_term t = in_val v),
                 dec t [] G (v, G)
  | dec_v_t  : forall t t0 f f0 E v G a
                 (DT    : dec_term t = in_val v)
                 (DC    : dec_context f v = in_term t0 f0)
                 (R_T   : dec t0 (f0 :: E) G a),
                 dec t (f :: E) G a
  | dec_red  : forall t t0 f E v r G G0 a
                 (DT    : dec_term t = in_val v)
                 (DC    : dec_context f v = in_red r)
                 (CONTR : contract r G = Some (t0, G0))
                 (R_T   : dec t0 E G0 a),
                 dec t (f :: E) G a
  | dec_rec  : forall t t0 f E G a
                 (DT    : dec_term t = in_term t0 f)
                 (R_T   : dec t0 (f :: E) G a),
                 dec t E G a.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a, dec t [] init a -> eval t a.

  Lemma decEamPem : forall t E G a, EAM.dec t E G a -> dec t E G a.
  Proof with eauto using dec.
    induction 1 using EAM.dec_Ind with
      (P := fun t E G a (HDec : EAM.dec t E G a) => dec t E G a)
      (P0:= fun v E G a (HDec : EAM.decctx v E G a) =>
        match E with
          | nil    => dec (value_to_term v) [] G a
          | f :: E => forall d, dec_context f v = d ->
            match d with
              | in_red r => forall t G0 (HCTR : contract r G = Some (t, G0)),
                  dec t E G0 a
              | in_term t f0 => dec t (f0 :: E) G a
              | in_val v => False
            end
        end); intros; simpl...
    (* Case 1 *)
    inversion R_C; subst...
    (* Case 2.1 *)
    econstructor 4...
    apply (IHdec (in_red r))...
    (* Case 2.3 *)
    contradiction (dec_context_not_val _ _ _ DC).
    (* Case 2.4 *)
    econstructor 3...
    apply (IHdec (R.in_term t0 f0))...
    (* Case 4 *)
    constructor; apply dec_term_value...
    (* Case 5 *)
    change (EAM.dec_context f v = d) in H0; rewrite DC in H0; inversion H0;
      subst; simpl; intros.
    rewrite CONTR in HCTR; inversion HCTR; subst; auto.
    (* Case 7 *)
    contradiction (dec_context_not_val _ _ _ DC).
    (* Case 8 *)
    change (EAM.dec_context f v = d) in H0; rewrite DC in H0; subst; simpl...
  Qed.

  Lemma evalEamPem : forall t a, EAM.eval t a -> eval t a.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamPem; auto.
  Qed.
  Hint Resolve evalEamPem.

  Lemma decPemEam : forall t E G a
    (HDec : dec t E G a),
    EAM.dec t E G a.
  Proof with eauto using EAM.dec, EAM.decctx.
    induction 1; intros; simpl...
  Qed.

  Lemma evalPemEam : forall t a, eval t a -> EAM.eval t a.
  Proof.
    intros t a H; inversion_clear H; constructor; apply decPemEam; auto.
  Qed.
  Hint Resolve evalPemEam.

  Theorem evalPem : forall t a, Red_Sem.RS.eval t a <-> eval t a.
  Proof.
    intros t v; rewrite EAM.evalEam; split; auto.
  Qed.

End PushEnterMachine.

Module ProperPEMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PROPER_PE_MACHINE R.

  Module PEM := PushEnterMachine R PRS.
  Module LP := Lang_Prop R.
  Import LP.
  Import PRS.
  Import R.

  Open Scope red_scope.

  Definition dec_term    := Red_Sem.dec_term.
  Definition dec_context := Red_Sem.dec_context.
  Definition dec_term_value      := dec_term_value.
  Definition dec_context_not_val := dec_context_not_val.
  Definition dec_context_correct := Red_Sem.dec_context_correct.
  Definition dec_term_correct    := Red_Sem.dec_term_correct.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> context -> state -> configuration
  | c_final : answer -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      c_init t → c_eval t [] init
  | t_red  : forall t t0 E r G G0
      (DT    : dec_term t = in_red r)
      (CONTR : contract r G = Some (t0, G0)),
      c_eval t E G → c_eval t0 E G0
  | t_cval : forall t G v
      (DT    : dec_term t = in_val v),
      c_eval t [] G → c_final (v, G)
  | t_cred : forall t t0 v f E r G G0
      (DT    : dec_term t = in_val v)
      (DC    : dec_context f v = in_red r)
      (CONTR : contract r G = Some (t0, G0)),
      c_eval t (f :: E) G → c_eval t0 E G0
  | t_crec : forall t t0 v f f0 E G
      (DT    : dec_term t = in_val v)
      (DC    : dec_context f v = in_term t0 f0),
      c_eval t (f :: E) G → c_eval t0 (f0 :: E) G
  | t_rec  : forall t t0 f E G
      (DT    : dec_term t = in_term t0 f),
      c_eval t E G → c_eval t0 (f :: E) G
  where " a →  b " := (transition a b).

  Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answer
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := term.
    Definition value := answer.
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

  Lemma decPemTrans : forall t E G a
    (HDec : PEM.dec t E G a),
    (c_eval t E G) →+ (c_final a).
  Proof with eauto.
    induction 1; intros; simpl; try (constructor; constructor; auto; fail);
      econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve decPemTrans.

  Lemma evalPemMachine : forall t a, PEM.eval t a -> AM.eval t a.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor;
      econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve evalPemMachine.

  Lemma transDecPem : forall t E G a
    (HTCL : (c_eval t E G) →+ (c_final a)),
    PEM.dec t E G a.
  Proof with eauto using PEM.dec.
    intros t E G a X; refine (@AM.trans_close_ind
    (fun c c0 => match c, c0 with
      | c_eval t E G, c_final a => PEM.dec t E G a
      | _, _ => True
    end) _ _ (c_eval t E G) (c_final a) X); intros...
    generalize H; clear H; case c0; case c1; simpl; intros; try inversion t2;
      subst; auto; inversion_clear H; econstructor 2...
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl;
      auto; intros; inversion H; subst...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecPem.

  Lemma evalMachinePem : forall t a, AM.eval t a -> PEM.eval t a.
  Proof.
    intros t a H; constructor; inversion_clear H; inversion H0; subst;
      inversion H; subst; auto.
  Qed.
  Hint Resolve evalMachinePem.

  Theorem push_enter_correct : forall t a, Red_Sem.RS.eval t a <-> AM.eval t a.
  Proof.
    intros t v; rewrite PEM.evalPem; split; auto.
  Qed.

End ProperPEMachine.
