Require Import Setoid.
Require Export refocusing_signatures.
Require Import Wellfounded.Inclusion.
Require Import Wellfounded.Inverse_Image.

Module Lang_Prop (R : RED_LANG) : LANG_PROP R.

  Lemma plug_empty : forall t, R.plug t R.empty = t.
  Proof.
    intros; simpl; auto.
  Qed.
  Hint Resolve plug_empty : prop.

  Lemma compose_empty : forall c : R.context, c = R.compose c R.empty.
  Proof.
    apply app_nil_end.
  Qed.
  Hint Resolve compose_empty : prop.

  Lemma plug_compose : forall (c c' : R.context) (t : R.term), R.plug t (R.compose c c') = R.plug (R.plug t c) c'.
  Proof.
    apply fold_left_app.
  Qed.
  Hint Resolve plug_compose : prop.

End Lang_Prop.

Module RedRefSem (R : RED_REF_LANG) <: RED_REF_SEM R.R.

  Definition dec_term := R.dec_term.
  Definition dec_context := R.dec_context.
  Inductive dec : R.R.term -> R.R.context -> R.R.decomp -> Prop :=
  | d_dec  : forall (t : R.R.term) (c : R.R.context) (r : R.R.redex)
               (DT  : dec_term t = R.R.in_red r),
               dec t c (R.R.d_red r c)
  | d_v    : forall (t : R.R.term) (c : R.R.context) (v : R.R.value) (d : R.R.decomp)
               (DT  : dec_term t = R.R.in_val v)
               (R_C : decctx v c d),
               dec t c d
  | d_term : forall (t t0 : R.R.term) (c : R.R.context) (ec : R.R.elem_context) (d : R.R.decomp)
               (DT  : dec_term t = R.R.in_term t0 ec)
               (R_T : dec t0 (ec :: c) d),
               dec t c d
  with decctx : R.R.value -> R.R.context -> R.R.decomp -> Prop :=
  | dc_end  : forall (v : R.R.value), decctx v R.R.empty (R.R.d_val v)
  | dc_dec  : forall (v : R.R.value) (ec : R.R.elem_context) (c : R.R.context) (r : R.R.redex)
                (DC  : dec_context ec v = R.R.in_red r),
                decctx v (ec :: c) (R.R.d_red r c)
  | dc_val  : forall (v v0 : R.R.value) (ec : R.R.elem_context) (c : R.R.context) (d : R.R.decomp)
                (DC  : dec_context ec v = R.R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (ec :: c) d
  | dc_term : forall (v : R.R.value) (ec ec0 : R.R.elem_context) (c : R.R.context) (t : R.R.term) (d : R.R.decomp)
                (DC  : dec_context ec v = R.R.in_term t ec0)
                (R_T : dec t (ec0 :: c) d),
                decctx v (ec :: c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
    
  Notation " a <| b " := (R.subterm_order a b) (at level 40).
  Notation " a <: b " := (R.ec_order a b) (at level 40).

  Lemma sto_trans : forall t t0 t1, t <| t0 -> t0 <| t1 -> t <| t1.
  Proof with auto.
    induction 2;
    econstructor 2; eauto.
  Qed.

  Lemma plug_le_eq : forall c t t0, R.R.plug t0 c = t -> t0 <| t \/ (c = R.R.empty /\ t = t0).
  Proof with auto.
    induction c; intros.
    simpl in H; right; auto.
    left; simpl in H.
    destruct (IHc _ _ H) as [H0 | [H1 H0]]; clear IHc.
    eapply sto_trans; eauto.
    econstructor 1; eauto; econstructor; eauto.
    subst c; econstructor; eauto; econstructor; eauto.
  Qed.

  Lemma st_c : forall t0 t1, t0 <| t1 -> exists c, R.R.plug t0 c = t1.
  Proof with auto.
    intros; induction H; inversion H; subst.
    exists (ec :: nil); simpl; auto.
    destruct IHclos_trans_n1 as [c H1].
    exists (c ++ (ec :: nil)); unfold R.R.plug in *; rewrite fold_left_app; simpl; subst; auto.
  Qed.

  Definition value_one_step (v v0 : R.R.value) : Prop := R.subterm_one_step (R.R.value_to_term v) (R.R.value_to_term v0).
  Definition value_order := clos_trans_n1 R.R.value value_one_step.
    
  Notation " a <v| b " := (value_order a b) (at level 40).
    
  Lemma wf_vo : well_founded value_order.
  Proof.
    apply wf_clos_trans_r; apply wf_inverse_image; apply R.wf_st1.
  Qed.

(*    Reserved Notation " a <v| b " (at level 40).

    Inductive value_order : R.R.value -> R.R.value -> Prop :=
    | vc_1 : forall v0 v1 ec (ATOM: R.R.atom_plug (R.R.value_to_term v0) ec = (R.R.value_to_term v1)), v0 <v| v1
    | vc_m : forall v0 v1 v2 ec (REC: v0 <v| v1) (ATOM: R.R.atom_plug (R.R.value_to_term v1) ec = (R.R.value_to_term v2)), v0 <v| v2
    where " a <v| b " := (value_order a b).

    Definition hp (v v0 : R.R.value) := (R.R.value_to_term v) <| (R.R.value_to_term v0).

    Lemma wf_vo : well_founded value_order.
    Proof with auto.
      apply wf_incl with hp.
      unfold inclusion; intros; induction H; [ econstructor | econstructor 2]; eauto; econstructor; eauto.
      apply wf_inverse_image; apply R.wf_sto.
    Qed.*)

    Lemma dec_val : forall (v : R.R.value) (c : R.R.context) (d : R.R.decomp), dec (R.R.value_to_term v) c d -> decctx v c d.
    Proof with eauto.
      induction v using (well_founded_ind wf_vo); intros.
      remember (R.dec_term (R.R.value_to_term v)); assert (hh := R.dec_term_correct (R.R.value_to_term v));
      destruct i; rewrite <- Heqi in hh.
      symmetry in hh; contradiction (R.R.value_redex _ _ hh).
      apply R.R.value_to_term_injective in hh; inversion H0; subst; unfold dec_term in DT;
      rewrite DT in Heqi; inversion Heqi; subst; auto.
      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate H1.
      destruct H1 as [v0 H1]; subst t.
      symmetry in hh; assert (ht := R.st_1 _ _ _ hh);
      apply (tn1_step _ value_one_step) in ht; change (v0 <v| v) in ht.
      inversion H0; subst; unfold dec_term in DT; rewrite DT in Heqi; inversion Heqi; subst.
      clear H0 Heqi DT; assert (H0 := H _ ht _ _ R_T); clear ht R_T.
      generalize dependent v0.
      induction ec using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context ec v0); assert (hc := R.dec_context_correct ec v0);
      destruct i; rewrite <- Heqi in hc; rewrite <- hh in hc.
      symmetry in hc; contradiction (R.R.value_redex _ _ hc).
      clear H H0; apply R.R.value_to_term_injective in hc; subst.
      inversion H1; subst; unfold dec_context in DC; rewrite DC in Heqi; inversion Heqi; subst; auto.
      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate.
      destruct H2 as [v1 H2]; subst t.
      inversion H1; subst; unfold dec_context in DC; rewrite DC in Heqi; inversion Heqi; subst.
      clear Heqi H1.
      apply H0 with ec1 v1...
      destruct (R.dec_context_term_next _ _ _ _ DC)...
      apply H...
      repeat econstructor...
    Qed.

    Lemma val_dec : forall v c d, decctx v c d -> dec (R.R.value_to_term v) c d.
    Proof with eauto.
      induction v using (well_founded_ind wf_vo); intros.
      remember (R.dec_term (R.R.value_to_term v)); assert (hh := R.dec_term_correct (R.R.value_to_term v));
      destruct i; rewrite <- Heqi in hh.
      symmetry in hh; contradiction (R.R.value_redex _ _ hh).
      apply R.R.value_to_term_injective in hh; subst; econstructor...
      destruct (R.R.value_trivial v t (e :: nil)); simpl...
      discriminate H1.
      destruct H1 as [v0 H1]; subst t; econstructor 3...
      apply H; [ repeat econstructor | clear Heqi; generalize dependent v0]...
      induction e using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context e v0); assert (hc := R.dec_context_correct e v0);
      destruct i; rewrite <- Heqi in hc; rewrite hh in hc.
      symmetry in hc; contradiction (R.R.value_redex _ _ hc).
      clear H H1; apply R.R.value_to_term_injective in hc; subst; econstructor...
      destruct (R.R.value_trivial v t (e0 :: nil)); simpl...
      discriminate.
      destruct H2 as [v1 H2]; subst t; econstructor 4...
      apply H.
      repeat econstructor...
      apply H1...
      symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi)...
    Qed.

  Module RS : RED_SEM R.R with Definition dec := dec.
    Definition dec := dec.

    Lemma decompose : forall t : R.R.term, (exists v:R.R.value, t = R.R.value_to_term v) \/
      (exists r:R.R.redex, exists c:R.R.context, R.R.plug (R.R.redex_to_term r) c = t).
    Proof with eauto.
      induction t using (well_founded_ind R.wf_sto); intros.


      remember (R.dec_term t); assert (hh := R.dec_term_correct t); destruct i;
      rewrite <- Heqi in hh.
      right; exists r; exists R.R.empty...
      left; exists v...
      destruct (H t0) as [[v Hv] | [r [c Hrc]]].
      repeat econstructor...
      subst t0; clear Heqi; generalize dependent v; induction e using (well_founded_ind R.wf_eco); intros.
      remember (R.dec_context e v); assert (ht := R.dec_context_correct e v); destruct i;
      rewrite <- Heqi in ht; rewrite hh in ht.
      right; exists r; exists R.R.empty...
      left; exists v0...
      destruct (H t0) as [[v0 Hv] | [r [c Hrc]]].
      repeat econstructor...
      symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi) as [H1 _].
      subst t0; destruct (H0 e0 H1 v0 ht) as [[v1 Hv1] | [r [c Hrc]]].
      left; exists v1...
      right; exists r; exists c...
      right; exists r; exists (c ++ (e0 :: nil)); 
      subst t0; unfold R.R.plug in *; rewrite fold_left_app...
      right; exists r; exists (c ++ (e :: nil));
      subst t0; unfold R.R.plug in *; rewrite fold_left_app...
    Qed.

    Lemma dec_redex_self_e : forall (r : R.R.redex), dec (R.R.redex_to_term r) (R.R.empty) (R.R.d_red r R.R.empty).
    Proof with eauto.
      intros; remember (dec_term (R.R.redex_to_term r)); destruct i; unfold dec_term in Heqi;
      assert (hh := R.dec_term_correct (R.R.redex_to_term r)); rewrite <- Heqi in hh; simpl in hh.
      apply R.R.redex_to_term_injective in hh; subst; constructor...
      contradict hh;  apply R.R.value_redex.
      symmetry in Heqi; assert (H := R.dec_term_term_top _ _ _ Heqi).
      econstructor 3; simpl; eauto.
      destruct (R.R.redex_trivial r t (e :: R.R.empty) hh) as [H1 | [v H1]]; [ discriminate | subst t].
      clear H Heqi.
      generalize dependent v; generalize dependent e.
      induction e using (well_founded_ind R.wf_eco); intros.
      apply val_dec.
      remember (R.dec_context e v); assert (ht := R.dec_context_correct e v);
      rewrite <- Heqi in ht; destruct i; simpl in ht.
      rewrite hh in ht; apply R.R.redex_to_term_injective in ht; subst.
      constructor...
      rewrite <- ht in hh; contradiction (R.R.value_redex _ _ hh).
      econstructor 4; simpl; eauto.
      rewrite hh in ht; destruct (R.R.redex_trivial r t (e0 :: R.R.empty) ht) as [H4 | [v1 H4]].
      discriminate.
      subst t; symmetry in Heqi; destruct (R.dec_context_term_next _ _ _ _ Heqi); apply H...
    Qed.

    Lemma dec_redex_self : forall (r : R.R.redex) (c : R.R.context), dec (R.R.redex_to_term r) c (R.R.d_red r c).
    Proof with eauto.
      intros.
      assert (hh := dec_redex_self_e r).
      induction hh using dec_Ind with
      (P := fun t c0 d (H : dec t c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red r' c1 => dec t (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end)
      (P0:= fun v c0 d (H : decctx v c0 d) => match d with
        | R.R.d_val v => True
        | R.R.d_red r' c1 => decctx v (R.R.compose c0 c) (R.R.d_red r' (R.R.compose c1 c))
      end); try destruct d; auto; 
      [ constructor | econstructor | econstructor 3 | constructor | econstructor | econstructor 4]...
    Qed.

    Lemma dec_correct : forall t c d, dec t c d -> R.R.decomp_to_term d = R.R.plug t c.    
    Proof.
      induction 1 using dec_Ind with
      (P := fun t c d (H:dec t c d) => R.R.decomp_to_term d = R.R.plug t c)
      (P0:= fun v c d (H:decctx v c d) => R.R.decomp_to_term d = R.R.plug (R.R.value_to_term v) c); 
      simpl; auto; match goal with
      | [ DT: (dec_term ?t = ?int) |- _ ] => unfold dec_term in DT; assert (hh := R.dec_term_correct t); rewrite DT in hh
      | [ DC: (dec_context ?ec ?v = ?int) |- _ ] => unfold dec_context in DC; assert (hh := R.dec_context_correct ec v); rewrite DC in hh
      end; try rewrite IHdec; rewrite <- hh; subst; auto.
    Qed.

    Lemma dec_plug_rev : forall c c0 t d, dec t (R.R.compose c c0) d -> dec (R.R.plug t c) c0 d.
    Proof with auto.
      induction c; intros; simpl; auto.
      apply IHc; clear IHc; remember (R.dec_term (R.R.atom_plug t a)); destruct i;
      assert (hh := R.dec_term_correct (R.R.atom_plug t a)); rewrite <- Heqi in hh.
      symmetry in Heqi; discriminate ( R.dec_term_red_empty _ _ Heqi t (a :: nil)); reflexivity.
      symmetry in Heqi; discriminate (R.dec_term_val_empty _ _ Heqi t (a :: nil))...
      destruct (R.dec_ec_ord t0 t e a hh) as [H0 | [H0 | [H0 H1]]]; try (subst; econstructor 3; eauto; fail).
      symmetry in Heqi; contradict (R.dec_term_term_top _ _ _ Heqi _ H0).
      symmetry in hh; destruct (R.elem_context_det _ _ _ _ H0 hh) as [v H1]; subst t0.
      econstructor 3; eauto.
      clear Heqi; generalize dependent v; generalize dependent e.
      induction e using (well_founded_ind R.wf_eco); intros.
      apply val_dec.
      remember (R.dec_context e v); destruct i; symmetry in Heqi;
      assert (ht := R.dec_context_correct e v); rewrite Heqi in ht.
      contradiction (R.dec_context_red_bot _ _ _ Heqi a).
      contradiction (R.dec_context_val_bot _ _ _ Heqi a).
      destruct (R.dec_context_term_next _ _ _ _ Heqi) as [H2 H3].
      econstructor 4; eauto; rewrite <- hh in ht.
      destruct (R.dec_ec_ord _ _ _ _ ht) as [H4 | [H4 | [H4 H5]]]; try (subst; auto; fail).
      contradiction (H3 a H1).
      symmetry in ht; clear H3; destruct (R.elem_context_det _ _ _ _ H4 ht) as [v0 H5]; subst t0.
      apply H0; auto.
    Qed.

    Lemma dec_plug : forall c c0 t d, dec (R.R.plug t c) c0 d -> dec t (R.R.compose c c0) d.
    Proof with auto.
      induction c; intros; simpl; auto.
      apply IHc in H; clear IHc; inversion H; subst; unfold dec_term in DT; clear H;
      assert (hh := R.dec_term_correct (R.R.atom_plug t a)); rewrite DT in hh.
      discriminate (R.dec_term_red_empty _ _ DT t (a :: nil)); reflexivity.
      symmetry in hh; discriminate (R.dec_term_val_empty _ _ DT t (a :: R.R.empty))...
      destruct (R.dec_ec_ord t1 t ec a hh) as [H2 | [H2 | [H2 H3]]].
      contradiction (R.dec_term_term_top _ _ _ DT a).
      symmetry in hh; destruct (R.elem_context_det _ _ _ _ H2 hh) as [v H3]; subst t1.
      clear DT; generalize dependent v; generalize dependent ec.
      induction ec using (well_founded_ind R.wf_eco); intros.
      assert (H0 := dec_val _ _ _ R_T); inversion H0; subst; clear R_T;
      assert (ht := R.dec_context_correct ec v); unfold dec_context in DC; rewrite DC in ht; simpl in ht.
      contradiction (R.dec_context_red_bot _ _ _ DC a).
      contradiction (R.dec_context_val_bot _ _ _ DC a).
      clear H0.
      rewrite <- hh in ht.
      destruct (R.dec_context_term_next _ _ _ _ DC).
      destruct (R.dec_ec_ord _ _ _ _ ht) as [hq | [hq | [hq hw]]].
      contradiction (H1 a).
      symmetry in ht; destruct (R.elem_context_det _ _ _ _ hq ht) as [v1 h4]; subst t0.
      apply H with ec1 v1; auto.
      subst; auto.
      subst; auto.
    Qed.

    Inductive decempty : R.R.term -> R.R.decomp -> Prop :=
    | d_intro : forall (t : R.R.term) (d : R.R.decomp), dec t R.R.empty d -> decempty t d.

    Inductive iter : R.R.decomp -> R.R.value -> Prop :=
    | i_val : forall (v : R.R.value), iter (R.R.d_val v) v
    | i_red : forall (r : R.R.redex) (t : R.R.term) (c : R.R.context) (d : R.R.decomp) (v : R.R.value),
                R.R.contract r = Some t -> decempty (R.R.plug t c) d -> iter d v -> iter (R.R.d_red r c) v.

    Inductive eval : R.R.term -> R.R.value -> Prop :=
    | e_intro : forall (t : R.R.term) (d : R.R.decomp) (v : R.R.value), decempty t d -> iter d v -> eval t v.

  End RS.

  Definition dec_term_correct := R.dec_term_correct.
  Definition dec_context_correct := R.dec_context_correct.

  Lemma dec_val_self : forall v c d, dec (R.R.value_to_term v) c d <-> decctx v c d.
  Proof.
    split; [apply dec_val | apply val_dec]; auto.
  Qed.

End RedRefSem.

Module Red_Prop (R : RED_LANG) (RS : RED_REF_SEM(R)) : RED_PROP R RS.

  Module LP := Lang_Prop R.

  Lemma dec_is_function : forall t d d0, RS.RS.decempty t d -> RS.RS.decempty t d0 -> d = d0.
  Proof.
    intros t d d0 DE DE0; inversion_clear DE; inversion_clear DE0.
    refine (RS.dec_Ind (fun t c d (H:RS.RS.dec t c d) => forall d0 (DEC : RS.RS.dec t c d0), d = d0)
    (fun c v d (H:RS.decctx c v d) => forall d0 (DCTX : RS.decctx c v d0),  d = d0)
    _ _ _ _ _ _ _ t R.empty d DEC d0 DEC0); intros; simpl; auto; try apply H; match goal with
    | [ RD : (RS.RS.dec ?t ?c ?d), DT : (RS.dec_term ?t = ?int) |- _ ] => inversion RD; rewrite DT0 in DT; inversion DT
    | [ RC : (RS.decctx ?v (?ec :: ?c) ?d), DC : (RS.dec_context ?ec ?v = ?int) |- _ ] => inversion RC; rewrite DC0 in DC; inversion DC
    | [ RC : (RS.decctx ?v R.empty ?d) |- _] => inversion RC
    end; subst; auto.
  Qed.
  Hint Resolve dec_is_function : prop.

  Lemma iter_is_function : forall d v v0, RS.RS.iter d v -> RS.RS.iter d v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros.
    inversion H...
    inversion H0; subst; rewrite CONTR0 in CONTR; inversion CONTR; subst;
    apply IHiter; cutrewrite (d = d0)...
  Qed.
  Hint Resolve iter_is_function : prop.

  Lemma eval_is_function : forall t v v0, RS.RS.eval t v -> RS.RS.eval t v0 -> v = v0.
  Proof with eauto with prop.
    induction 1; intros; inversion H; subst; cutrewrite (d = d0) in ITER...
  Qed.

  Lemma dec_correct : forall t c d, RS.RS.dec t c d -> R.decomp_to_term d = R.plug t c.
  Proof.
    induction 1 using RS.dec_Ind with
    (P := fun t c d (H:RS.RS.dec t c d) => R.decomp_to_term d = R.plug t c)
    (P0:= fun v c d (H:RS.decctx v c d) => R.decomp_to_term d = R.plug (R.value_to_term v) c); simpl; auto;
    try (assert (hh := RS.dec_term_correct t); rewrite DT in hh; simpl in hh; try rewrite IHdec; subst; auto);
    assert (hh := RS.dec_context_correct ec v); rewrite DC in hh; simpl in hh; try rewrite IHdec; try (contradiction hh); rewrite <- hh; auto.
  Qed.

  Lemma dec_total : forall t, exists d, RS.RS.decempty t d.
  Proof.
    intro t; destruct (RS.RS.decompose t) as [[v Hv] | [r [c Hp]]]; intros; subst t.
    exists (R.d_val v); constructor; rewrite RS.dec_val_self; constructor.
    exists (R.d_red r c); constructor; apply RS.RS.dec_plug_rev;
    rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
  Qed.

  Lemma unique_decomposition : forall t:R.term, (exists v:R.value, t = R.value_to_term v) \/ 
      (exists r:R.redex, exists c:R.context, R.plug (R.redex_to_term r) c = t /\ 
	  forall (r0:R.redex) c0, (R.plug (R.redex_to_term r0) c0 = t -> r=r0 /\ c= c0)).
  Proof.
    intro t; destruct (RS.RS.decompose t) as [[v H] | [r [c H]]]; intros;
    [left; exists v | right; exists r; exists c]; auto; split; auto; intros.
    assert (RS.RS.decempty t (R.d_red r c)).
    constructor; rewrite <- H; apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
    assert (RS.RS.decempty t (R.d_red r0 c0)).
    constructor; rewrite <- H0; apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
    assert (hh := dec_is_function _ _ _ H1 H2); injection hh; intros; auto.
  Qed.

End Red_Prop.
(*
Module RefRedSem_SOS (R : RED_REF_LANG) <: SOS_SEM.

  Definition not_val (t : R.R.term) : Prop := forall v, R.R.value_to_term v <> t.

  Lemma not_triv_term_ec : forall t, ~R.only_trivial t -> exists t0, exists ec0, R.R.atom_plug t0 ec0 = t /\ not_val t0.
  Proof.
    intros; remember (R.dec_term t); destruct i; [contradict H | contradict H | idtac]; symmetry in Heqi.
    unfold R.only_trivial; intros; left; eapply R.dec_term_red_empty; eauto.
    unfold R.only_trivial; intros; left; assert (hh := R.dec_term_correct t); 
    rewrite Heqi in hh; subst t; eapply R.value_empty; simpl; eauto.
    
    assert (hh := R.dec_term_correct t); rewrite Heqi in hh; subst t.

    generalize dependent e; induction e using (well_founded_ind R.wf); intros.


  Definition dec_simpl (t : R.R.term) (H : not_val t) :
    {d : R.R.interm_dec | match d with
      | R.R.in_red r => R.R.redex_to_term r = t
      | R.R.in_val v => False
      | R.R.in_term t0 ec0 => R.R.atom_plug t0 ec0 = t /\ forall v, R.R.value_to_term v <> t0
    end}.
  Proof.
    intros t H; remember (R.dec_term t); destruct i; assert (hh := R.dec_term_correct t); rewrite <- Heqi in hh; simpl in *.
    constructor 1 with (R.R.in_red r);  auto.
    contradiction (H _ hh).
    clear Heqi; generalize dependent e; induction e using (well_founded_ind R.wf).
  *)


Module PreAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM (R)) <: PRE_ABSTRACT_MACHINE (R).

  Module LP := Lang_Prop R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term : R.term -> R.interm_dec := RS.dec_term.
  Definition dec_context : R.elem_context -> R.value -> R.interm_dec := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.

  Inductive dec : R.term -> R.context -> R.decomp -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex)
                 (DT  : dec_term t = R.in_red r),
                 dec t c (R.d_red r c)
  | d_v    : forall (t : R.term) (c : R.context) (v : R.value) (d : R.decomp)
                 (DT  : dec_term t = R.in_val v)
                 (R_C : decctx v c d),
                 dec t c d
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (d : R.decomp)
                 (DT  : dec_term t = R.in_term t0 ec)
                 (R_T : dec t0 (ec :: c) d),
                 dec t c d
  with decctx : R.value -> R.context -> R.decomp -> Prop :=
  | dc_end  : forall (v : R.value), decctx v R.empty (R.d_val v)
  | dc_dec  : forall (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
                (DC  : dec_context ec v = R.in_red r),
                decctx v (ec :: c) (R.d_red r c)
  | dc_val  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (d : R.decomp)
                (DC  : dec_context ec v = R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (ec :: c) d
  | dc_term : forall (v : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term) (d : R.decomp)
                (DC  : dec_context ec v = R.in_term t ec0)
                (R_T : dec t (ec0 :: c) d),
                decctx v (ec :: c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : R.decomp -> R.value -> Prop :=
  | i_val : forall (v : R.value), iter (R.d_val v) v
  | i_red : forall (r : R.redex) (t : R.term) (c : R.context) (d : R.decomp) (v : R.value)
              (CONTR  : R.contract r = Some t)
              (DEC    : dec t c d)
              (R_ITER : iter d v),
              iter (R.d_red r c) v.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (d : R.decomp) (v : R.value)
                (DEC  : dec t R.empty d)
                (ITER : iter d v),
                eval t v.

  Lemma dec_id_l : forall t c d, RS.RS.dec t c d -> dec t c d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
    (P := fun t c d (H : RS.RS.dec t c d) => dec t c d)
    (P0:= fun v c d (H0 : RS.decctx v c d) => decctx v c d);
    [ constructor | econstructor 2 | econstructor 3 | constructor | econstructor 2 | econstructor | econstructor 4]...
  Qed.
  Hint Resolve dec_id_l.

  Lemma dec_id_r : forall t c d, dec t c d -> RS.RS.dec t c d.
  Proof with eauto.
    induction 1 using dec_Ind with 
    (P := fun t c d (H : dec t c d) => RS.RS.dec t c d)
    (P0:= fun v c d (H0 : decctx v c d) => RS.decctx v c d);
    [ constructor | econstructor 2 | econstructor 3 | constructor | econstructor | econstructor | econstructor 4]...
  Qed.
  Hint Resolve dec_id_r.

  Lemma iterRedPam : forall (d : R.decomp) (v : R.value), RS.RS.iter d v -> iter d v.
  Proof with auto.
    induction 1; [ constructor | constructor 2 with t d; auto;
    inversion_clear D_EM]; rewrite app_nil_end with (l:=c);
    apply dec_id_l; apply RS.RS.dec_plug...
  Qed.

  Lemma evalRedPam : forall (t : R.term) (v : R.value), RS.RS.eval t v -> eval t v.
  Proof with auto.
    intros t v H; inversion_clear H; constructor 1 with d; [inversion_clear D_EM | apply iterRedPam]...
  Qed.
  Hint Resolve evalRedPam.

  Lemma iterPamRed : forall (d : R.decomp) (v : R.value), iter d v -> RS.RS.iter d v.
  Proof with auto.
    induction 1; [constructor | constructor 2 with t d; auto; constructor];
    apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty...
  Qed.

  Lemma evalPamRed : forall (t : R.term) (v : R.value), eval t v -> RS.RS.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor 1 with d; [ constructor | apply iterPamRed]; auto.
  Qed.
  Hint Resolve evalPamRed.

  Theorem evalPam : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    split...
  Qed.

End PreAbstractMachine.

Module StagedAbstractMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: STAGED_ABSTRACT_MACHINE R.

  Module PAM := PreAbstractMachine R RS.
  Module LP := Lang_Prop R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term : R.term -> R.interm_dec := RS.dec_term.
  Definition dec_context : R.elem_context -> R.value -> R.interm_dec := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex) (v : R.value)
               (DT   : dec_term t = R.in_red r)
               (R_IT : iter (R.d_red r c) v),
               dec t c v
  | d_v    : forall (t : R.term) (c : R.context) (v v0 : R.value)
               (DT   : dec_term t = R.in_val v)
               (R_C  : decctx v c v0),
               dec t c v0
  | d_many : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
               (DT   : dec_term t = R.in_term t0 ec)
               (R_T  : dec t0 (ec :: c) v),
               dec t c v
  with decctx : R.value -> R.context -> R.value -> Prop :=
  | dc_end  : forall (v v0 : R.value)
               (IT_V : iter (R.d_val v) v0),
               decctx v R.empty v0
  | dc_dec  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
               (DC   : dec_context ec v = R.in_red r)
               (R_IT : iter (R.d_red r c) v0),
               decctx v (ec :: c) v0
  | dc_val  : forall (v v0 v1 : R.value) (ec : R.elem_context) (c : R.context)
               (DC   : dec_context ec v = R.in_val v0)
               (R_C  : decctx v0 c v1),
               decctx v (ec :: c) v1
  | dc_term : forall (v v0 : R.value) (t : R.term) (ec ec0 : R.elem_context) (c : R.context)
               (DC   : dec_context ec v = R.in_term t ec0)
               (R_T  : dec t (ec0 :: c) v0),
               decctx v (ec :: c) v0
  with iter : R.decomp -> R.value -> Prop :=
  | i_val : forall (v : R.value), iter (R.d_val v) v
  | i_red : forall (r : R.redex) (c : R.context) (t : R.term) (v : R.value)
               (CONTR: R.contract r = Some t)
               (R_T  : dec t c v),
               iter (R.d_red r c) v.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

  Lemma decPamSam : forall (t : R.term) (c : R.context) (d : R.decomp),
    PAM.dec t c d -> forall (v : R.value), iter d v -> dec t c v.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P := fun t c d (H:PAM.dec t c d) => forall v, iter d v -> dec t c v)
    (P0 := fun c v d (H:PAM.decctx c v d) => forall v', iter d v' -> decctx c v v');
    intros; simpl;
    [econstructor 1 | econstructor 2 | econstructor 3 | constructor | econstructor | econstructor 3 | econstructor 4]...
  Qed.
  Hint Resolve decPamSam.

  Lemma iterPamSam : forall (d : R.decomp) (v : R.value), PAM.iter d v -> iter d v.
  Proof with eauto.
    induction 1; [constructor | econstructor 2]...
  Qed.
  Hint Resolve iterPamSam.

  Lemma evalPamSam : forall (t : R.term) (v : R.value), PAM.eval t v -> eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor...
  Qed.
  Hint Resolve evalPamSam.

  Module P := Red_Prop R RS.

  Lemma decSamPam : forall (t : R.term) (c : R.context) (v : R.value),
    dec t c v -> forall (d : R.decomp), PAM.dec t c d -> PAM.iter d v.
  Proof with auto.
    induction 1 using dec_Ind with
    (P  := fun t c v (H:dec t c v) => forall d, PAM.dec t c d -> PAM.iter d v)
    (P0 := fun v c v' (H:decctx v c v') => forall d, PAM.decctx v c d -> PAM.iter d v')
    (P1 := fun d v (H:iter d v) => PAM.iter d v); intros; simpl.
    (* Case 1 *)
    change (PAM.dec_term t = R.in_red r) in DT;
    inversion H; rewrite DT0 in DT; inversion DT; subst...
    (* Case 2 *)
    apply IHdec; change (PAM.dec_term t = R.in_val v) in DT;
    inversion H; subst; rewrite DT0 in DT; inversion DT; subst...
    (* Case 3 *)
    apply IHdec; change (PAM.dec_term t = R.in_term t0 ec) in DT;
    inversion H0; subst; rewrite DT0 in DT; inversion DT; subst...
    (* Case 4 *)
    inversion H; subst...
    (* Case 5 *)
    change (PAM.dec_context ec v = R.in_red r) in DC;
    inversion H; subst; rewrite DC0 in DC; inversion DC; subst...
    (* Case 5 *)
    apply IHdec; clear IHdec; change (PAM.dec_context ec v = R.in_val v0) in DC;
    inversion H; rewrite DC0 in DC; inversion DC; subst...
    (* Case 6 *)
    apply IHdec; inversion H0; subst; change (PAM.dec_context ec v = R.in_term t ec0) in DC;
    rewrite DC0 in DC; inversion DC; subst...
    (* Case 5 *)
    constructor.
    (* Case 6 *)
    destruct(P.dec_total (R.plug t c)) as [d H0]; inversion_clear H0.
    apply RS.RS.dec_plug in DEC; rewrite <- LP.compose_empty in DEC;
    constructor 2 with t d...
  Qed.
  Hint Resolve decSamPam.

  Lemma evalSamPam : forall (t : R.term) (v : R.value), eval t v -> PAM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; destruct (P.dec_total t) as [d H]; inversion_clear H; econstructor...
  Qed.
  Hint Resolve evalSamPam.

  Theorem evalSam : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros t v; rewrite PAM.evalPam; split; intros...
  Qed.

End StagedAbstractMachine.

Module EvalApplyMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: EVAL_APPLY_MACHINE R.

  Module SAM := StagedAbstractMachine R RS.

  Definition dec_term := RS.dec_term.
  Definition dec_context := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | d_d_r  : forall (t t0 : R.term) (c : R.context) (r : R.redex) (v : R.value)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0)
               (R_T   : dec t0 c v),
               dec t c v
  | d_v    : forall (t : R.term) (c : R.context) (v v0 : R.value)
               (DT    : dec_term t = R.in_val v)
               (R_C   : decctx v c v0),
               dec t c v0
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
               (DT    : dec_term t = R.in_term t0 ec) 
               (R_T   : dec t0 (ec :: c) v),
               dec t c v
  with decctx : R.value -> R.context -> R.value -> Prop :=
  | dc_end : forall (v : R.value), decctx v R.empty v
  | dc_red : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex) (t : R.term)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t)
               (R_T   : dec t c v0),
               decctx v (ec :: c) v0
  | dc_rec : forall (v v0 v1 : R.value) (ec : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_val v0)
               (R_C   : decctx v0 c v1),
               decctx v (ec :: c) v1
  | dc_trm : forall (v v0 : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term)
               (DC    : dec_context ec v = R.in_term t ec0)
               (R_T   : dec t (ec0 :: c) v0),
               decctx v (ec :: c) v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

  Lemma decSamEam : forall (t : R.term) (c : R.context) (v : R.value), SAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using SAM.dec_Ind with
    (P := fun t c v (H:SAM.dec t c v) => dec t c v)
    (P0:= fun c v v' (H:SAM.decctx c v v') => decctx c v v')
    (P1:= fun d v (H:SAM.iter d v) => match d with
                                        | R.d_val v' => decctx v R.empty v'
                                        | R.d_red r c => forall t : R.term,
                                                         R.contract r = Some t -> dec t c v
                                      end); simpl; intros.
    (* Case 1 *)
    inversion R_IT; subst; econstructor 1...
    (* Case 2 *)
    econstructor 2...
    (* Case 3 *)
    econstructor 3...
    (* Case 4 *)
    inversion IT_V; subst; constructor.
    (* Case 5 *)
    inversion_clear R_IT; econstructor 2...
    (* Case 6 *)
    econstructor 3...
    (* Case 7 *)
    econstructor 4...
    (* Case 8 *)
    constructor.
    (* Case 9 *)
    rewrite CONTR in H0; inversion H0; subst; auto.
  Qed.

  Lemma evalSamEam : forall (t : R.term) (v : R.value), SAM.eval t v -> eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decSamEam; auto.
  Qed.
  Hint Resolve evalSamEam.

  Lemma decEamSam : forall (t : R.term) (c : R.context) (v : R.value), dec t c v -> SAM.dec t c v.
  Proof with eauto.
    induction 1 using dec_Ind with
    (P := fun t c v (H:dec t c v) => SAM.dec t c v)
    (P0:= fun v c v' (H:decctx v c v') => SAM.decctx v c v'); intros; simpl.
    econstructor 1; try econstructor...
    econstructor 2...
    econstructor 3...
    repeat constructor.
    econstructor 2; try econstructor 2...
    econstructor 3...
    econstructor 4...
  Qed.

  Lemma evalEamSam : forall (t : R.term) (v : R.value), eval t v -> SAM.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamSam; auto.
  Qed.
  Hint Resolve evalEamSam.

  Theorem evalEam : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> eval t v.
  Proof with auto.
    intros t v; rewrite SAM.evalSam; split...
  Qed.

End EvalApplyMachine.

Module ProperEAMachine (R : RED_LANG) (RS : RED_REF_SEM R) <: PROPER_EA_MACHINE R.

  Module EAM := EvalApplyMachine R RS.

  Definition dec_term := RS.dec_term.
  Definition dec_context := RS.dec_context.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.
    
  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_apply : R.context -> R.value -> configuration
  | c_final : R.value -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).
  
  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term), transition (c_init t) (c_eval t R.empty)
  | t_red  : forall (t t0 : R.term) (c : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0),
               (c_eval t c) → (c_eval t0 c)
  | t_val  : forall (t : R.term) (v : R.value) (c : R.context)
      	       (DT    : dec_term t = R.in_val v),
               (c_eval t c) → (c_apply c v)
  | t_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_term t0 ec),
               (c_eval t c) → (c_eval t0 (ec :: c))
  | t_cfin : forall (v : R.value),
               (c_apply R.empty v) → (c_final v)
  | t_cred : forall (v : R.value) (t : R.term) (ec : R.elem_context) (c : R.context) (r : R.redex)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t),
               (c_apply (ec :: c) v) → (c_eval t c)
  | t_cval : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_val v0),
               (c_apply (ec :: c) v) → (c_apply c v0)
  | t_cterm: forall (v : R.value) (t : R.term) (ec ec0 : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_term t ec0),
               (c_apply (ec :: c) v) → (c_eval t (ec0 :: c))
  where " a → b " := (transition a b).

  Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := R.term.
    Definition value := R.value.
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

  Definition trfun (cfg : configuration) : option configuration :=
    match cfg with
      | c_init t           => Some (c_eval t R.empty)
      | c_eval t E         =>
        match dec_term t with
          | R.in_red r  =>
            match R.contract r with
              | Some t' => Some (c_eval t' E)
              | None    => None
            end
          | R.in_val v    => Some (c_apply E v)
          | R.in_term t f => Some (c_eval t (f :: E))
        end
      | c_apply nil v       => Some (c_final v)
      | c_apply (f :: E) v =>
        match dec_context f v with
          | R.in_red r =>
            match R.contract r with
              | Some t' => Some (c_eval t' E)
              | None    => None
            end
          | R.in_val v    => Some (c_apply E v)
          | R.in_term t f => Some (c_eval t (f :: E))
        end
      | c_final _          => None
    end.

  Lemma transition_fun : forall cfg cfg0
    (HTran : transition cfg cfg0),
    trfun cfg = Some cfg0.
  Proof.
    intros; inversion_clear HTran;
    repeat (simpl;
      match goal with
        | [DT : dec_term ?t = ?ir       |- context [dec_term ?t]] => rewrite DT
        | [DC : dec_context ?f ?v = ?ir |- context [dec_context ?f ?v]] => rewrite DC
        | [CTR : R.contract ?r = ?ot |- context [R.contract ?r]] => rewrite CTR
      end); reflexivity.
  Qed.

  Lemma fun_transition : forall cfg,
    match trfun cfg with
      | Some cfg' => transition cfg cfg'
      | None => forall cfg', ~transition cfg cfg'
    end.
  Proof.
    destruct cfg; simpl.
    (* Init *)
    apply t_init.
    (* Eval *)
    remember (dec_term t) as dt; destruct dt; simpl; symmetry in Heqdt.
    (* red *)
    remember (R.contract r) as ct; destruct ct; simpl; symmetry in Heqct.
    (* ok *)
    eapply t_red; eassumption.
    (* fail *)
    intros ? HTran; inversion_clear HTran;
      rewrite Heqdt in DT; inversion DT; subst; rewrite Heqct in CONTR;
        inversion CONTR.
    (* val *)
    eapply t_val; assumption.
    (* term *)
    eapply t_term; assumption.
    (* Apply *)
    destruct c; simpl.
    (* empty *)
    apply t_cfin.
    (* frame *)
    remember (dec_context e v) as dc; destruct dc; simpl; symmetry in Heqdc.
    (* red *)
    remember (R.contract r) as ct; destruct ct; simpl; symmetry in Heqct.
    (* ok *)
    eapply t_cred; eassumption.
    (* fail *)
    intros ? HTran; inversion_clear HTran;
      rewrite Heqdc in DC; inversion DC; subst; rewrite Heqct in CONTR;
        inversion CONTR.
    (* val *)
    apply t_cval; assumption.
    (* term *)
    apply t_cterm; assumption.
    (* Final *)
    intros ? HTran; inversion HTran.
  Qed.

  Notation " a →+ b " := (AM.trans_close a b) (at level 40, no associativity).

  Lemma decEamTrans : forall (t:R.term) (c : R.context) (v:R.value), EAM.dec t c v -> (c_eval t c) →+ (c_final v).
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t c v (H:EAM.dec t c v) => (c_eval t c) →+ (c_final v))
    (P0:= fun v c v' (H:EAM.decctx v c v') =>  (c_apply c v) →+ (c_final v')); intros; simpl; auto;
    try (constructor; constructor; auto; fail); econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve decEamTrans.

  Lemma evalEamMachine : forall (t : R.term) (v : R.value), EAM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor; econstructor 2 with (c_eval t R.empty); auto; constructor.
  Qed.
  Hint Resolve evalEamMachine.

  Lemma transDecEam : forall (t : R.term) (c : R.context) (v : R.value), (c_eval t c) →+ (c_final v) -> EAM.dec t c v.
  Proof with eauto.
    intros t c v X.
    refine (AM.trans_close_ind
    (fun c c0 =>match c, c0 with
      | c_eval t c, c_final v => EAM.dec t c v
      | c_apply c v, c_final v0 => EAM.decctx v c v0
      | _, _ => True
    end)
    _ _ (c_eval t c) (c_final v) X); intros; auto.
    (* Case 1 *)
    generalize H; clear H; case c0; case c1; simpl; intros; try inversion t2; subst; auto;
    inversion_clear H; constructor 1; auto.
    (* Case 2 *)
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl; auto; intros; inversion H; subst.
    econstructor...
    econstructor 3...
    econstructor 2...
    econstructor...
    econstructor 4...
    econstructor 3...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecEam.

  Lemma evalMachineEam : forall (t : R.term) (v : R.value), AM.eval t v -> EAM.eval t v.
  Proof with auto.
    intros t v H; inversion_clear H; constructor; inversion_clear H0; inversion H; subst...
  Qed.
  Hint Resolve evalMachineEam.

  Theorem eval_apply_correct : forall (t : R.term) (v : R.value), RS.RS.eval t v <-> AM.eval t v.
  Proof with auto.
    intros t v; rewrite EAM.evalEam; split...
  Qed.

End ProperEAMachine.

Module PushEnterMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PUSH_ENTER_MACHINE R.

  Module EAM := EvalApplyMachine R PRS.Red_Sem.
  Module PR := Red_Prop R PRS.Red_Sem.

  Definition dec_term := PRS.Red_Sem.dec_term.
  Definition dec_context := PRS.Red_Sem.dec_context.
  Definition dec_context_not_val := PRS.dec_context_not_val.
  Definition dec_context_correct := PRS.Red_Sem.dec_context_correct.
  Definition dec_term_correct := PRS.Red_Sem.dec_term_correct.
  Definition dec_term_value := PRS.dec_term_value.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | dec_r    : forall (t t0 : R.term) (c : R.context) (r : R.redex) (v : R.value)
                 (DT    : dec_term t = R.in_red r)
                 (CONTR : R.contract r = Some t0)
                 (R_T   : dec t0 c v),
                 dec t c v
  | dec_val  : forall (t : R.term) (v : R.value)
                 (DT    : dec_term t = R.in_val v),
                 dec t R.empty v
  | dec_v_t  : forall (t t0 : R.term) (ec ec0 : R.elem_context) (c : R.context) (v v0 : R.value)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_term t0 ec0)
                 (R_T   : dec t0 (ec0 :: c) v0),
                 dec t (ec :: c) v0
  | dec_red  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v v0 : R.value) (r : R.redex)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_red r)
                 (CONTR : R.contract r = Some t0)
                 (R_T   : dec t0 c v0),
                 dec t (ec :: c) v0
  | dec_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
                 (DT    : dec_term t = R.in_term t0 ec)
                 (R_T   : dec t0 (ec :: c) v),
                 dec t c v.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

  Lemma decEamPem : forall (t : R.term) (c : R.context) (v : R.value), EAM.dec t c v -> dec t c v.
  Proof with eauto.
    induction 1 using EAM.dec_Ind with
    (P := fun t c v (H:EAM.dec t c v) => dec t c v)
    (P0:= fun v c v0 (H:EAM.decctx v c v0) =>
      match c with
      | nil => dec (R.value_to_term v) R.empty v0
      | (ec :: c) => forall d : R.interm_dec, dec_context ec v = d ->
        match d with
        | R.in_red r => forall t : R.term, R.contract r = Some t -> dec t c v0
        | R.in_term t ec0 => dec t (ec0 :: c) v0
        | R.in_val v => False
        end
      end); intros; simpl.
    (* Case 1 *)
    econstructor...
    (* Case 2 *)
    inversion R_C; subst.
    (* Case 2.1 *)
    constructor...
    (* Case 2.2 *)
    econstructor 4...
    apply (IHdec (R.in_red r))...
    (* Case 2.3 *)
    contradict (dec_context_not_val _ _ _ DC).
    (* Case 2.4 *)
    econstructor 3...
    apply (IHdec (R.in_term t0 ec0))...
    (* Case 3 *)
    econstructor 5...
    (* Case 4 *)
    constructor; apply dec_term_value...
    (* Case 5 *)
    change (EAM.dec_context ec v = d) in H0; rewrite DC in H0; inversion H0;
    subst; simpl; intros.
    rewrite CONTR in H0; inversion H0; subst; auto.
    (* Case 7 *)
    contradict (dec_context_not_val _ _ _ DC).
    (* Case 8 *)
    change (EAM.dec_context ec v = d) in H0; rewrite DC in H0; subst; simpl...
  Qed.

  Lemma evalEamPem : forall (t : R.term) (v : R.value), EAM.eval t v -> eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamPem; auto.
  Qed.
  Hint Resolve evalEamPem.

  Lemma decPemEam : forall (t : R.term) (c : R.context) (v : R.value), dec t c v -> EAM.dec t c v.
  Proof with eauto.
    induction 1; intros; simpl; auto.
    econstructor 1...
    econstructor 2... econstructor...
    econstructor 2... econstructor 4...
    econstructor 2... econstructor 2...
    econstructor 3...
  Qed.

  Lemma evalPemEam : forall (t : R.term) (v : R.value), eval t v -> EAM.eval t v.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decPemEam; auto.
  Qed.
  Hint Resolve evalPemEam.

  Theorem evalPem : forall (t : R.term) (v : R.value), PRS.Red_Sem.RS.eval t v <-> eval t v.
  Proof.
    intros t v; rewrite EAM.evalEam; split; auto.
  Qed.

End PushEnterMachine.

Module ProperPEMachine (R : RED_LANG) (PRS : PE_REF_SEM R) <: PROPER_PE_MACHINE R.

  Module PEM := PushEnterMachine R PRS.

  Definition dec_term := PRS.Red_Sem.dec_term.
  Definition dec_context := PRS.Red_Sem.dec_context.
  Definition dec_term_value := PEM.dec_term_value.
  Definition dec_context_not_val := PRS.dec_context_not_val.
  Definition dec_context_correct := PRS.Red_Sem.dec_context_correct.
  Definition dec_term_correct := PRS.Red_Sem.dec_term_correct.

  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_final : R.value -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term),
               c_init t → c_eval t R.empty
  | t_red  : forall (t t0 : R.term) (c : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r = Some t0),
               c_eval t c → c_eval t0 c
  | t_cval : forall (t : R.term) (v : R.value)
               (DT    : dec_term t = R.in_val v),
               c_eval t R.empty → c_final v
  | t_cred : forall (t t0 : R.term) (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r = Some t0),
               c_eval t (ec :: c) → c_eval t0 c
  | t_crec : forall (t t0 : R.term) (v : R.value) (ec ec0 : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_term t0 ec0),
               c_eval t (ec :: c) → c_eval t0 (ec0 :: c)
  | t_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_term t0 ec),
               c_eval t c → c_eval t0 (ec :: c)
  where " a →  b " := (transition a b).

  Definition trfun (cfg : configuration) : option configuration :=
    match cfg with
      | c_init t           => Some (c_eval t R.empty)
      | c_eval t E         =>
        match dec_term t with
          | R.in_red r  =>
            match R.contract r with
              | Some t' => Some (c_eval t' E)
              | None    => None
            end
          | R.in_val v    =>
            match E with
              | nil      => Some (c_final v)
              | (f :: E) =>
                match dec_context f v with
                  | R.in_red r =>
                    match R.contract r with
                      | Some t' => Some (c_eval t' E)
                      | None    => None
                    end
                  | R.in_val v    => None
                  | R.in_term t f => Some (c_eval t (f :: E))
                end
            end
          | R.in_term t f => Some (c_eval t (f :: E))
        end
      | c_final _          => None
    end.

  Lemma transition_fun : forall cfg cfg0
    (HTran : transition cfg cfg0),
    trfun cfg = Some cfg0.
  Proof.
    intros; inversion_clear HTran;
    repeat (simpl;
      match goal with
        | [DT : dec_term ?t = ?ir       |- context [dec_term ?t]] => rewrite DT
        | [DC : dec_context ?f ?v = ?ir |- context [dec_context ?f ?v]] => rewrite DC
        | [CTR : R.contract ?r = ?ot |- context [R.contract ?r]] => rewrite CTR
      end); reflexivity.
  Qed.

  Lemma fun_transition : forall cfg,
    match trfun cfg with
      | Some cfg' => transition cfg cfg'
      | None => forall cfg', ~transition cfg cfg'
    end.
  Proof.
    destruct cfg; simpl.
    (* Init *)
    apply t_init.
    (* Eval *)
    remember (dec_term t) as dt; destruct dt; simpl; symmetry in Heqdt.
    (* red *)
    remember (R.contract r) as ct; destruct ct; simpl; symmetry in Heqct.
    (* ok *)
    eapply t_red; eassumption.
    (* fail *)
    intros ? HTran; inversion_clear HTran;
      rewrite Heqdt in DT; inversion DT; subst; rewrite Heqct in CONTR;
        inversion CONTR.
    (* val *)
    destruct c; simpl.
    (* empty *)
    apply t_cval; assumption.
    (* frame *)
    remember (dec_context e v) as dc; destruct dc; simpl; symmetry in Heqdc.
    (* red *)
    remember (R.contract r) as ct; destruct ct; simpl; symmetry in Heqct.
    (* ok *)
    eapply t_cred; eassumption.
    (* fail *)
    intros ? HTran; inversion_clear HTran; rewrite Heqdt in DT; inversion DT; subst;
      rewrite Heqdc in DC; inversion DC; subst; rewrite Heqct in CONTR;
        inversion CONTR.
    (* val *)
    contradiction (dec_context_not_val _ _ _ Heqdc).
    (* term *)
    eapply t_crec; eassumption.
    (* term *)
    eapply t_rec; assumption.
    (* Final *)
    intros ? HTran; inversion HTran.
  Qed.

  Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := R.term.
    Definition value := R.value.
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

  Lemma decPemTrans : forall (t : R.term) (c : R.context) (v : R.value), PEM.dec t c v -> (c_eval t c) →+ (c_final v).
  Proof with eauto.
    induction 1; intros; simpl; try (constructor; constructor; auto; fail); econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve decPemTrans.

  Lemma evalPemMachine : forall (t : R.term) (v : R.value), PEM.eval t v -> AM.eval t v.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor; econstructor 2; eauto; econstructor...
  Qed.
  Hint Resolve evalPemMachine.

  Lemma transDecPem : forall (t : R.term) (c : R.context) (v : R.value), (c_eval t c) →+ (c_final v) -> PEM.dec t c v.
  Proof with eauto.
    intros t c v X; refine (AM.trans_close_ind
    (fun c c0 => match c, c0 with
      | c_eval t c, c_final v => PEM.dec t c v
      | _, _ => True
    end) _ _ (c_eval t c) (c_final v) X); intros...
    generalize H; clear H; case c0; case c1; simpl; intros; try inversion t2; subst; auto; inversion_clear H; econstructor 2...
    generalize H H0 H1; clear H H0 H1; case c0; case c1; case c2; simpl; auto; intros; inversion H; subst.
    econstructor...
    econstructor 4...
    econstructor 3...
    econstructor 5...
    inversion H0; subst; inversion H2.
  Qed.
  Hint Resolve transDecPem.

  Lemma evalMachinePem : forall (t : R.term) (v : R.value), AM.eval t v -> PEM.eval t v.
  Proof.
    intros t v H; constructor; inversion_clear H; inversion H0; subst; inversion H; subst; auto.
  Qed.
  Hint Resolve evalMachinePem.

  Theorem push_enter_correct : forall (t : R.term) (v : R.value), PRS.Red_Sem.RS.eval t v <-> AM.eval t v.
  Proof.
    intros t v; rewrite (PEM.evalPem); split; auto.
  Qed.

End ProperPEMachine.
