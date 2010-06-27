Require Import Setoid.
Require Export refocusing_trace_signatures.

Module Lang_PropT (R : RED_LANG) : LANG_PROP R.

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

End Lang_PropT.

Module Red_PropT (R : RED_LANG) (RS : RED_REF_SEM_T(R)) : RED_PROP_T R RS.

  Module LP := Lang_PropT R.

  Lemma dec_is_function : forall t d d0, RS.RS.decempty t d -> RS.RS.decempty t d0 -> d = d0.
  Proof.
    intros t d d0 DE DE0; inversion_clear DE; inversion_clear DE0.
    refine (RS.dec_Ind (fun t c d (H:RS.RS.dec t c d) => forall d0, RS.RS.dec t c d0 -> d = d0)
    (fun c v d (H:RS.decctx c v d) => forall d0, RS.decctx c v d0 -> d = d0)
    _ _ _ _ _ _ _ t R.empty d H d0 H0); intros; simpl; auto;
    try (apply H1; inversion H2; rewrite H3 in e; inversion e; subst; auto).
    inversion H1; rewrite H2 in e; inversion e; subst; auto.
    inversion H1; reflexivity.
    inversion H1; subst; [rewrite H6 in e | rewrite H5 in e | rewrite H5 in e]; inversion e; auto.
    apply H1; inversion H2; [rewrite H7 in e | rewrite H6 in e | rewrite H6 in e]; inversion e; subst; auto.
    apply H1; inversion H2; [rewrite H7 in e | rewrite H6 in e | rewrite H6 in e]; inversion e; subst; auto.
  Qed.
  Hint Resolve dec_is_function : prop.

  Lemma gather_is_function : forall d tr tr0, RS.RS.gather d tr -> RS.RS.gather d tr0 -> bisim_stream tr tr0.
  Proof with eauto with prop.
    cofix; intros.
    inversion H; subst; inversion H0; subst.
    repeat constructor.
    rewrite H1 in H6; inversion H6; subst;
    apply (dec_is_function _ _ _ H2) in H7; subst; constructor; eauto.
  Qed.
  Hint Resolve gather_is_function : prop.

  Lemma eval_is_function : forall t tr tr0, RS.RS.eval t tr -> RS.RS.eval t tr0 -> bisim_stream tr tr0.
  Proof with eauto with prop.
    intros; inversion_clear H; inversion_clear H0; apply (dec_is_function _ _ _ H1) in H; subst...
  Qed.

  Lemma dec_correct : forall t c d, RS.RS.dec t c d -> R.decomp_to_term d = R.plug t c.
  Proof.
    induction 1 using RS.dec_Ind with
    (P := fun t c d (H:RS.RS.dec t c d) => R.decomp_to_term d = R.plug t c)
    (P0:= fun v c d (H:RS.decctx v c d) => R.decomp_to_term d = R.plug (R.value_to_term v) c); simpl; auto;
    try (assert (hh := RS.dec_term_correct t); rewrite e in hh; simpl in hh; try rewrite IHdec; subst; auto);
    assert (hh := RS.dec_context_correct ec v); rewrite e in hh; simpl in hh; try rewrite IHdec; rewrite <- hh; auto.
  Qed.

  Lemma dec_total : forall t, exists d, RS.RS.decempty t d.
  Proof.
    intro t; elim (RS.RS.decompose t); intros.
    destruct H as [v H]; exists (R.d_val v); rewrite H; constructor; econstructor 2;
    [ eapply RS.dec_term_value | constructor ].
    destruct H as [r [c H]]; rewrite <- H; exists (R.d_red r c); constructor.
    apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
  Qed.

  Lemma unique_decomposition : forall t:R.term, (exists v:R.value, t = R.value_to_term v) \/ 
      (exists r:R.redex, exists c:R.context, R.plug (R.redex_to_term r) c = t /\ 
	  forall (r0:R.redex) c0, (R.plug (R.redex_to_term r0) c0 = t -> r=r0 /\ c= c0)).
  Proof.
    intro t; elim (RS.RS.decompose t); intros; destruct H; [left | right];
    split with x; auto; destruct H; split with x0; split; auto; intros.
    assert (RS.RS.decempty t (R.d_red x x0)).
    constructor; rewrite <- H; apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
    assert (RS.RS.decempty t (R.d_red r0 c0)).
    constructor; rewrite <- H0; apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty; apply RS.RS.dec_redex_self.
    assert (hh := dec_is_function _ _ _ H1 H2); injection hh; intros; auto.
  Qed.

End Red_PropT.

Module PreAbstractMachineT (R : RED_LANG) (RS : RED_REF_SEM_T (R)) <: PRE_ABSTRACT_MACHINE_T (R).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term := RS.dec_term.
  Definition dec_context := RS.dec_context.
  Definition dec_term_value := RS.dec_term_value.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : R.term -> R.context -> R.decomp -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex),
                 dec_term t = R.in_red r -> dec t c (R.d_red r c)
  | d_v    : forall (t : R.term) (c : R.context) (v : R.value) (d : R.decomp),
                 dec_term t = R.in_val v -> decctx v c d -> dec t c d
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (d : R.decomp),
                 dec_term t = R.in_term t0 ec -> dec t0 (ec :: c) d -> dec t c d
  with decctx : R.value -> R.context -> R.decomp -> Prop :=
  | dc_end  : forall (v : R.value), decctx v R.empty (R.d_val v)
  | dc_dec  : forall (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex),
                dec_context ec v = R.in_red r -> decctx v (ec :: c) (R.d_red r c)
  | dc_val  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (d : R.decomp),
                dec_context ec v = R.in_val v0 -> decctx v0 c d -> decctx v (ec :: c) d
  | dc_term : forall (v : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term) (d : R.decomp),
                dec_context ec v = R.in_term t ec0 -> dec t (ec0 :: c) d -> decctx v (ec :: c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.
  Definition trace := stream R.decomp.

  CoInductive gather : R.decomp -> trace -> Prop :=
  | i_val : forall (v : R.value), gather (R.d_val v) (s_cons (R.d_val v) s_nil)
  | i_red : forall (r : R.redex) (t : R.term) (c : R.context) (d : R.decomp) (tr : trace),
              R.contract r = Some t -> dec t c d -> gather d tr -> gather (R.d_red r c) (s_cons (R.d_red r c) tr).

  CoInductive eval : R.term -> trace -> Prop :=
  | e_intro : forall (t : R.term) (d : R.decomp) (tr : trace), dec t R.empty d -> gather d tr -> eval t tr.

  Module LP := Lang_PropT R.

  Lemma dec_id_l : forall t c d, RS.RS.dec t c d -> dec t c d.
  Proof with eauto.
    induction 1 using RS.dec_Ind with 
    (P := fun t c d (H : RS.RS.dec t c d) => dec t c d)
    (P0:= fun v c d (H0 : RS.decctx v c d) => decctx v c d);
    [ constructor | econstructor 2 | econstructor 3 | constructor | econstructor | econstructor | econstructor 4]...
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

  Lemma gatherRedPam : forall (d : R.decomp) (ds : trace), RS.RS.gather d ds -> gather d ds.
  Proof with auto.
    cofix; intros.
    destruct d; inversion H; subst.
    constructor.
    apply gatherRedPam in H5.
    econstructor; eauto.
    inversion_clear H3; rewrite LP.compose_empty with (c:=c);
    apply dec_id_l;     apply RS.RS.dec_plug...
  Qed.

  Lemma evalRedPam : forall (t : R.term) (ds : trace), RS.RS.eval t ds -> eval t ds.
  Proof with auto.
    intros; inversion_clear H; constructor 1 with d; [inversion_clear H0 | apply gatherRedPam]...
  Qed.
  Hint Resolve evalRedPam.

  Lemma gatherPamRed : forall (d : R.decomp) (ds : trace), gather d ds -> RS.RS.gather d ds.
  Proof with auto.
    cofix G; intros; destruct d; inversion H; [constructor | constructor 2 with t d; auto; constructor];
    apply RS.RS.dec_plug_rev; rewrite <- LP.compose_empty...
  Qed.

  Lemma evalPamRed : forall (t : R.term) (ds : trace), eval t ds -> RS.RS.eval t ds.
  Proof.
    intros t v H; inversion_clear H; constructor 1 with d; [ constructor | apply gatherPamRed]; auto.
  Qed.
  Hint Resolve evalPamRed.

  Theorem evalPam : forall (t : R.term) (ds : trace), RS.RS.eval t ds <-> eval t ds.
  Proof with auto.
    split...
  Qed.

End PreAbstractMachineT.

Module StagedAbstractMachineT (R : RED_LANG) (RS : RED_REF_SEM_T R) <: STAGED_ABSTRACT_MACHINE_T R.

  Module PAM := PreAbstractMachineT R RS.

  Definition dec_term  := RS.dec_term.
  Definition dec_context := RS.dec_context.
  Definition dec_term_value := RS.dec_term_value.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.
  Definition trace := stream R.decomp.

  CoInductive dec : R.term -> R.context -> trace -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex) (ds : trace),
               dec_term t = R.in_red r -> gather (R.d_red r c) ds -> dec t c ds
  | d_v    : forall (t : R.term) (c : R.context) (v : R.value) (ds : trace),
               dec_term t = R.in_val v -> decctx v c ds -> dec t c ds
  | d_many : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (ds : trace),
               dec_term t = R.in_term t0 ec -> dec t0 (ec :: c) ds -> dec t c ds
  with decctx : R.value -> R.context -> trace -> Prop :=
  | dc_end  : forall (v : R.value) (ds : trace), gather (R.d_val v) ds -> decctx v R.empty ds
  | dc_dec  : forall (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex) (ds : trace),
                dec_context ec v = R.in_red r -> gather (R.d_red r c) ds -> decctx v (ec :: c) ds
  | dc_val  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (ds : trace),
                dec_context ec v = R.in_val v0 -> decctx v0 c ds -> decctx v (ec :: c) ds
  | dc_term : forall (v : R.value) (t : R.term) (ec ec0 : R.elem_context) (c : R.context) (ds : trace),
                dec_context ec v = R.in_term t ec0 -> dec t (ec0 :: c) ds -> decctx v (ec :: c) ds
  with gather : R.decomp -> trace -> Prop :=
  | i_val : forall (v : R.value), gather (R.d_val v) (s_cons (R.d_val v) s_nil)
  | i_red : forall (r : R.redex) (c : R.context) (t : R.term) (ds : trace),
              R.contract r = Some t -> dec t c ds -> gather (R.d_red r c) (s_cons (R.d_red r c) ds).

(*  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with gather_Ind := Induction for gather Sort Prop.*)

  CoInductive eval : R.term -> trace -> Prop :=
  | e_intro : forall (t : R.term) (ds : trace), dec t R.empty ds -> eval t ds.

  Lemma decPamSam : forall (t : R.term) (c : R.context) (d : R.decomp),
    PAM.dec t c d -> forall (ds : trace), gather d ds -> dec t c ds.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P := fun t c d (H:PAM.dec t c d) => forall ds, gather d ds -> dec t c ds)
    (P0 := fun c v d (H:PAM.decctx c v d) => forall ds, gather d ds -> decctx c v ds);
    intros; simpl;
    [econstructor 1 | econstructor 2 | econstructor 3 | constructor | econstructor | econstructor 3 | econstructor 4]...
  Qed.
  Hint Resolve decPamSam.

  Lemma dect : forall t c d ds, PAM.dec t c d -> PAM.gather d ds -> dec t c ds.
  Proof with eauto.
    refine (cofix DT t c d ds PT PG : dec t c ds := _
      with DV v c d ds (PV : PAM.decctx v c d) (PG : PAM.gather d ds) : decctx v c ds := _
      for DT).
    inversion PT; subst.
    econstructor...
    inversion PG; econstructor; eauto.
    econstructor 2...
    econstructor 3...
    inversion PV; subst.
    constructor; inversion PG; constructor.
    econstructor...
    inversion PG; econstructor...
    econstructor 3...
    econstructor 4...
  Qed.

  Lemma iterPamSam : forall (d : R.decomp) (ds : trace), PAM.gather d ds -> gather d ds.
  Proof with eauto.
    intros; inversion H.
    constructor.
    econstructor 2...
    eapply dect...
  Qed.
  Hint Resolve iterPamSam.

  Lemma evalPamSam : forall (t : R.term) (ds : trace), PAM.eval t ds -> eval t ds.
  Proof with eauto.
    intros t v H; inversion_clear H; constructor...
  Qed.
  Hint Resolve evalPamSam.

  Module P := Red_PropT R RS.
  Module LP := Lang_PropT R.

  Lemma temp : forall t c d (PT : PAM.dec t c d) ds (T : dec t c ds), gather d ds.
  Proof with eauto.
    induction 1 using PAM.dec_Ind with
    (P := fun t c d (PT : PAM.dec t c d) => forall ds (T : dec t c ds), gather d ds)
    (P0:= fun v c d (PV : PAM.decctx v c d) => forall ds (V : decctx v c ds), gather d ds); intros; simpl in *; auto;
    try (inversion T; unfold dec_term in H; unfold PAM.dec_term in e; rewrite H in e; inversion e; subst; eauto);
    try(inversion V; unfold dec_context in H2; unfold PAM.dec_context in e; rewrite H2 in e; inversion e; subst; eauto);
    inversion V; subst...
  Qed.

  Lemma decSamPam : forall (t : R.term) (c : R.context) (ds : trace),
    dec t c ds -> forall (d : R.decomp), PAM.dec t c d -> PAM.gather d ds.
  Proof with eauto.
    cofix DT; intros.
    apply (temp _ _ _ H0) in H.
    inversion H; subst.
    constructor.
    destruct (P.dec_total (R.plug t0 c0)) as [d0 PD].
    inversion_clear PD; apply RS.RS.dec_plug in H3; rewrite <- LP.compose_empty in H3; apply PAM.dec_id_l in H3.
    econstructor 2...
  Qed.
  Hint Resolve decSamPam.

  Lemma evalSamPam : forall (t : R.term) (ds : trace), eval t ds -> PAM.eval t ds.
  Proof with eauto.
    intros t v H; inversion_clear H; destruct (P.dec_total t) as [d H]; inversion_clear H; econstructor...
  Qed.
  Hint Resolve evalSamPam.

  Theorem evalSam : forall (t : R.term) (ds : trace), RS.RS.eval t ds <-> eval t ds.
  Proof with auto.
    intros t v; rewrite PAM.evalPam; split; intros...
  Qed.

End StagedAbstractMachineT.

Module EvalApplyMachineT (R : RED_LANG) (RS : RED_REF_SEM_T R) <: EVAL_APPLY_MACHINE_T R.

  Module SAM := StagedAbstractMachineT R RS.

  Definition dec_term := RS.dec_term.
  Definition dec_context := RS.dec_context.
  Definition dec_term_value := RS.dec_term_value.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.
  Definition trace := stream R.decomp.

  CoInductive dec : R.term -> R.context -> trace -> Prop :=
  | d_d_r  : forall (t t0 : R.term) (c : R.context) (r : R.redex) (ds : trace),
               dec_term t = R.in_red r -> R.contract r = Some t0 ->
               dec t0 c ds -> dec t c (s_cons (R.d_red r c) ds)
  | d_v    : forall (t : R.term) (c : R.context) (v : R.value) (ds : trace),
               dec_term t = R.in_val v -> decctx v c ds -> dec t c ds
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (ds : trace),
               dec_term t = R.in_term t0 ec -> dec t0 (ec :: c) ds -> dec t c ds
  with decctx : R.value -> R.context -> trace -> Prop :=
  | dc_val : forall (v : R.value), decctx v R.empty (s_cons (R.d_val v) s_nil)
  | dc_red : forall (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex) (t : R.term) (ds : trace),
               dec_context ec v = R.in_red r -> R.contract r = Some t ->
               dec t c ds -> decctx v (ec :: c) (s_cons (R.d_red r c) ds)
  | dc_rec : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (ds : trace),
               dec_context ec v = R.in_val v0 -> decctx v0 c ds -> decctx v (ec :: c) ds
  | dc_trm : forall (v v0 : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term) (ds : trace),
               dec_context ec v = R.in_term t ec0 -> dec t (ec0 :: c) ds -> decctx v (ec :: c) ds.

(*  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.*)

  CoInductive eval : R.term -> trace -> Prop :=
  | e_intro : forall (t : R.term) (ds : trace), dec t R.empty ds -> eval t ds.

  Lemma decSamEam : forall (t : R.term) (c : R.context) (ds : trace), SAM.dec t c ds -> dec t c ds.
  Proof with eauto.
    refine (cofix DT t c ds ST : dec t c ds := _
    with DV v c ds (SV : SAM.decctx v c ds) : decctx v c ds := _
    for DT).
    inversion ST; subst.
    inversion H0; econstructor...
    econstructor...
    econstructor 3...
    inversion SV; subst.
    inversion H; constructor.
    inversion H0; econstructor...
    econstructor...
    econstructor 4...
  Qed.

  Lemma evalSamEam : forall (t : R.term) (ds : trace), SAM.eval t ds -> eval t ds.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decSamEam; auto.
  Qed.
  Hint Resolve evalSamEam.

  Lemma decEamSam : forall (t : R.term) (c : R.context) (ds : trace), dec t c ds -> SAM.dec t c ds.
  Proof with eauto.
    refine (cofix DT t c ds ET : SAM.dec t c ds := _
    with DV v c ds (EV : decctx v c ds) : SAM.decctx v c ds := _
    for DT).
    inversion ET; subst.
    econstructor...
    econstructor...
    econstructor 2...
    econstructor 3...
    inversion EV; subst.
    repeat constructor.
    econstructor... econstructor...
    econstructor 3...
    econstructor 4...
  Qed.
  Hint Resolve decEamSam.

  Lemma evalEamSam : forall (t : R.term) (ds : trace), eval t ds -> SAM.eval t ds.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamSam; auto.
  Qed.
  Hint Resolve evalEamSam.

  Theorem evalEam : forall (t : R.term) (ds : trace), RS.RS.eval t ds <-> eval t ds.
  Proof with auto.
    intros t v; rewrite SAM.evalSam; split...
  Qed.

End EvalApplyMachineT.

Module ProperEAMachineT (R : RED_LANG) (RS : RED_REF_SEM_T R) <: PROPER_EA_MACHINE_T R.

  Module EAM := EvalApplyMachineT R RS.

  Definition dec_term := RS.dec_term.
  Definition dec_context := RS.dec_context.
  Definition dec_term_value := RS.dec_term_value.

  Definition dec_term_correct := RS.dec_term_correct.
  Definition dec_context_correct := RS.dec_context_correct.
    
  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_apply : R.context -> R.value -> configuration
  | c_final : R.value -> configuration.

  Notation " <<i t >> " := (c_init t) : eam_scope.
  Notation " <<e t , E >> " := (c_eval t E) : eam_scope.
  Notation " <<a E , v >> " := (c_apply E v) : eam_scope.
  Notation " <<f v >> " := (c_final v) : eam_scope.
  Open Scope eam_scope.
  Reserved Notation " a |> d ↑ b " (at level 40).
  Notation " [] " := R.empty.


  Inductive transition : configuration -> configuration -> option R.decomp -> Prop :=
  | t_init : forall t,
               <<i t>> |> <<e t, []>> ↑ None
  | t_red  : forall t t0 E r,
               dec_term t = R.in_red r -> R.contract r = Some t0 ->
               <<e t, E>> |> <<e t0, E>> ↑ Some (R.d_red r E)
  | t_val  : forall t v E,
      	       dec_term t = R.in_val v -> 
               <<e t, E>> |> <<a E, v>> ↑ None
  | t_term : forall t t0 f E,
               dec_term t = R.in_term t0 f ->
               <<e t, E>> |> <<e t0, f::E>> ↑ None
  | t_cfin : forall v,
               <<a [], v>> |> <<f v>> ↑ Some (R.d_val v)
  | t_cred : forall v t f E r,
               dec_context f v = R.in_red r -> R.contract r = Some t ->
               <<a f::E, v>> |> <<e t, E>> ↑ Some (R.d_red r E)
  | t_cval : forall v v0 f E,
               dec_context f v = R.in_val v0 ->
               <<a f::E, v>> |> <<a E, v0>> ↑ None
  | t_cterm: forall v t f f0 E,
               dec_context f v = R.in_term t f0 ->
               <<a f::E, v>> |> <<e t, f0::E>> ↑ None
  where " c1 |> c2 ↑ d " := (transition c1 c2 d).

  Module AM : ABSTRACT_MACHINE_T
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition decomp := R.decomp
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := R.term.
    Definition value := R.value.
    Definition configuration := configuration.
    Definition decomp := R.decomp.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.
    Definition trace := stream decomp.

  Notation " a >>= b " := (match a with
  | None => b
  | Some c => s_cons c b
  end) (at level 40).

  CoInductive trace_m : configuration -> trace -> Prop :=
  | empty_trace : forall v : value, trace_m (c_final v) s_nil
  | trace_trans : forall (c0 c1 : configuration) (od : option decomp) (ds : trace), transition c0 c1 od -> trace_m c1 ds -> trace_m c0 (od >>= ds).
(*  CoInductive trace_m : configuration -> list decomp -> Prop :=
  | empty_trace : forall v : value, trace_m (c_final v) nil
  | trace_trans : forall (c0 c1 : configuration) (od : option decomp) (ds : list decomp), transition c0 c1 od -> trace_m c1 ds -> trace_m c0 (opt_to_list od ++ ds).*)

  CoInductive eval : term -> trace -> Prop :=
  | e_intro : forall (t : term) (ds : trace), trace_m (c_init t) ds -> eval t ds.

  End AM.
  Import AM.

  Notation " a >>= b " := (match a with
  | None => b
  | Some c => s_cons c b
  end) (at level 40).

  Lemma decEamTrans : forall (t:R.term) (c : R.context) (ds : trace),
                        EAM.dec t c ds -> trace_m (c_eval t c) ds.
  Proof with eauto.
    refine (cofix DT t c ds ET : trace_m (c_eval t c) ds := _
    with DV v c ds (EV : EAM.decctx v c ds) : trace_m (c_apply c v) ds := _
    for DT).
    inversion ET; subst.
    change (trace_m (c_eval t c) (Some (R.d_red r c) >>= ds0)); econstructor...
    constructor...
    change (trace_m (c_eval t c) (None >>= ds)); econstructor...
    constructor...
    change (trace_m (c_eval t c) (None >>= ds)); econstructor...
    constructor...
    inversion EV; subst; clear EV.
    change (trace_m (c_apply (R.empty) v) (Some (R.d_val v) >>= s_nil)); econstructor...
    constructor...
    constructor.
    change (trace_m (c_apply (ec::c0) v) (Some (R.d_red r c0) >>=ds0)); econstructor...
    constructor...
    change (trace_m (c_apply (ec::c0) v) (None >>= ds)); econstructor 2...
    econstructor 7...
    change (trace_m (c_apply (ec::c0) v) (None >>= ds)); econstructor...
    constructor 8...
  Qed.
  Hint Resolve decEamTrans.

  Lemma evalEamMachine : forall (t : R.term) (ds : trace), EAM.eval t ds -> AM.eval t ds.
  Proof with eauto.
    intros t ds H; inversion_clear H; constructor.
    change (trace_m (c_init t) (None >>= ds)); econstructor...
    constructor...
  Qed.
  Hint Resolve evalEamMachine.

  Lemma transDecEam : forall (t : R.term) (c : R.context) (ds : trace),
    AM.trace_m (c_eval t c) ds -> EAM.dec t c ds.
  Proof with eauto.
    refine (cofix DT t c ds TE : EAM.dec t c ds := _
    with DV v c ds (TV : trace_m (c_apply c v) ds) : EAM.decctx v c ds := _
    for DT).
    inversion TE; inversion H; subst; simpl.
    econstructor...
    econstructor...
    econstructor 3...
    inversion TV; inversion H; subst; simpl.
    inversion H0; subst. constructor.
    inversion H1.
    econstructor...
    econstructor...
    econstructor 4...
  Qed.
  Hint Resolve transDecEam.

  Lemma evalMachineEam : forall (t : R.term) (ds : trace), AM.eval t ds -> EAM.eval t ds.
  Proof with eauto.
    intros t ds H; inversion_clear H; constructor; inversion_clear H0; inversion H; subst...
  Qed.
  Hint Resolve evalMachineEam.

  Theorem eval_apply_correct : forall (t : R.term) (ds : trace), RS.RS.eval t ds <-> AM.eval t ds.
  Proof with auto.
    intros t v; rewrite EAM.evalEam; split...
  Qed.

End ProperEAMachineT.

Module PushEnterMachineT (R : RED_LANG) (PRS : PE_REF_SEM_T R) <: PUSH_ENTER_MACHINE_T R.

  Module EAM := EvalApplyMachineT R PRS.Red_Sem.

  Definition dec_term := PRS.Red_Sem.dec_term.
  Definition dec_context := PRS.Red_Sem.dec_context.
  Definition dec_term_value := PRS.Red_Sem.dec_term_value.
  Definition dec_context_not_val := PRS.dec_context_not_val.
  Definition dec_context_correct := PRS.Red_Sem.dec_context_correct.
  Definition dec_term_correct := PRS.Red_Sem.dec_term_correct.
  Definition trace := stream R.decomp.

  CoInductive dec : R.term -> R.context -> trace -> Prop :=
  | dec_r    : forall (t t0 : R.term) (c : R.context) (r : R.redex) (ds : trace),
                 dec_term t = R.in_red r -> R.contract r = Some t0 ->
                 dec t0 c ds -> dec t c (s_cons (R.d_red r c) ds)
  | dec_val  : forall (t : R.term) (v : R.value),
                 dec_term t = R.in_val v -> dec t R.empty (s_cons (R.d_val v) s_nil)
  | dec_v_t  : forall (t t0 : R.term) (ec ec0 : R.elem_context) (c : R.context) (v : R.value) (ds : trace),
                 dec_term t = R.in_val v -> dec_context ec v = R.in_term t0 ec0 ->
                 dec t0 (ec0 :: c) ds -> dec t (ec :: c) ds
  | dec_red  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value) (r : R.redex) (ds : trace),
                 dec_term t = R.in_val v -> dec_context ec v = R.in_red r ->
                 R.contract r = Some t0 -> dec t0 c ds -> dec t (ec :: c) (s_cons (R.d_red r c) ds)
  | dec_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (ds : trace),
                 dec_term t = R.in_term t0 ec -> dec t0 (ec :: c) ds -> dec t c ds.

  (*Scheme dec_Ind := Induction for dec Sort Prop.*)

  CoInductive eval : R.term -> trace -> Prop :=
  | e_intro : forall (t : R.term) (ds : trace), dec t R.empty ds -> eval t ds.

  Lemma decEamPem : forall (t : R.term) (c : R.context) (ds : trace), EAM.dec t c ds -> dec t c ds.
  Proof with eauto.
    cofix DT; intros; inversion H; subst.
    econstructor...
    inversion H1; subst.
    econstructor...
    econstructor 4...
    contradiction (dec_context_not_val _ _ _ H2).
    econstructor...
    econstructor 5...
  Qed.

  Lemma evalEamPem : forall (t : R.term) (ds : trace), EAM.eval t ds -> eval t ds.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decEamPem; auto.
  Qed.
  Hint Resolve evalEamPem.

  Lemma decPemEam : forall (t : R.term) (c : R.context) (ds : trace), dec t c ds -> EAM.dec t c ds.
  Proof with eauto.
    cofix DT; intros; inversion H; subst.
    econstructor...
    econstructor 2... econstructor...
    econstructor 2... econstructor 4...
    econstructor... econstructor...
    econstructor 3...
  Qed.

  Lemma evalPemEam : forall (t : R.term) (ds : trace), eval t ds -> EAM.eval t ds.
  Proof.
    intros t v H; inversion_clear H; constructor; apply decPemEam; auto.
  Qed.
  Hint Resolve evalPemEam.

  Theorem evalPem : forall (t : R.term) (ds : trace), PRS.Red_Sem.RS.eval t ds <-> eval t ds.
  Proof.
    intros t v; rewrite EAM.evalEam; split; auto.
  Qed.

End PushEnterMachineT.

Module ProperPEMachineT (R : RED_LANG) (PRS : PE_REF_SEM_T R) <: PROPER_PE_MACHINE_T R.

  Module PEM := PushEnterMachineT R PRS.

  Definition dec_term := PRS.Red_Sem.dec_term.
  Definition dec_context := PRS.Red_Sem.dec_context.
  Definition dec_term_value := PRS.Red_Sem.dec_term_value.
  Definition dec_context_not_val := PRS.dec_context_not_val.
  Definition dec_context_correct := PRS.Red_Sem.dec_context_correct.
  Definition dec_term_correct := PRS.Red_Sem.dec_term_correct.

  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_final : R.value -> configuration.

  Inductive transition : configuration -> configuration -> option R.decomp -> Prop :=
  | t_init : forall (t : R.term), transition (c_init t) (c_eval t R.empty) None
  | t_red  : forall (t t0 : R.term) (c c0 : R.context) (r : R.redex),
               dec_term t = R.in_red r -> R.contract r = Some t0 ->
               transition (c_eval t c) (c_eval t0 c) (Some (R.d_red r c))
  | t_cval : forall (t : R.term) (v : R.value),
               dec_term t = R.in_val v -> transition (c_eval t R.empty) (c_final v) (Some (R.d_val v))
  | t_cred : forall (t t0 : R.term) (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex),
               dec_term t = R.in_val v -> dec_context ec v = R.in_red r ->
               R.contract r = Some t0 -> transition (c_eval t (ec :: c)) (c_eval t0 c) (Some (R.d_red r c))
  | t_crec : forall (t t0 : R.term) (v : R.value) (ec ec0 : R.elem_context) (c : R.context),
               dec_term t = R.in_val v -> dec_context ec v = R.in_term t0 ec0 ->
               transition (c_eval t (ec :: c)) (c_eval t0 (ec0 :: c)) None
  | t_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context), 
               dec_term t = R.in_term t0 ec -> transition (c_eval t c) (c_eval t0 (ec :: c)) None.

  Module AM : ABSTRACT_MACHINE_T
    with Definition decomp := R.decomp
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.
    Definition term := R.term.
    Definition value := R.value.
    Definition decomp := R.decomp.
    Definition configuration := configuration.
    Definition transition := transition.
    Definition c_init := c_init.
    Definition c_final := c_final.
    Definition trace := stream decomp.
  Notation " a >>= b " := (match a with
  | None => b
  | Some c => s_cons c b
  end) (at level 40).

  CoInductive trace_m : configuration -> trace -> Prop :=
  | empty_trace : forall v : value, trace_m (c_final v) s_nil
  | trace_trans : forall (c0 c1 : configuration) (od : option decomp) (ds : trace), transition c0 c1 od -> trace_m c1 ds -> trace_m c0 (od >>= ds).

(*  CoInductive trace_m : configuration -> list decomp -> Prop :=
  | empty_trace : forall v : value, trace_m (c_final v) nil
  | trace_trans : forall (c0 c1 : configuration) (od : option decomp) (ds : list decomp), transition c0 c1 od -> trace_m c1 ds -> trace_m c0 (opt_to_list od ++ ds).*)

  CoInductive eval : term -> trace -> Prop :=
  | e_intro : forall (t : term) (ds : trace), trace_m (c_init t) ds -> eval t ds.

  End AM.
  Import AM.
  Notation " a >>= b " := (match a with
  | None => b
  | Some c => s_cons c b
  end) (at level 40).

  Lemma decPemTrans : forall (t : R.term) (c : R.context) (ds : trace),
    PEM.dec t c ds -> trace_m (c_eval t c) ds.
  Proof with eauto.
    cofix DT; intros; inversion H; subst.
    change (trace_m (c_eval t c) (Some (R.d_red r c) >>= ds0)); econstructor...
    constructor...
    change (trace_m (c_eval t R.empty) (Some (R.d_val v) >>= s_nil)); econstructor...
    constructor...
    constructor...
    change (trace_m (c_eval t (ec :: c0)) (None >>= ds)); econstructor.
    econstructor 5...
    auto.
    change (trace_m (c_eval t (ec :: c0)) (Some (R.d_red r c0) >>= ds0)); econstructor...
    econstructor...
    change (trace_m (c_eval t c) (None >>= ds)); econstructor.
    econstructor 6...
    auto.
  Qed.
  Hint Resolve decPemTrans.

  Lemma evalPemMachine : forall (t : R.term) (ds : trace), PEM.eval t ds -> AM.eval t ds.
  Proof with eauto.
    intros t ds H; inversion_clear H; constructor; change (trace_m (c_init t) (None >>= ds)); econstructor 2...
    constructor.
  Qed.
  Hint Resolve evalPemMachine.

  Lemma transDecPem : forall (t : R.term) (c : R.context) (ds : trace),
    trace_m (c_eval t c) ds -> PEM.dec t c ds.
  Proof with eauto.
    cofix TE; intros; inversion H; inversion H0; subst; simpl.
    econstructor...
    inversion H1.
    econstructor 2...
    inversion H2.
    econstructor 4...
    econstructor...
    econstructor 5...
  Qed.
  Hint Resolve transDecPem.

  Lemma evalMachinePem : forall (t : R.term) (ds : trace), AM.eval t ds -> PEM.eval t ds.
  Proof.
    intros t ds H; constructor; inversion_clear H; inversion H0; subst; inversion H; subst; eauto.
  Qed.
  Hint Resolve evalMachinePem.

  Theorem push_enter_correct : forall (t : R.term) (ds : trace), PRS.Red_Sem.RS.eval t ds <-> AM.eval t ds.
  Proof.
    intros t v; rewrite (PEM.evalPem); split; auto.
  Qed.

End ProperPEMachineT.
