Require Import refocusing_environments_cs.

Module CallByValueRTL <: RED_LANG.

  Inductive term' : Set :=
  | var : nat -> term'
  | lam : nat -> term' -> term'
  | app : term' -> term' -> term'.
  Definition term := term'.

  Inductive closure' : Set :=
  | pair' : term -> list closure' -> closure'
  | comp  : closure' ->  closure' -> closure'.
  Definition closure := closure'.
  Definition env := list closure.
  Definition pair := pair'.

  Inductive value' : Set :=
  | v_lam : nat -> term -> env -> value'.
  Definition value := value'.

  Inductive redex' : Set :=
  | r_beta : value -> value -> redex'
  | r_get  : nat -> env -> redex'
  | r_app  : term -> term -> env -> redex'.
  Definition redex := redex'.

  Inductive frame' : Set :=
  | ap_r : value -> frame'
  | ap_l : closure -> frame'.
  Definition frame := frame'.
  Definition context := list frame.
  Definition empty : context := nil.

  Inductive closureC' : Set :=
  | pairC' : term -> list closureC' -> closureC'.
  Definition closureC := closureC'.
  Definition pairC := pairC'.
  Definition envC := list closureC.

  Inductive valueC' : Set :=
  | v_lamC : nat -> term -> envC -> valueC'.
  Definition valueC := valueC'.

  Inductive frameC' : Set :=
  | ap_rC : valueC -> frameC'
  | ap_lC : closureC -> frameC'.
  Definition frameC := frameC'.
  Definition contextC := list frameC'.
  Definition emptyC : contextC := nil.

  Definition value_to_closure (v : value) : closure :=
    match v with v_lam n t s => pair (lam n t) s end.
  Coercion value_to_closure : value >-> closure.
  Definition redex_to_closure (r : redex) : closure :=
    match r with
      | r_beta v v' => comp (v:closure) (v':closure)
      | r_get n s   => pair (var n) s
      | r_app t1 t2 s => pair (app t1 t2) s
    end.
  Coercion redex_to_closure : redex >-> closure.

  Definition atom_plug (c : closure) (f : frame) :=
    match f with
    | ap_r v => comp c (v : closure)
    | ap_l c0 => comp c0 c
    end.

  Definition plug (c : closure) (E : context) : closure 
    := fold_left atom_plug E c.
  Definition compose (E E0 : context) : context := E ++ E0.
  Definition composeC (E E0 : contextC) : contextC := E ++ E0.

  Definition valueC_to_closureC (v : valueC) : closureC :=
    match v with v_lamC n t s => pairC (lam n t) s end.
  Coercion valueC_to_closureC : valueC >-> closureC.

  Fixpoint closureC_to_closure (cl : closureC) : closure :=
    match cl with pairC t s =>
      pair t (map closureC_to_closure s) end.
  Coercion closureC_to_closure : closureC >-> closure.
  Definition envC_to_env : envC -> env := map closureC_to_closure.

  Definition valueC_to_value (v : valueC) : value :=
    match v with v_lamC n t s => v_lam n t (envC_to_env s) end.

  Definition frameC_to_frame (fC : frameC) : frame :=
    match fC with
      | ap_rC vC => ap_r (valueC_to_value vC)
      | ap_lC cC => ap_l cC
    end.
  Coercion frameC_to_frame : frameC >-> frame.
  Definition contextC_to_context : contextC -> context := map frameC_to_frame.
  Coercion contextC_to_context : contextC >-> context.

  Lemma closureC_ind : forall (P : closureC' -> Prop)
    (PAIR : forall (t : term) (l : list closureC')
      (IN : forall t0, In t0 l -> P t0),
      P (pairC' t l)),
    forall c : closureC', P c.
  Proof with auto.
    intros P h; refine (fix IH (c : closureC') : P c := _);
    destruct c; apply h; induction l; intros; destruct H;
      [rewrite <- H | apply IHl]...
  Qed.

  Lemma closureC_to_closure_injective : forall cl cl0
    (EQC : closureC_to_closure cl = closureC_to_closure cl0),
    cl = cl0.
  Proof with isda.
    induction cl using closureC_ind; destruct cl0; intro; inversion EQC;
      f_equal; subst; clear EQC; generalize dependent l0; induction l;
        destruct l0...
    inversion H1; f_equal...
  Qed.
  Hint Resolve closureC_to_closure_injective : ref.

  Definition envC_to_env_injective : forall sC sC0
    (EQS : envC_to_env sC = envC_to_env sC0), sC = sC0 :=
    map_injective closureC_to_closure closureC_to_closure_injective.
  Hint Resolve envC_to_env_injective : ref.

  Lemma valueC_to_value_injective : forall (v v0 : valueC)
    (EQV : valueC_to_value v = valueC_to_value v0),
    v = v0.
  Proof with auto with ref.
    destruct v; destruct v0; intro H; inversion H; f_equal...
  Qed.
  Hint Resolve valueC_to_value_injective : ref.

  Lemma frameC_to_frame_injective : forall fC fC0
    (EQF : frameC_to_frame fC = frameC_to_frame fC0),
    fC = fC0.
  Proof with auto with ref.
    destruct fC; destruct fC0; intro H; inversion H; f_equal...
  Qed.
  Hint Resolve frameC_to_frame_injective : ref.

  Definition contextC_to_context_injective : forall E E0,
    contextC_to_context E = contextC_to_context E0 -> E = E0 :=
    map_injective frameC_to_frame frameC_to_frame_injective.
  Hint Resolve contextC_to_context_injective : ref.

  Lemma valueC_to_closureC_injective : forall (v v0 : valueC)
    (EQV : valueC_to_closureC v = valueC_to_closureC v0),
    v = v0.
  Proof with auto.
    destruct v; destruct v0; intro H; inversion H; f_equal...
  Qed.
  Hint Resolve valueC_to_closureC : ref.

  Lemma value_to_closure_injective : forall v v0
    (EQV : value_to_closure v = value_to_closure v0),
    v = v0.
  Proof.
    destruct v; destruct v0; intro H; inversion H; f_equal...
  Qed.
  Hint Resolve value_to_closure_injective : ref.
  Lemma redex_to_closure_injective : forall r r0
    (EQR : redex_to_closure r = redex_to_closure r0),
    r = r0.
  Proof.
    destruct r; destruct r0; intro H; inversion H; f_equal; auto with ref.
  Qed.

  Lemma pairC_pair : forall t sC,
    closureC_to_closure (pairC t sC) = pair t (map closureC_to_closure sC).
  Proof. auto. Qed.
  Lemma pairC_injective : forall t t0 sC sC0
    (EQP : pairC t sC = pairC t0 sC0),
    t = t0 /\ sC = sC0.
  Proof. 
    intros t t0 sC sC0 PS; inversion PS; auto.
  Qed.
  Lemma valueC_to_closure_commutes : forall v,
    value_to_closure (valueC_to_value v)
      = closureC_to_closure (valueC_to_closureC v).
  Proof. destruct v; isda. Qed.

  Fixpoint nth_option (s : env) (n : nat) {struct s} : option closure :=
    match s, n with
      | nil, _ => None
      | h::t, O => Some h
      | h::t, S m => nth_option t m
    end.
  
  Fixpoint beta_plus E n s t : (closure * context) :=
    match n, E with
      | 0, ap_r v :: E0 => (pair t ((v:closure) :: s), E0)
      | S m, ap_r v :: E0 => beta_plus E0 m ((v : closure) :: s) t
      | _, _ => (pair (lam n t) s, E)
    end.

  Definition contract (r : redex) (E : context) : option (closure * context) :=
    match r with
      | r_beta (v_lam n t s) v => Some (beta_plus (ap_r v :: E) n s t)
      | r_get x s => match nth_option s x with
                       | Some cl => Some (cl, E)
                       | None => None
                     end
      | r_app t t0 s => Some ((pair t0 s), ap_l (pair t s) :: E)
    end.

  Notation " E '[' c ']' " := (plug c E) (at level 40) : red_scope.
  Notation " E '·' E1 " := (compose E E1) 
    (at level 40, left associativity) : red_scope.
  Notation " E '··' E1 " := (composeC E E1)
    (at level 40, left associativity) : red_scope.
  Notation " f '[' c ']a' " := (atom_plug c f) (at level 40) : red_scope.

  Open Scope red_scope.

  Definition only_empty (c : closure) : Prop := 
    forall c0 E, E[c0] = c -> E = empty.
  Definition only_trivial (c : closure) : Prop := 
    forall c0 E, E[c0] = c -> E = empty \/ exists v, c0 = value_to_closure v.

  Lemma closureC_only_empty : forall cC,
    only_empty (closureC_to_closure cC).
  Proof with isda.
    intros cC c E; generalize dependent c; induction E...
    assert (T := IHE _ H); subst; destruct cC; destruct a; discriminate.
  Qed.
  Lemma value_trivial : forall v : value,
    only_trivial (value_to_closure v).
  Proof with isda.
    intros v c E; generalize dependent c; induction E...
    destruct (IHE _ H) as [H0 | [v0 H0]]; subst; simpl in *;
      match goal with
        [Hdisc : atom_plug ?t ?a = _ ?v |- _ ] => 
          destruct a; destruct v; discriminate Hdisc
      end.
  Qed.
  Lemma redex_trivial : forall r : redex,
    only_trivial (redex_to_closure r).
  Proof with isda; eauto.
    intros r c E; generalize dependent c; induction E...
    right; destruct (IHE _ H) as [H0 | [v0 H0]]; subst; simpl in *;
      match goal with
        [Hinv : atom_plug ?c ?a = _ ?rv |- _ ] => 
          destruct a; destruct rv; inversion Hinv
      end...
  Qed.
  Lemma value_redex : forall (v : value) (r : redex),
    value_to_closure v <> redex_to_closure r.
  Proof.
    destruct v; destruct r; isda.
  Qed.

  Lemma ot_subt : forall c c0 f, 
    only_trivial c -> f[ c0 ]a = c ->
    exists v, c0 = value_to_closure v.
  Proof with isda; eauto.
    intros; destruct (H c0 (f :: nil)) as [H1 | [v H1]]...
  Qed.

  Ltac ot_v c f :=
    match goal with
      | [Hot : (only_trivial ?H1) |- _] => 
          destruct (ot_subt _ c f Hot) as [?v HV]; [auto | subst c]
    end.

  Ltac mlr rv :=
  match goal with
    | [ |- (exists v, ?H1 = value_to_closure v)
        \/ (exists r, ?H1 = redex_to_closure r)] =>
      match rv with
        | (?v : value) => left; exists v
        | (?r : redex) => right; exists r
      end; simpl; auto
  end.

  Lemma trivial_val_red : forall c : closure, only_trivial c ->
    (exists v : value, c = value_to_closure v)
      \/ (exists r : redex, c = redex_to_closure r).
  Proof.
    destruct c; intros.
    destruct t.
    mlr (r_get n l).
    mlr (v_lam n t l).
    mlr (r_app t1 t2 l).
    ot_v c2 (ap_l c1); ot_v c1 (ap_r v); mlr (r_beta v0 v).
  Qed.

  (** Datatype of decompositions -- either a value or a redex in a context (analogous to the decompose lemma) *)
  Inductive decomp : Set :=
  | d_val : value -> decomp
  | d_red : redex -> context -> decomp.

  Inductive interm_dec : Set :=
  | in_red : redex -> interm_dec
  | in_val : value -> interm_dec
  | in_clo : closure -> frame -> interm_dec.

  Definition decomp_to_closure (d : decomp) : closure :=
  match d with
    | d_val v => value_to_closure v
    | d_red r c0 => plug (redex_to_closure r) c0
  end.

  Definition closureC_dec : forall cC : closureC,
    {p : term * envC + valueC | match p with
	| inl (t, sC) => cC = pairC t sC
	| inr vC => cC = valueC_to_closureC vC
    end}.
  Proof with auto.
    destruct cC as [t sC]; exists (inl _ (t, sC))...
  Defined.
  Lemma dec_pairC : forall t sC,
    proj1_sig (closureC_dec (pairC t sC)) = inl _ (t, sC).
  Proof with auto.
    intros; simpl in *...
  Qed.

End CallByValueRTL.

Module CBV_Prop <: LANG_PROP CallByValueRTL := Lang_Prop CallByValueRTL.

Module CallByValue_Eval <: RED_SEM CallByValueRTL.
  Import CallByValueRTL.
  Module P := CBV_Prop.
  Import P.
  Open Scope red_scope.

  Inductive dec' : closure -> context -> decomp -> Prop :=
  | dec_var : forall n s E,
      dec' (pair (var n) s) E (d_red (r_get n s) E)
  | dec_val : forall v E d
      (DEC : decctx E v d),
      dec' (v : closure) E d
  | dec_app : forall t0 t1 s E,
      dec' (pair (app t0 t1) s) E (d_red (r_app t0 t1 s) E)
  | dec_cmp : forall c0 c1 E d
      (DEC : dec' c1 (ap_l c0 :: E) d),
      dec' (comp c0 c1) E d
  with decctx : context -> value -> decomp -> Prop :=
  | dec_emp : forall v,
      decctx empty v (d_val v)
  | dec_apL : forall cl E v d
      (DEC : dec' cl (ap_r v :: E) d),
      decctx (ap_l cl :: E) v d
  | dec_apR : forall v v0 E,
      decctx (ap_r v :: E) v0 (d_red (r_beta v0 v) E).

  Definition dec := dec'.
  Scheme dec_Ind := Induction for dec' Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive decempty : closure -> decomp -> Prop :=
  | d_intro : forall (c : closure) (d : decomp) 
      (DEC : dec c empty d),
      decempty c d.

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall v,
      iter (d_val v) v
  | i_red : forall r c E E0 d v
      (CTR : contract r E = Some (c, E0))
      (DEC : decempty (E0 [c]) d)
      (ITR : iter d v),
      iter (d_red r E) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t d v
      (DEC : decempty (pair t nil) d)
      (ITR : iter d v),
      eval t v.

  Hint Constructors dec' decctx decempty iter eval.
  Hint Unfold dec.

  (** A redex in context will only ever be reduced to itself *)
  Lemma dec_redex_self : forall (r : redex) (c : context),
    dec (redex_to_closure r) c (d_red r c).
  Proof. destruct r; repeat constructor. Qed.

  Lemma decompose : forall c : closure,
    (exists v : value, c = v) \/
    (exists r : redex, exists E :context, c = E [ r ]).
  Proof with isda.
    induction c; try destruct t...
    right; exists (r_get n l); exists empty...
    left;  exists (v_lam n t l)...
    right; exists (r_app t1 t2 l); exists empty...
    destruct IHc2 as [[v0 Hv0] | [r [E HrE]]]; subst.
    destruct IHc1 as [[v Hv] | [r [E HrE]]]; subst.
    right; exists (r_beta v v0); exists empty...
    right; exists r; exists (E · (ap_r v0 :: nil)); rewrite plug_compose...
    right; exists r; exists (E · (ap_l c1 :: nil)); rewrite plug_compose...
  Qed.

  (** dec is left inverse of plug *)
  Lemma dec_correct : forall c E d, dec c E d -> decomp_to_closure d = E [c].
  Proof with isda.
    induction 1 using dec_Ind with
      (P := fun c E d (DEC : dec c E d) =>
        decomp_to_closure d = E [c])
      (P0:= fun E v d (DECX : decctx E v d) =>
        decomp_to_closure d = E [v])...
  Qed.

  Lemma dec_plug : forall E E0 c d
    (DEC : dec (E [c]) E0 d),
    dec c (E · E0) d.
  Proof with isda.
    induction E...
    apply IHE in DEC; destruct a...
    inversion DEC; subst; try destruct v0...
    inversion DEC0; subst; try destruct v...
    inversion DEC1; try destruct v; subst; inversion H0; subst...
    inversion DEC; auto; destruct v; inversion H1; subst...
  Qed.

  Lemma dec_plug_rev : forall E E0 c d
    (DEC : dec c (E · E0) d),
    dec (E [c]) E0 d.
  Proof with isda; auto 6.
    induction E; try destruct a...
  Qed.

End CallByValue_Eval.

Module CallByValue_Ref <: RED_REF_LANG.

  Module Lang := CallByValueRTL.
  Import Lang.

  Definition dec_closure (cl : closure) : interm_dec :=
    match cl with
      | pair (lam n t) s => in_val (v_lam n t s)
      | pair (var n) s => in_red (r_get n s)
      | pair (app t t0) s => in_red (r_app t t0 s)
      | comp cl0 cl1 => in_clo cl1 (ap_l cl0)
    end.

  Definition dec_context (f : frame) (v : value) : interm_dec :=
    match f with
      | ap_l cl => in_clo cl (ap_r v)
      | ap_r v0 => in_red (r_beta v v0)
    end.

  Inductive subclosure_one_step : closure -> closure -> Prop :=
  | scl : forall cl cl0 f
    (AP : cl = atom_plug cl0 f),
    subclosure_one_step cl0 cl.
  Lemma subclosure_one_step_wf : well_founded subclosure_one_step.
  Proof. prove_st_wf. Qed.

  Definition closure_order : closure -> closure -> Prop 
    := clos_trans_n1 _ subclosure_one_step.
  Notation " cl <| cl0 " := (closure_order cl cl0) (at level 40) : red_scope.
  Definition closure_order_wf : well_founded closure_order
    := wf_clos_trans_r _ _ subclosure_one_step_wf.

  Definition frame_order (f f0 : frame) : Prop :=
    match f, f0 with
      | ap_r _, ap_l _ => True
      | _, _ => False
    end.
  Notation " f <: f0 " := (frame_order f f0) (at level 40) : red_scope.
  Lemma frame_order_wf : well_founded frame_order.
  Proof. prove_ec_wf. Qed.

  Open Scope red_scope.

  Lemma dec_closure_red_empty  : forall c r
    (DCL : dec_closure c = in_red r),
    only_empty c.
  Proof with isda.
    destruct c; intros r H; try discriminate; destruct t; inversion H;
      subst; clear H; intros c E H; generalize dependent c; induction E;
        isda; assert (ht := IHE _ H); subst; destruct a...
  Qed.
  Lemma dec_closure_val_empty  : forall c v
    (DCL : dec_closure c = in_val v),
    only_empty c.
  Proof with isda.
    destruct c; intros r H; try discriminate; destruct t; inversion H;
      subst; clear H; intros c E H; generalize dependent c; induction E...
    assert (ht := IHE _ H); subst; destruct a...
  Qed.
  Lemma dec_closure_clo_top    : forall c c0 f
    (DCL : dec_closure c = in_clo c0 f),
    forall f0, ~f <: f0.
  Proof.
    destruct c; try destruct t; intros; inversion DCL; subst; isda.
  Qed.
  Lemma dec_context_red_bot    : forall f v r
    (DCT : dec_context f v = in_red r),
    forall f0, ~ f0 <: f.
  Proof.
    destruct f; intros; inversion DCT; subst; destruct f0; isda.
  Qed.
  Lemma dec_context_val_bot    : forall f v v0
    (DCT : dec_context f v = in_val v0),
    forall f0, ~ f0 <: f.
  Proof. destruct f; isda. Qed.
  Lemma dec_context_clo_next   : forall f f0 v c
    (DCT : dec_context f v = in_clo c f0),
    f0 <: f /\ forall f1, f1 <: f -> ~ f0 <: f1.
  Proof. 
    destruct f; intros; inversion DCT; subst; intuition isda; destruct f1; isda.
  Qed.

  Lemma dec_closure_correct : forall c,
    match dec_closure c with
      | in_red r => redex_to_closure r = c
      | in_val v => value_to_closure v = c
      | in_clo c0 f0 => f0[ c0 ]a = c
    end.
  Proof with isda.
    destruct c; try destruct t...
  Qed.
  Lemma dec_context_correct : forall f v,
    match dec_context f v with
      | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
      | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
      | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
    end.
  Proof.
    destruct f; isda.
  Qed.

  Lemma frame_order_antisym : forall f f0, f <: f0 -> ~ f0 <: f.
  Proof.
    destruct f; destruct f0; isda.
  Qed.
  Lemma dec_frame_ord : forall c c0 f f0, 
    f[ c ]a = f0 [c0]a ->
    f <: f0 \/ f0 <: f \/ (c = c0 /\ f = f0).
  Proof.
    destruct f; destruct f0; intros; inversion H; isda;
      apply value_to_closure_injective in H2; subst; isda. 
  Qed.
  Lemma frame_det : forall c c0 f f0,
    f <: f0 -> f[ c ]a = f0[ c0 ]a ->
    exists v, c0 = value_to_closure v.
  Proof.
    destruct f; destruct f0; intros; inversion H; inversion H0; subst; eauto.
  Qed.

  Lemma getC : forall l i r,
    nth_option (map closureC_to_closure l) i = Some r ->
    {c:closureC | r = closureC_to_closure c}.
  Proof.
    induction l; induction i; simpl; intros; try discriminate.
    split with a; congruence.
    eapply IHl; eapply H.
  Qed.

  Definition eqP cE cEC : Prop :=
    match cE, cEC with
      (cl, E), (clC, EC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
    end.

  Lemma betaC : forall n EC sC t c E
    (BETA : beta_plus (contextC_to_context EC) n (envC_to_env sC) t = (c, E)),
    {p : closureC * contextC | eqP (c, E) p}.
  Proof with isda.
    induction n; destruct EC; try destruct f; intros; inversion BETA; subst.
    exists (pairC (lam 0 t) sC, emptyC)...
    exists (pairC t ((v : closureC) :: sC), EC);
      rewrite valueC_to_closure_commutes...
    exists (pairC (lam 0 t) sC, ap_lC c :: EC)...
    exists (pairC (lam (S n) t) sC, emptyC)...
    rewrite H0; rewrite valueC_to_closure_commutes in H0; 
      replace (((v : closureC) : closure) :: envC_to_env sC) with 
        (envC_to_env ((v : closureC) :: sC)) in H0 by auto.
    destruct (IHn _ _ _ _ _ H0) as [[cC EC0] [EQC EQE]]; eauto.
    exists (pairC (lam (S n) t) sC, ap_lC c :: EC)...    
  Qed.

  Definition closure_red : forall cC r EC cl E
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Proof with isda.
    destruct cC; destruct t; intros; inversion DCL; subst; inversion CTR; subst.
    fold envC_to_env in H0; remember (nth_option (envC_to_env l) n) as nn;
      destruct nn; inversion H0; subst; symmetry in Heqnn;
    destruct (getC _ _ _ Heqnn) as [cC EQCC]; subst; exists (cC, EC)...
    exists (pairC t2 l,  (ap_lC (pairC t1 l)) :: EC)...
  Defined.
  Definition context_red : forall fC vC r EC cl E
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Proof with isda.
    destruct fC; intros; inversion DCT; subst; destruct vC; inversion CTR; subst.
    destruct n; isda; eauto.
    inversion H0; subst; clear H0.
    exists (pairC t ((v : closureC) :: e), EC); 
      rewrite valueC_to_closure_commutes...
    rewrite H0; eapply betaC with (sC := (v : closureC) :: e);
      rewrite valueC_to_closure_commutes in H0; eauto.
  Defined.
  Definition closure_val : forall cC v
    (DCL : dec_closure (closureC_to_closure cC) = in_val v),
    {vC : valueC | v = valueC_to_value vC}.
  Proof with isda.
    destruct cC as [t sC]; destruct t; intros; inversion DCL; 
      subst; exists (v_lamC n t sC)...
  Defined.
  Definition context_val : forall fC vC v
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Proof with isda.
    destruct fC...
  Defined.
  Definition context_clo : forall fC vC cl f
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    {p : closureC * frameC |
      match p with 
        (cC, fC) => cl = closureC_to_closure cC /\ f = frameC_to_frame fC
      end}.
  Proof with isda.
    destruct fC; intros; inversion DCT; subst; exists (c, ap_rC vC)...
  Defined.

  Close Scope red_scope.

End CallByValue_Ref.

Module CBV_RS <: RED_REF_SEM CallByValueRTL := RedRefSem CallByValue_Ref.

Section Equivalence.

  Import CallByValueRTL.

  Lemma dec_equiv : forall c E d,
    CallByValue_Eval.dec c E d <-> CBV_RS.dec c E d.
  Proof with isda.
    split...
    induction H using CallByValue_Eval.dec_Ind with
      (P := fun c E d (DEC : CallByValue_Eval.dec c E d) =>
        CBV_RS.dec c E d)
      (P0:= fun E v d (DEC : CallByValue_Eval.decctx E v d) =>
        CBV_RS.decctx E v d)...
    destruct v; econstructor...
    econstructor 3...
    econstructor 4...
    induction H using CBV_RS.dec_Ind with
      (P := fun c E d (DEC : CBV_RS.dec c E d) =>
        CallByValue_Eval.dec c E d)
      (P0:= fun E v d (DEC : CBV_RS.decctx E v d) =>
        CallByValue_Eval.decctx E v d);
      match goal with
        | [ DCL : CBV_RS.dec_closure ?c = ?int |- _ ] => 
            destruct c; try destruct t; inversion DCL; subst
        | [ DCT : CBV_RS.dec_context ?f ?v = ?int |- _ ] =>
          destruct f; inversion DCT; subst
        | [ |- _ ] => idtac
      end...
    cutrewrite ((pair' (lam n t) l : closure) = (v_lam n t l : value)); auto.
  Qed.

  Lemma iter_equiv : forall d v,
    CallByValue_Eval.iter d v <-> CBV_RS.RS.iter d v.
  Proof with isda.
    split; intro H; induction H; econstructor; eauto; constructor;
      inversion_clear DEC; [rewrite <- dec_equiv | rewrite dec_equiv]...
  Qed.

  Lemma eval_equiv : forall t v,
    CallByValue_Eval.eval t v <-> CBV_RS.RS.eval t v.
  Proof with isda.
    split; intro H; inversion_clear H; inversion_clear DEC;
      constructor 1 with d; [ constructor; rewrite <- dec_equiv
        | rewrite <- iter_equiv | constructor; rewrite dec_equiv
        | rewrite iter_equiv]...
  Qed.

End Equivalence.

Module PE_CBV_RS <: PE_REF_SEM CallByValueRTL.

  Module Red_Sem := CBV_RS.
  Import CallByValueRTL.

  Lemma dec_context_not_val : forall v v0 ec,
    ~(Red_Sem.dec_context ec v = in_val v0).
  Proof.
    destruct ec; isda.
  Qed.
  Lemma dec_closure_value : forall v,
    Red_Sem.dec_closure (value_to_closure v) = in_val v.
  Proof.
    destruct v; isda.
  Qed.
  Lemma closureC_dec_not_right : forall cC p,
    ~(proj1_sig (closureC_dec cC) = inr _ p).
  Proof.
    destruct cC; isda.
  Qed.

End PE_CBV_RS.

Module CBV_PEM <: PROPER_PE_MACHINE CallByValueRTL
  := ProperPEMachine CallByValueRTL PE_CBV_RS.

Module Zinc <: ABSTRACT_MACHINE.

  Import CallByValueRTL.
  Module P := CBV_Prop.
  Import P.
  Import CBV_PEM.
  Open Scope red_scope.
  Open Scope pem_scope.

  Definition term := term.
  Definition value := valueC.
  Definition configuration := configuration.
  Definition c_init := c_init.
  Definition c_final := c_final.

  Reserved Notation " c '|>>' c0 " (at level 70, no associativity).

  Inductive transition' : configuration -> configuration -> Prop :=
  | t_init : forall t,
      <<i t >> |>> << t, nil, emptyC >>
  | t_val  : forall n t sC,
      << lam n t, sC, emptyC >> |>> <<f v_lamC n t sC >>
  | t_apR  : forall n t t0 sC sC0 vC EC EC0
      (BETA: beta_plus (contextC_to_context (ap_rC vC :: EC)) n (envC_to_env sC) t
        = (closureC_to_closure (pairC t0 sC0), contextC_to_context EC0)),
      << lam n t, sC, ap_rC vC :: EC >> |>> << t0, sC0, EC0 >>
  | t_apL  : forall n t t0 sC sC0 EC,
      << lam n t, sC, ap_lC (pairC t0 sC0) :: EC >> |>> 
        << t0, sC0, ap_rC (v_lamC n t sC) :: EC >>
  | t_var  : forall n sC sC0 t0 EC
      (GET : nth_option (envC_to_env sC) n 
        = Some (closureC_to_closure (pairC t0 sC0))),
      << var n, sC, EC >> |>> << t0, sC0, EC >>
  | t_app  : forall t0 t1 sC EC,
      << app t0 t1, sC, EC >> |>> << t1, sC, ap_lC (pairC t0 sC) :: EC >>

  where " c '|>>' c0 " := (transition' c c0).

  Definition transition := transition'.
  Definition trans_close := clos_trans_1n _ transition.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value),
      trans_close (c_init t) (c_final v) -> eval t v.
  
  Hint Constructors transition' eval clos_trans_1n.
  Hint Unfold transition trans_close.
  Notation " c |>>+ c0 " := (trans_close c c0) (at level 70, no associativity).
    
  Lemma trans_pem_zinc : forall c c0, c |> c0 -> c |>> c0.
  Proof with isda.
    intros; inversion H; auto; try unfold dec_closure in DCL;
      try unfold dec_context in DCT.
    (* red *)
    remember (closure_red _ _ _ _ _ DCL CTR) as UN2; clear HeqUN2;
      destruct UN2 as [[cc EE] [EQC EQE]]; simpl in *; inversion UNF; subst;
        clear UNF; destruct t; inversion DCL; subst...
      (* var *)
    fold envC_to_env in CTR; remember (nth_option (envC_to_env sC) n) as nn;
      symmetry in Heqnn; destruct nn; inversion CTR.
    destruct (CallByValue_Ref.getC _ _ _ Heqnn) as [ccC HcC];
      destruct ccC; apply contextC_to_context_injective in H2; subst...
      (* app *)
    inversion CTR; subst.
    change (contextC_to_context (ap_lC (pairC t1 sC) :: EC) 
      = contextC_to_context EC0) in H3; apply envC_to_env_injective in H2;
    apply contextC_to_context_injective in H3; subst...
    (* val *)
    remember (closure_val _ _ DCL) as clv; clear Heqclv; 
      destruct clv as [vC0 HUNF]; destruct t; inversion DCL; isda; subst...
    change (valueC_to_value (v_lamC n t sC) = valueC_to_value vC) in H3;
      apply valueC_to_value_injective in H3; subst...
    (* beta *)
    remember (closure_val _ _ DCL) as clv; clear Heqclv; 
      destruct clv as [vC0 HUNF]; destruct t; inversion DCL; isda; subst...
    change (valueC_to_value (v_lamC n t sC) = valueC_to_value vC) in H3;
      clear DCL; apply valueC_to_value_injective in H3; subst...
    change (dec_context fC (valueC_to_value (v_lamC n t sC)) = in_red r) in DCT.
    remember (context_red _ _ _ _ _ _ DCT CTR) as ctr; clear Heqctr;
      destruct ctr as [[ccC EEC] [EQC EQE]]; inversion UNC; clear UNC; subst...
    destruct fC; inversion DCT; subst; isda; inversion CTR...
    (* ap_l *)
    remember (closure_val _ _ DCL) as clv; clear Heqclv; 
      destruct clv as [vC0 HUNF]; destruct t; inversion DCL; isda; subst...
    change (valueC_to_value (v_lamC n t sC) = valueC_to_value vC) in H3;
      clear DCL; apply valueC_to_value_injective in H3; subst...
    change (dec_context fC (valueC_to_value (v_lamC n t sC)) = in_clo c1 f)
      in DCT; remember (context_clo _ _ _ _ DCT) as ctc; clear Heqctc;
        destruct ctc as [[ccC ff] [H_cl H_f]]; destruct fC; inversion DCT;
          inversion UNC; subst...
    replace (ap_r (v_lam n t (envC_to_env sC))) with 
      (frameC_to_frame (ap_rC (v_lamC n t sC))) in H_f by auto;
        apply frameC_to_frame_injective in H_f; subst.
    fold envC_to_env in H_cl; replace (pair t0 (envC_to_env sC0)) with
      (closureC_to_closure (pairC t0 sC0)) in H_cl by auto; 
        apply closureC_to_closure_injective in H_cl; subst...
  Qed.

  Lemma trans_zinc_pem : forall c c0, c |>> c0 -> c |> c0.
  Proof with isda.
    intros; inversion H; auto.
    (* val *)
    assert (DCL : dec_closure (closureC_to_closure (pairC (lam n t) sC))
      = in_val (valueC_to_value (v_lamC n t sC))) by auto.
    eapply t_cval with (DCL := DCL);
      destruct (closure_val (pairC (lam n t) sC) _ DCL) as [vC HUNF]; simpl;
        apply valueC_to_value_injective in HUNF...
    (* beta *)
    assert (DCL : dec_closure (closureC_to_closure (pairC (lam n t) sC))
      = in_val (valueC_to_value (v_lamC n t sC))) by auto.
    assert (DCT : dec_context (frameC_to_frame (ap_rC vC))
      (valueC_to_value (v_lamC n t sC)) = in_red (r_beta 
        (valueC_to_value (v_lamC n t sC)) (valueC_to_value vC))) by auto.
    assert (CTR : contract (r_beta (valueC_to_value (v_lamC n t sC))
      (valueC_to_value vC)) (contextC_to_context EC)
        = Some (closureC_to_closure (pairC t0 sC0), contextC_to_context EC0)).
    rewrite <- BETA; simpl; rewrite valueC_to_closure_commutes; auto.
    eapply t_cred with (DCL := DCL) (DCT := DCT) (CTR := CTR).
    destruct (closure_val (pairC (lam n t) sC) _ DCL) as [vC0 HUNF]; simpl;
      auto using valueC_to_value_injective.
    destruct (context_red (ap_rC vC) _ _ _ _ _ DCT CTR) as [[cC0 EC1] [EQC EQE]]; simpl;
      f_equal; auto using closureC_to_closure_injective,
        contextC_to_context_injective.
    (* ap_l *)
    assert (DCL : dec_closure (closureC_to_closure (pairC (lam n t) sC))
      = in_val (valueC_to_value (v_lamC n t sC))) by auto.
    assert (DCT : dec_context (frameC_to_frame (ap_lC (pairC t0 sC0)))
      (valueC_to_value (v_lamC n t sC)) = in_clo (closureC_to_closure (pairC t0 sC0))
        (frameC_to_frame (ap_rC (v_lamC n t sC)))) by auto.
    eapply t_crec with (DCL := DCL) (DCT := DCT).    
    destruct (closure_val (pairC (lam n t) sC) _ DCL) as [vC0 HUNF]; simpl;
      auto using valueC_to_value_injective.
    destruct (context_clo (ap_lC (pairC t0 sC0)) _ _ _ DCT) as [[ccC ffC] [EQC EQF]]; simpl;
      f_equal; auto using closureC_to_closure_injective, frameC_to_frame_injective.
    (* var *)
    assert (DCL : dec_closure (closureC_to_closure (pairC (var n) sC))
      = in_red (r_get n (envC_to_env sC))) by auto.
    assert (CTR : contract (r_get n (envC_to_env sC)) (contextC_to_context EC)
      = Some (closureC_to_closure (pairC t0 sC0), contextC_to_context EC))
    by (simpl; rewrite GET; auto).
    eapply t_red with (DCL := DCL) (CTR := CTR).
    destruct (closure_red (pairC (var n) sC) _ _ _ _ DCL CTR) as [[cC0 EC0] [EQC EQE]]; simpl;
      f_equal; auto using closureC_to_closure_injective,
        contextC_to_context_injective.
    (* app *)
    assert (DCL : dec_closure (closureC_to_closure (pairC (app t0 t1) sC))
      = in_red (r_app t0 t1 (envC_to_env sC))) by auto.
    assert (CTR : contract (r_app t0 t1 (envC_to_env sC)) (contextC_to_context EC)
      = Some (closureC_to_closure (pairC t1 sC), 
        contextC_to_context (ap_lC (pairC t0 sC) :: EC))) by auto.
    eapply t_red with (DCL := DCL) (CTR := CTR);
      destruct (closure_red (pairC (app t0 t1) sC) _ _ _ _ DCL CTR) as [[cC0 EC0] [EQC EQE]];
        simpl; f_equal; auto using closureC_to_closure_injective,
          contextC_to_context_injective.
  Qed.
 
  Lemma tcl_pem_zinc : forall c c0, c |>+ c0 -> c |>>+ c0.
  Proof.
    induction 1; eauto using trans_pem_zinc.
  Qed.

  Lemma tcl_zinc_pem : forall c c0, c |>>+ c0 -> c |>+ c0.
  Proof.
    induction 1; eauto using trans_zinc_pem.
  Qed.

  Lemma eval_zinc : forall t v,
    AM.eval t v <-> eval t v.
  Proof.
    split; intro H; inversion_clear H; auto using tcl_zinc_pem, tcl_pem_zinc.
  Qed.

  Theorem ZincMachineCorrect : forall t (v : valueC),
    CallByValue_Eval.eval t (valueC_to_value v) <-> eval t v.
  Proof with auto.
    intros; rewrite eval_equiv; rewrite push_enter_correct; apply eval_zinc.
  Qed.

End Zinc.
