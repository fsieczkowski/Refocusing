Require Import refocusing_substitutions.
Require Import Setoid.

Module CallByValue <: RED_LANG.

  Parameter var_name : Set.

  Inductive term' : Set :=
  | var : var_name -> term'
  | lam : var_name -> term' -> term'
  | appl : term' -> term' -> term'.
  Definition term := term'.

  Inductive value' : Set :=
  | v_var : var_name -> value'
  | v_lam : var_name -> term -> value'.
  Definition value := value'.

  Inductive redex' : Set :=
  | beta : value -> value -> redex'.
  Definition redex := redex'.

  Definition value_to_term (v : value) : term :=
  match v with
  | v_var v' => var v'
  | v_lam v' t => lam v' t
  end.
  Coercion value_to_term : value >-> term.

  Lemma value_to_term_injective : forall v v', value_to_term v = value_to_term v' -> v = v'.
  Proof.
    intros v v0; case v; case v0; simpl; intros; try discriminate; injection H;
    intros; subst v1; try subst t; auto.
  Qed.
  Hint Immediate value_to_term_injective.

  Definition redex_to_term (r : redex) : term :=
  match r with
  | beta v v0 => appl (v:term) (v0:term)
  end.
  Coercion redex_to_term : redex >-> term.

  Lemma redex_to_term_injective : forall r r', redex_to_term r = redex_to_term r' -> r = r'.
  Proof with auto.
    intros r r0; case r; case r0; intros; injection H; intros; f_equal...
  Qed.

  Parameter subst : term -> var_name -> term -> term.

  Definition contract (r : redex) : option term :=
  match r with
  | beta (v_lam x t0) v0 => Some (subst t0 x v0)
  | _ => None
  end.

  Inductive elem_context' : Set :=
  | ap_r : term -> elem_context'
  | ap_l : value-> elem_context'.
  Definition elem_context := elem_context'.
  Definition context := list elem_context.
  Definition empty : context := nil.

  Definition compose (c0 c1 : context) : context := app c0 c1.
  Definition atom_plug (t : term) (ec : elem_context) : term :=
  match ec with
  | ap_r t0 => appl t t0
  | ap_l v => appl (v:term) t
  end.
  Definition plug (t : term) (c : context) : term := fold_left atom_plug c t.

  Lemma plug_compose : forall c1 c2 r, plug r (compose c1 c2) = plug (plug r c1) c2.
  Proof (fold_left_app atom_plug).

  Lemma decompose : forall t : term, (exists v : value, t = v) \/
                      (exists r : redex, exists c : context, plug r c = t).
  Proof.
    induction t; simpl; [ left; split with (v_var v) | left; split with (v_lam v t) | right ]; auto.
    destruct IHt1 as [[v1 Hv1] | [r [c Hrc]]]; [ destruct IHt2 as [[v2 Hv2] | [r [c Hrc]]]; [ exists (beta v1 v2);
    exists empty | exists r; exists (compose c (ap_l v1 :: empty))] | exists r; exists (compose c (ap_r t2 :: empty))];
    subst; auto; rewrite plug_compose; auto.
  Qed.

  Inductive decomp : Set :=
  | d_val : value -> decomp
  | d_red : redex -> context -> decomp.

  Inductive interm_dec : Set :=
  | in_red : redex -> interm_dec
  | in_val : value -> interm_dec
  | in_term: term  -> elem_context -> interm_dec.

  Definition decomp_to_term (d : decomp) : term :=
  match d with
  | d_val v => value_to_term v
  | d_red r c0 => plug (redex_to_term r) c0
  end.
  Definition only_empty (t : term) : Prop := forall t' c, plug t' c = t -> c = empty.
  Definition only_trivial (t : term) : Prop := forall t' c, plug t' c = t -> c = empty \/ exists v, t' = value_to_term v.
  Lemma value_trivial : forall v : value, only_trivial (value_to_term v).
  Proof.
    intros v t c; generalize dependent t; induction c; intros; simpl in *; auto; right;
    destruct (IHc _ H) as [H0 | [v0 H0]]; subst; simpl in *; match goal with
    [Hdisc : CallByValue.atom_plug ?t ?a = _ ?v |- _ ] => destruct a; destruct v; discriminate Hdisc end.
  Qed.
  Lemma redex_trivial : forall r : redex, only_trivial (redex_to_term r).
  Proof.
    intros r t c; generalize dependent t; induction c; intros; simpl in *; auto; right;
    destruct (IHc _ H) as [H0 | [v0 H0]]; subst; simpl in *; match goal with
    | [Hdisc : CallByValue.atom_plug ?t ?a = CallByValue.value_to_term ?v |- _ ] => destruct a; destruct v; discriminate Hdisc 
    | [Hred  : CallByValue.atom_plug ?t ?a = CallByValue.redex_to_term ?r |- exists v, ?t = _ v] => destruct a; destruct r; inversion H; subst t
    end; match goal with [ |- exists u, _ ?v = _ u ] => exists v; auto end.
  Qed.
  Lemma value_redex : forall (v : value) (r : redex), value_to_term v <> redex_to_term r.
  Proof.
    intros v r H; destruct v; destruct r; discriminate H.
  Qed.

  Lemma ot_subt : forall t t0 ec, only_trivial t -> atom_plug t0 ec = t -> exists v, t0 = value_to_term v.
  Proof with auto.
    intros; destruct (H t0 (ec :: nil)) as [H1 | [v H1]]...
    discriminate.
    exists v...
  Qed.

  Ltac ot_v t ec :=
  match goal with
  | [Hot : (only_trivial ?H1) |- _] => destruct (ot_subt _ t ec Hot) as [?v HV]; [auto | subst t]
  end.

  Ltac mlr rv :=
  match goal with [ |- (exists v, ?H1 = value_to_term v) \/ (exists r, ?H1 = redex_to_term r)] =>
    match rv with
    | (?v : value) => left; exists v
    | (?r : redex) => right; exists r
    end; simpl; auto
  end.

  Lemma trivial_val_red : forall t : term, only_trivial t ->
    (exists v : value, t = value_to_term v) \/ (exists r : redex, t = redex_to_term r).
  Proof.
    destruct t; intros.
    mlr (v_var v).
    mlr (v_lam v t).
    ot_v t1 (ap_r t2); ot_v t2 (ap_l v); mlr (beta v v0).
  Qed.

End CallByValue.

Module CallByValue_Eval <: RED_SEM CallByValue.

Definition term := CallByValue.term.
Definition value := CallByValue.value.
Definition redex := CallByValue.redex.
Definition context := CallByValue.context.
Definition var := CallByValue.var.
Definition lam := CallByValue.lam.
Definition appl := CallByValue.appl.
Definition v_var := CallByValue.v_var.
Definition v_lam := CallByValue.v_lam.
Definition beta := CallByValue.beta.
Definition empty := CallByValue.empty.
Definition ap_r := CallByValue.ap_r.
Definition ap_l := CallByValue.ap_l.
Definition value_to_term : value -> term := CallByValue.value_to_term.
Definition redex_to_term : redex -> term := CallByValue.redex_to_term.
Coercion value_to_term : value >-> term.
Coercion redex_to_term : redex >-> term.
Definition decomp_to_term := CallByValue.decomp_to_term.

Definition contract := CallByValue.contract.
Definition plug := CallByValue.plug.
Definition compose := CallByValue.compose.

Definition decomp := CallByValue.decomp.
Definition d_val := CallByValue.d_val.
Definition d_red := CallByValue.d_red.

Inductive dec' : term -> context -> decomp -> Prop :=
| val_ctx : forall (v : value) (c : context) (d : decomp),
      	      decctx c v d -> dec' v c d
| app_ctx : forall (t s : term) (c : context) (d : decomp),
      	      dec' t (ap_r s :: c) d -> dec' (appl t s) c d
with decctx : context -> value -> decomp -> Prop :=
| mt_dec   : forall (v : value),
      	       decctx empty v (d_val v)
| ap_l_dec : forall (v0 v1 : value) (c : context),
      	       decctx (ap_l v0 :: c) v1 (d_red (beta v0 v1) c)
| ap_r_dec : forall (v : value) (s : term) (c : context) (d : decomp),
      	      dec' s (ap_l v :: c) d -> decctx (ap_r s :: c) v d.

Scheme dec_Ind := Induction for dec' Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

Definition dec := dec'.

(** A redex in context will only ever be reduced to itself *)
Lemma dec_redex_self : forall (r : redex) (c : context), dec (redex_to_term r) c (d_red r c).
Proof with eauto.
intros; destruct r; repeat (constructor; simpl; auto).
Qed.

Lemma dec_correct : forall t c d, dec t c d -> decomp_to_term d = plug t c.
Proof with auto.
induction 1 using dec_Ind with
(P := fun t c d (H : dec t c d) => decomp_to_term d = plug t c)
(P0:= fun c v d (H : decctx c v d) => decomp_to_term d = plug (v:term) c); simpl; auto.
Qed.

Lemma dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
Proof.
induction c; simpl; auto; destruct a; intros c0 t0 d X; assert (hh := IHc _ _ _ X); inversion hh; subst;
try (destruct v; discriminate); try (destruct v0; discriminate); inversion H3; subst; auto;
try (destruct v; discriminate); apply CallByValue.value_to_term_injective in H; subst; inversion H0; subst; auto.
Qed.

Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
Proof.
induction c; simpl; auto; destruct a; intros; apply IHc;
repeat (constructor; simpl; auto).
Qed.

  Inductive decempty : term -> decomp -> Prop :=
  | d_intro : forall (t : term) (d : decomp), dec t empty d -> decempty t d.

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall (v : value), iter (d_val v) v
  | i_red : forall (r : redex) (t : term) (c : context) (d : decomp) (v : value),
              contract r = Some t -> decempty (plug t c) d -> iter d v -> iter (d_red r c) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (d : decomp) (v : value), decempty t d -> iter d v -> eval t v.

  Definition decompose := CallByValue.decompose.

End CallByValue_Eval.

Module CallByValue_SOS.

Module R := CallByValue.

Inductive step : R.term -> R.term -> Prop :=
| s_red   : forall v v0 t, R.contract (R.beta v v0) = Some t ->
              step (R.appl (R.value_to_term v) (R.value_to_term v0)) t
| s_left  : forall t t0 t1, step t t0 -> step (R.appl t t1) (R.appl t0 t1)
| s_right : forall v t t0, step t t0 -> step (R.appl (R.value_to_term v) t) (R.appl (R.value_to_term v) t0).

Inductive step_close : R.term -> R.value -> Prop :=
| c_z : forall v, step_close (R.value_to_term v) v
| c_s : forall t t0 v, step t t0 -> step_close t0 v -> step_close t v.

Module RS := CallByValue_Eval.
Module LP := Lang_Prop R.

Lemma plug_step : forall c t t0, step t t0 -> step (R.plug t c) (R.plug t0 c).
Proof.
  induction c; intros; simpl; auto.
  apply IHc; destruct a; constructor; auto.
Qed.

Lemma dec_red_step : forall t r c t0 t1, RS.decempty t (R.d_red r c) -> R.contract r = Some t0 -> R.plug t0 c = t1 -> step t t1.
Proof.
  intros t r c t0 t1 H; inversion_clear H; generalize dependent t1; generalize dependent t0;
  rewrite <- LP.plug_empty with (t := t);
  induction H0 using RS.dec_Ind with
  (P := fun t c d (H : RS.dec t c d) => match d with
    | R.d_val v => True
    | R.d_red r c' => forall t0 t1, R.contract r = Some t0 -> R.plug t0 c' = t1 -> step (R.plug t c) t1
  end)
  (P0:= fun c v d (H : RS.decctx c v d) => match d with
    | R.d_val v => True
    | R.d_red r c' => forall t0 t1, R.contract r = Some t0 -> R.plug t0 c' = t1 -> step (R.plug (R.value_to_term v) c) t1
  end); try destruct d; simpl; intros; subst; auto.
  eapply IHdec'; simpl; eauto.
  simpl in IHdec'; eapply IHdec'; eauto.
  apply plug_step; constructor; auto.
  simpl in IHdec'; eapply IHdec'; simpl; eauto.
Qed.

Lemma eval_sc : forall t v, RS.eval t v -> step_close t v.
Proof.
intros; inversion_clear H; generalize dependent t; induction H1; intros.
inversion_clear H0; assert (hh := RS.dec_correct _ _ _ H); simpl in hh; subst; constructor.
remember (R.plug t c).
econstructor 2; [ eapply dec_red_step | eapply IHiter]; eauto.
Qed.

Lemma dec_con : forall t c c0 r c1, RS.dec t c (R.d_red r c1) -> RS.dec t (R.compose c c0) (R.d_red r (R.compose c1 c0)).
Proof.
intros t c c0; induction 1 using RS.dec_Ind with
(P := fun t c d (H : RS.dec t c d) => match d with
  | R.d_val v => True
  | R.d_red r c1 => RS.dec t (R.compose c c0) (R.d_red r (R.compose c1 c0))
end)
(P0 := fun c v d (H : RS.decctx c v d) => match d with
  | R.d_val v => True
  | R.d_red r c1 => RS.decctx (R.compose c c0) v (R.d_red r (R.compose c1 c0))
end); try destruct d; simpl in *; intros; constructor; auto.
Qed.

Lemma step_dec_red : forall t t0, step t t0 -> exists r, exists c, (RS.decempty t (R.d_red r c) /\ exists t1, (R.contract r = Some t1 /\ R.plug t1 c = t0)).
Proof.
induction 1.
exists (R.beta v v0); exists R.empty; repeat constructor.
exists t; repeat constructor; auto.
destruct IHstep as [r [c [Hd [t2 [Hc Hp]]]]]; inversion_clear Hd.
exists r; exists (R.compose c (R.ap_r t1 :: nil)); repeat constructor.
cutrewrite (RS.ap_r t1 :: RS.empty = R.compose RS.empty (RS.ap_r t1 :: RS.empty));
try apply dec_con; auto.
exists t2; subst; rewrite LP.plug_compose; simpl; auto.
destruct IHstep as [r [c [Hd [t2 [Hc Hp]]]]]; inversion_clear Hd.
exists r; exists (R.compose c (R.ap_l v :: nil)); repeat constructor.
cutrewrite (RS.ap_l v :: RS.empty = R.compose RS.empty (RS.ap_l v :: RS.empty));
try apply dec_con; auto.
exists t2; subst; rewrite LP.plug_compose; simpl; auto.
Qed.

Lemma sc_eval : forall t v, step_close t v -> RS.eval t v.
Proof.
induction 1.
econstructor; repeat constructor.
destruct (step_dec_red t t0) as [r [c [Hd [t1 [Hc Hp]]]]]; auto.
econstructor; eauto.
inversion_clear IHstep_close; subst; econstructor 2; eauto.
Qed.

End CallByValue_SOS.


Module CallByValue_Ref <: RED_REF_LANG.

  Module R := CallByValue.

  Definition dec_term (t : R.term) : R.interm_dec :=
  match t with
  | R.var v0 => R.in_val (R.v_var v0)
  | R.lam v t => R.in_val (R.v_lam v t)
  | R.appl t0 t1 => R.in_term t0 (R.ap_r t1)
  end.
  Definition dec_context (ec : R.elem_context) (v : R.value) : R.interm_dec :=
  match ec with
  | R.ap_r t => R.in_term t (R.ap_l v)
  | R.ap_l v' => R.in_red (R.beta v' v)
  end.

  Inductive subterm_one_step : R.term -> R.term -> Prop :=
  | st_1 : forall t t0 ec (DECT : t = R.atom_plug t0 ec), subterm_one_step t0 t.
  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    prove_st_wf.
  Qed.

  Definition subterm_order := clos_trans_n1 R.term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_r _ _ wf_st1.

  Definition ec_order (ec0 : R.elem_context) (ec1 : R.elem_context) : Prop :=
  match ec0, ec1 with
  | R.ap_l _, R.ap_r _ => True
  | _, _ => False
  end.
  Notation " a <: b " := (ec_order a b) (at level 40).
  Lemma wf_eco : well_founded ec_order.
  Proof.
    prove_ec_wf.
  Qed.

  Lemma dec_term_red_empty  : forall t r, dec_term t = R.in_red r -> R.only_empty t.
  Proof.
    intros; destruct t; inversion H.
  Qed.
  Lemma dec_term_val_empty : forall t v, dec_term t = R.in_val v -> R.only_empty t.
  Proof.
    intros; destruct t; inversion H; subst; intros t0 c; generalize dependent t0; induction c; intros; simpl in *;
    auto; assert (hh := IHc _ H0); subst c; destruct a; inversion H0.
  Qed.
  Lemma dec_term_term_top   : forall t t' ec, dec_term t = R.in_term t' ec -> forall ec', ~ec <: ec'.
  Proof.
    intros; destruct t; inversion H; subst; intro; contradiction H0.
  Qed.
  Lemma dec_context_red_bot : forall ec v r, dec_context ec v = R.in_red r -> forall ec', ~ec' <: ec.
  Proof.
    intros; destruct ec; inversion H; subst; intro; destruct ec'; contradiction H0.
  Qed.
  Lemma dec_context_val_bot : forall ec v v0, dec_context ec v = R.in_val v0 -> forall ec', ~ec' <: ec.
  Proof.
    intros; destruct ec; inversion H.
  Qed.
  Lemma dec_context_term_next : forall ec v t ec', dec_context ec v = R.in_term t ec' -> ec' <: ec /\ forall ec'', ec'' <: ec -> ~ec' <: ec''.
  Proof.
    intros; destruct ec; inversion H; constructor; [ constructor | intros ]; destruct ec''; inversion H0; intro hh; inversion hh.
  Qed.

  Lemma dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t' ec => R.atom_plug t' ec = t
    end.
  Proof.
    intros; destruct t; simpl; auto.
  Qed.
  Lemma dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t ec' => R.atom_plug t ec' = R.atom_plug (R.value_to_term v) ec
    end.
  Proof.
    intros; destruct ec; simpl; auto.
  Qed.

  Lemma ec_order_antisym : forall ec ec0, ec <: ec0 -> ~ec0 <: ec.
  Proof.
    intros; destruct ec; destruct ec0; inversion H.
    intro H0; inversion H0.
  Qed.
  Lemma dec_ec_ord : forall t0 t1 ec0 ec1, R.atom_plug t0 ec0 = R.atom_plug t1 ec1 -> ec0 <: ec1 \/ ec1 <: ec0 \/ (t0 = t1 /\ ec0 = ec1).
  Proof.
    destruct ec0; destruct ec1; [right; right | right; left | left | right; right]; try constructor;
    inversion H; subst; auto; apply R.value_to_term_injective in H1; subst; auto.
  Qed.
  Lemma elem_context_det : forall t0 t1 ec0 ec1, ec0 <: ec1 -> R.atom_plug t0 ec0 = R.atom_plug t1 ec1 ->
    exists v, t1 = R.value_to_term v.
  Proof.
    intros; destruct ec0; destruct ec1; inversion H; 
    inversion H0; exists v; subst; reflexivity.
  Qed.

End CallByValue_Ref.


Module CallByValue_RefEval <: RED_REF_SEM CallByValue.

Definition term := CallByValue.term.
Definition value := CallByValue.value.
Definition redex := CallByValue.redex.
Definition context := CallByValue.context.
Definition var := CallByValue.var.
Definition lam := CallByValue.lam.
Definition appl := CallByValue.appl.
Definition v_var := CallByValue.v_var.
Definition v_lam := CallByValue.v_lam.
Definition beta := CallByValue.beta.
Definition empty := CallByValue.empty.
Definition elem_context := CallByValue.elem_context.
Definition ap_r := CallByValue.ap_r.
Definition ap_l := CallByValue.ap_l.
Definition value_to_term : value -> term := CallByValue.value_to_term.
Definition redex_to_term : redex -> term := CallByValue.redex_to_term.
Coercion value_to_term : value >-> term.
Coercion redex_to_term : redex >-> term.

Definition contract := CallByValue.contract.
Definition plug := CallByValue.plug.
Definition compose := CallByValue.compose.
Definition atom_plug := CallByValue.atom_plug.

Definition decomp := CallByValue.decomp.
Definition d_val := CallByValue.d_val.
Definition d_red := CallByValue.d_red.

Definition interm_dec := CallByValue.interm_dec.
Definition in_red := CallByValue.in_red.
Definition in_val := CallByValue.in_val.
Definition in_term := CallByValue.in_term.
Definition decomp_to_term := CallByValue.decomp_to_term.

(** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
Definition dec_term (t : term) : interm_dec :=
match t with
  | var vname => in_val (v_var vname)
  | lam vname s => in_val (v_lam vname s)
  | appl t s => in_term t (ap_r s)
end.

Definition dec_context : elem_context -> value -> interm_dec :=
fun (ec : elem_context) (v : value) => match ec with
  | ap_r t  => in_term t (ap_l v)
  | ap_l v0 => in_red (beta v0 v)
end.

Lemma dec_term_value : forall (v:value), dec_term (v:term) = in_val v.
Proof.
destruct v; simpl; auto.
Qed.
Hint Resolve dec_term_value.

(** dec is left inverse of plug *)
Lemma dec_term_correct : forall t, match dec_term t with
  | in_red r => redex_to_term r = t
  | in_val v => (value_to_term v) = t
  | in_term t0 ec0 => atom_plug t0 ec0 = t
end.
Proof.
induction t; simpl; auto.
Qed.
Lemma dec_context_correct : forall c v, match dec_context c v with
  | in_red r => redex_to_term r = atom_plug (value_to_term v) c
  | in_val v0 => value_to_term v0 = atom_plug (value_to_term v) c
  | in_term t ec0 => atom_plug t ec0 = atom_plug (value_to_term v) c
end.
Proof.
induction c; simpl; auto.
Qed.

(** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> context -> decomp -> Prop :=
  | d_dec  : forall (t : term) (c : context) (r : redex),
                 dec_term t = in_red r -> dec t c (d_red r c)
  | d_v    : forall (t : term) (c : context) (v : value) (d : decomp),
                 dec_term t = in_val v -> decctx v c d -> dec t c d
  | d_term : forall (t t0 : term) (c : context) (ec : elem_context) (d : decomp),
                 dec_term t = in_term t0 ec -> dec t0 (ec :: c) d -> dec t c d
  with decctx : value -> context -> decomp -> Prop :=
  | dc_end  : forall (v : value), decctx v empty (d_val v)
  | dc_dec  : forall (v : value) (ec : elem_context) (c : context) (r : redex),
                dec_context ec v = in_red r -> decctx v (ec :: c) (d_red r c)
  | dc_val  : forall (v v0 : value) (ec : elem_context) (c : context) (d : decomp),
                dec_context ec v = in_val v0 -> decctx v0 c d -> decctx v (ec :: c) d
  | dc_term : forall (v : value) (ec ec0 : elem_context) (c : context) (t : term) (d : decomp),
                dec_context ec v = in_term t ec0 -> dec t (ec0 :: c) d -> decctx v (ec :: c) d.

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

  Lemma dec_red_ref : forall t c d, CallByValue_Eval.dec t c d <-> dec t c d.
  Proof with eauto.
    intros; split; intro.
    induction H using CallByValue_Eval.dec_Ind with
    (P := fun t c d (H : CallByValue_Eval.dec t c d) => dec t c d)
    (P0:= fun v c d (H : CallByValue_Eval.decctx v c d) => decctx c v d);
    [ econstructor 2 | econstructor 3 | constructor | constructor | econstructor 4]; simpl...
    induction H using dec_Ind with
    (P := fun t c d (H : dec t c d) => CallByValue_Eval.dec t c d)
    (P0:= fun v c d (H : decctx v c d) => CallByValue_Eval.decctx c v d);
    try (destruct t; inversion e; subst; 
      try (change (CallByValue_Eval.dec (value_to_term (v_var v0)) c d));
      try (change (CallByValue_Eval.dec (value_to_term (v_lam v0 t)) c d));
    constructor); auto; try constructor;
    destruct c; destruct ec; inversion e; subst; constructor...
  Qed.

Module RS : RED_SEM CallByValue with Definition dec := dec.

    Definition dec := dec.

    Inductive decempty : term -> decomp -> Prop :=
    | d_intro : forall (t : term) (d : decomp), dec t empty d -> decempty t d.

    Inductive iter : decomp -> value -> Prop :=
    | i_val : forall (v : value), iter (d_val v) v
    | i_red : forall (r : redex) (t : term) (c : context) (d : decomp) (v : value),
                contract r = Some t -> decempty (plug t c) d -> iter d v -> iter (d_red r c) v.

    Inductive eval : term -> value -> Prop :=
    | e_intro : forall (t : term) (d : decomp) (v : value), decempty t d -> iter d v -> eval t v.

    Lemma dec_redex_self : forall (r : redex) (c : context), dec (redex_to_term r) c (d_red r c).
    Proof.
      intros; rewrite <- dec_red_ref; apply CallByValue_Eval.dec_redex_self.
    Qed.

    (** dec is left inverse of plug *)
    Lemma dec_correct : forall t c d, dec t c d -> decomp_to_term d = plug t c.
    Proof.
      intros; apply CallByValue_Eval.dec_correct; rewrite dec_red_ref; auto.
    Qed.

    Lemma dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
    Proof.
      intros; rewrite <- dec_red_ref; apply CallByValue_Eval.dec_plug; rewrite dec_red_ref; auto.
    Qed.

    Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
    Proof.
      intros; rewrite <- dec_red_ref; apply CallByValue_Eval.dec_plug_rev; rewrite dec_red_ref; auto.
    Qed.

    Definition decompose := CallByValue.decompose.

End RS.

  Lemma iter_red_ref : forall d v, CallByValue_Eval.iter d v <-> RS.iter d v.
  Proof.
    intros; split; intro; induction H; try constructor;
    constructor 2 with t d; auto; constructor; 
    [inversion_clear H0; rewrite <- dec_red_ref | inversion_clear D_EM; rewrite dec_red_ref]; auto.
  Qed.

  Lemma eval_red_ref : forall t v, CallByValue_Eval.eval t v <-> RS.eval t v.
  Proof.
    intros; split; intro; inversion_clear H; constructor 1 with d.
    constructor; inversion_clear H0; rewrite <- dec_red_ref; auto.
    rewrite <- iter_red_ref; auto.
    constructor; inversion_clear D_EM; rewrite dec_red_ref; auto.
    rewrite iter_red_ref; auto.
  Qed.

  Lemma dec_val_self : forall v c d, dec (value_to_term v) c d <-> decctx v c d.
  Proof.
    split; intro.
    destruct v; inversion H; inversion H0; subst; auto.
    assert (hh := dec_term_value v); econstructor; eauto.
  Qed.

End CallByValue_RefEval.

Module CBV_EAM  := ProperEAMachine CallByValue CallByValue_RefEval.

Module CKMachine <: ABSTRACT_MACHINE.

Definition term := CallByValue.term.
Definition value := CallByValue.value.
Definition redex := CallByValue.redex.
Definition context := CallByValue.context.
Definition var := CallByValue.var.
Definition lam := CallByValue.lam.
Definition appl := CallByValue.appl.
Definition v_var := CallByValue.v_var.
Definition v_lam := CallByValue.v_lam.
Definition beta := CallByValue.beta.
Definition empty := CallByValue.empty.
Definition ap_r := CallByValue.ap_r.
Definition ap_l := CallByValue.ap_l.
Definition value_to_term : value -> term := CallByValue.value_to_term.
Definition redex_to_term : redex -> term := CallByValue.redex_to_term.
Coercion value_to_term : value >-> term.
Coercion redex_to_term : redex >-> term.

Definition contract := CallByValue.contract.
Definition plug := CallByValue.plug.
Definition compose := CallByValue.compose.

Definition decomp := CallByValue.decomp.
Definition d_val := CallByValue.d_val.
Definition d_red := CallByValue.d_red.

Definition configuration := CBV_EAM.configuration.
Definition c_init := CBV_EAM.c_init.
Definition c_eval := CBV_EAM.c_eval.
Definition c_apply := CBV_EAM.c_apply.
Definition c_final := CBV_EAM.c_final.

Inductive transition' : configuration -> configuration -> Prop :=
| t_init : forall t : term, transition' (c_init t) (c_eval t empty)
| t_val  : forall (v : value) (c : context), transition' (c_eval (v:term) c) (c_apply c v)
| t_app  : forall (t s : term) (c : context), transition' (c_eval (appl t s) c) (c_eval t (ap_r s :: c))
| t_empty: forall v : value, transition' (c_apply empty v) (c_final v)
| t_ap_r : forall (t : term) (v : value) (c : context), transition' (c_apply (ap_r t :: c) v) (c_eval t (ap_l v :: c))
| t_ap_l : forall (v v0 : value) (c : context) (t : term),
             contract (beta v0 v) = Some t -> transition' (c_apply (ap_l v0 :: c) v) (c_eval t c).

Definition transition := transition'.
Inductive trans_close : configuration -> configuration -> Prop :=
| one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
| multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

Lemma trEA_CK : forall w w' : configuration, CBV_EAM.transition w w' -> transition w w'.
Proof with auto.
intros c c0 H; inversion H; subst; try (destruct t; discriminate);
try constructor;
try (destruct ec; inversion DC; subst; constructor; auto);
destruct t; inversion DT; subst;
[cutrewrite (CallByValue.var v0 = value_to_term (v_var v0)) | cutrewrite (CallByValue.lam v0 t = value_to_term (v_lam v0 t)) | idtac]; try constructor...
Qed.
Hint Resolve trEA_CK.

Lemma tcEA_CK : forall w w' : configuration, CBV_EAM.AM.trans_close w w' -> trans_close w w'.
Proof.
intros w w' H; induction H; subst; [ constructor 1 | econstructor 2]; eauto.
Qed.

Lemma evalEA_CK : forall t v, CBV_EAM.AM.eval t v -> eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcEA_CK; auto.
Qed.
Hint Resolve evalEA_CK.

Lemma trCK_EA : forall w w' : configuration, transition w w' -> CBV_EAM.AM.transition w w'.
Proof.
intros c c0 H; inversion H; subst; try (constructor; simpl; auto; apply CallByValue_RefEval.dec_term_value);
econstructor; simpl; eauto.
Qed.
Hint Resolve trCK_EA.

Lemma tcCK_EA : forall w w' : configuration, trans_close w w' -> CBV_EAM.AM.trans_close w w'.
Proof.
induction 1; [ constructor 1 | econstructor 2]; eauto.
Qed.

Lemma evalCK_EA : forall t v, eval t v -> CBV_EAM.AM.eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcCK_EA; auto.
Qed.
Hint Resolve evalCK_EA.

Theorem CKMachineCorrect : forall (t : term) (v : value), CallByValue_Eval.eval t v <-> eval t v.
Proof with auto.
intros t v; rewrite CallByValue_RefEval.eval_red_ref; rewrite CBV_EAM.eval_apply_correct; split...
Qed.

End CKMachine.
