Require Import refocusing_substitutions.
Require Import Setoid.

Module CallByName <: RED_LANG.

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
  | beta : value -> term -> redex'.
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
  Hint Resolve value_to_term_injective.

  Definition redex_to_term (r : redex) : term :=
  match r with
  | beta v t => appl (v:term) t
  end.
  Coercion redex_to_term : redex >-> term.

  Lemma redex_to_term_injective : forall r r', redex_to_term r = redex_to_term r' -> r = r'.
  Proof.
    intros r r0; case r; case r0; intros; injection H; intros;
    rewrite (value_to_term_injective _ _ H1); rewrite H0; auto.
  Qed.

  Parameter subst : term -> var_name -> term -> term.

  Definition contract (r : redex) : option term :=
  match r with
    | beta v t => match v with
                    | v_var x => None
                    | v_lam x t0 => Some (subst t0 x t)
                  end
  end.

  Inductive elem_context' : Set :=
  | ap_r : term -> elem_context'.
  Definition elem_context := elem_context'.
  Definition context := list elem_context.
  Definition empty : context := nil.

  Definition compose (c0 c1 : context) : context := app c0 c1.
  Definition atom_plug (t : term) (ec : elem_context) : term :=
  match ec with
    | ap_r t0 => appl t t0
  end.
  Definition plug (t : term) (c : context) : term := fold_left atom_plug c t.

  Lemma plug_compose : forall (c c' : context) (t : term), plug t (compose c c') = plug (plug t c) c'.
  Proof (fold_left_app atom_plug).
  Hint Resolve plug_compose : prop.

  Lemma decompose : forall t : term, (exists v : value, t = v) \/
                      (exists r : redex, exists c : context, plug r c = t).
  Proof.
    induction t; simpl; [ left; split with (v_var v) | left; split with (v_lam v t) | right ]; auto.
    clear IHt2; destruct IHt1 as [[v H] | [r [c H]]]; [exists (beta v t2); exists empty 
    | exists r; exists (compose c (ap_r t2 :: empty)); rewrite plug_compose]; subst; simpl; auto.
  Qed.

  Inductive decomp : Set :=
  | d_val : value -> decomp
  | d_red : redex -> context -> decomp.

  Inductive interm_dec : Set :=
  | in_red : redex -> interm_dec
  | in_val : value -> interm_dec
  | in_term: term -> elem_context -> interm_dec.

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
    destruct (IHc _ H) as [H0 | [v0 H0]]; subst; simpl in *;
    match goal with [Hdisc : atom_plug ?t ?a = _ ?v |- _ ] => destruct a; destruct v; discriminate Hdisc end.
  Qed.
  Lemma redex_trivial : forall r : redex, only_trivial (redex_to_term r).
  Proof.
    intros r t c; generalize dependent t; induction c; intros; simpl in *; auto; right;
    destruct (IHc _ H) as [H0 | [v0 H0]]; subst; simpl in *.
    destruct r; destruct a; inversion H; subst; exists v; auto.
    destruct a; destruct v0; discriminate H0.
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
  match goal with
  | [ |- (exists v, ?H1 = value_to_term v) \/ (exists r, ?H1 = redex_to_term r)] =>
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
    ot_v t1 (ap_r t2); mlr (beta v t2).
  Qed.

End CallByName.

Module CallByName_Eval <: RED_SEM CallByName.

Definition term := CallByName.term.
Definition value := CallByName.value.
Definition redex := CallByName.redex.
Definition context := CallByName.context.
Definition var := CallByName.var.
Definition lam := CallByName.lam.
Definition appl := CallByName.appl.
Definition v_var := CallByName.v_var.
Definition v_lam := CallByName.v_lam.
Definition beta := CallByName.beta.
Definition empty := CallByName.empty.
Definition ap_r := CallByName.ap_r.
Definition value_to_term : value -> term := CallByName.value_to_term.
Definition redex_to_term : redex -> term := CallByName.redex_to_term.
Coercion value_to_term : value >-> term.
Coercion redex_to_term : redex >-> term.
Definition decomp_to_term := CallByName.decomp_to_term.

Definition contract := CallByName.contract.
Definition plug := CallByName.plug.
Definition compose := CallByName.compose.

Definition decomp := CallByName.decomp.
Definition d_val := CallByName.d_val.
Definition d_red := CallByName.d_red.

Inductive dec' : CallByName.term -> CallByName.context -> CallByName.decomp -> Prop :=
| val_ctx : forall (v : CallByName.value) (c : CallByName.context) (d : CallByName.decomp),
  decctx c v d -> dec' v c d
| app_ctx : forall (t s : CallByName.term) (c : CallByName.context) (d : CallByName.decomp),
  dec' t (ap_r s :: c) d -> dec' (appl t s) c d
with decctx : CallByName.context -> CallByName.value -> CallByName.decomp -> Prop :=
| mt_dec : forall (v : CallByName.value),
  decctx CallByName.empty v (CallByName.d_val v)
| ap_dec : forall (v : CallByName.value) (t : CallByName.term) (c : CallByName.context),
  decctx (ap_r t :: c) v (CallByName.d_red (CallByName.beta v t) c).

Definition dec := dec'.

Scheme dec_Ind := Induction for dec' Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

Lemma dec_redex_self : forall (r : redex) (c : context), dec (redex_to_term r) c (d_red r c).
Proof.
intros; destruct r; repeat (constructor; simpl; auto).
Qed.

Lemma dec_correct : forall t c d, dec t c d -> decomp_to_term d = plug t c.
Proof.
induction 1 using dec_Ind with
(P := fun t c d (H:dec t c d) => decomp_to_term d = plug t c)
(P0 := fun c v d (H:decctx c v d) => decomp_to_term d = plug v c); intros; simpl; auto.
Qed.

Lemma dec_plug :
  forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
Proof.
  induction c; intros; auto; simpl; assert (hh:=IHc _ _ _ H); inversion hh; subst;
  destruct a; try (destruct v); inversion H0; subst; auto.
Qed.

Lemma dec_plug_rev :
  forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
Proof.
induction c; intros; auto; simpl; apply IHc; destruct a;
constructor; inversion H; subst; constructor; trivial.
Qed.

  Inductive decempty : term -> decomp -> Prop :=
  | d_intro : forall (t : term) (d : decomp), dec t empty d -> decempty t d.

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall (v : value), iter (d_val v) v
  | i_red : forall (r : redex) (t : term) (c : context) (d : decomp) (v : value),
              contract r = Some t -> decempty (plug t c) d -> iter d v -> iter (d_red r c) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (d : decomp) (v : value), decempty t d -> iter d v -> eval t v.

  Definition decompose := CallByName.decompose.

End CallByName_Eval.

Module CallByName_Ref <: RED_REF_LANG.

  Module R := CallByName.

  Definition dec_term (t : R.term) : R.interm_dec :=
  match t with
  | CallByName.var v0 => R.in_val (CallByName.v_var v0)
  | CallByName.lam v t => R.in_val (CallByName.v_lam v t)
  | CallByName.appl t0 t1 => R.in_term t0 (CallByName.ap_r t1)
  end.
  Definition dec_context (ec : R.elem_context) (v : R.value) : R.interm_dec :=
  match ec with
  | CallByName.ap_r t => R.in_red (R.beta v t)
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

  Definition ec_order (ec0 : R.elem_context) (ec1 : R.elem_context) : Prop := False.
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
    auto; assert (hh := IHc _ H0); subst; destruct a; inversion H0.
  Qed.
  Lemma dec_term_term_top   : forall t t' ec, dec_term t = R.in_term t' ec -> forall ec', ~ec <: ec'.
  Proof.
    intros; destruct t; inversion H; subst; intro; contradiction H0.
  Qed.
  Lemma dec_context_red_bot : forall ec v r, dec_context ec v = R.in_red r -> forall ec', ~ec' <: ec.
  Proof.
    intros; destruct ec; inversion H; subst; intro; contradiction H0.
  Qed.
  Lemma dec_context_val_bot : forall ec v v0, dec_context ec v = R.in_val v0 -> forall ec', ~ec' <: ec.
  Proof.
    intros; destruct ec; inversion H.
  Qed.
  Lemma dec_context_term_next : forall ec v t ec', dec_context ec v = R.in_term t ec' -> ec' <: ec /\ forall ec'', ec'' <: ec -> ~ec' <: ec''.
  Proof.
    intros; destruct ec; inversion H.
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
    intros; inversion H.
  Qed.
  Lemma dec_ec_ord : forall t0 t1 ec0 ec1, R.atom_plug t0 ec0 = R.atom_plug t1 ec1 -> ec0 <: ec1 \/ ec1 <: ec0 \/ (t0 = t1 /\ ec0 = ec1).
  Proof.
    intros; destruct ec0; destruct ec1; destruct t0; destruct t1; inversion H; subst; right; right; constructor; auto.
  Qed.
  Lemma elem_context_det : forall t0 t1 ec0 ec1, ec0 <: ec1 -> R.atom_plug t0 ec0 = R.atom_plug t1 ec1 ->
    exists v, t1 = R.value_to_term v.
  Proof.
    intros; inversion H.
  Qed.

End CallByName_Ref.

Module CallByName_RefEval_auto <: RED_REF_SEM CallByName := RedRefSem CallByName_Ref.

Lemma dec_sem_aref : forall t c d, CallByName_Eval.dec t c d <-> CallByName_RefEval_auto.dec t c d.
Proof with auto.
split; intro H.
induction H using CallByName_Eval.dec_Ind with
(P := fun t c d (H : CallByName_Eval.dec t c d) => CallByName_RefEval_auto.dec t c d)
(P0:= fun c v d (H : CallByName_Eval.decctx c v d) => CallByName_RefEval_auto.decctx v c d).
econstructor; eauto; destruct v; simpl; auto.
econstructor 3; simpl; eauto.
constructor.
econstructor; eauto.
induction H using CallByName_RefEval_auto.dec_Ind with
(P := fun t c d (H : CallByName_RefEval_auto.dec t c d) => CallByName_Eval.dec t c d)
(P0:= fun v c d (H : CallByName_RefEval_auto.decctx v c d) => CallByName_Eval.decctx c v d);
try (destruct t; inversion DT); try (destruct ec; inversion DC); subst; try econstructor; eauto.
cutrewrite (CallByName.var v0 = CallByName.value_to_term (CallByName.v_var v0)); try constructor; auto.
cutrewrite (CallByName.lam v0 t = CallByName.value_to_term (CallByName.v_lam v0 t)); try constructor; auto.
Qed.

Lemma iter_sem_aref : forall d v, CallByName_Eval.iter d v <-> CallByName_RefEval_auto.RS.iter d v.
Proof with auto.
split; intro H; induction H; try constructor;
[inversion_clear H0; rewrite dec_sem_aref in H2 | inversion_clear D_EM; rewrite <- dec_sem_aref in DEC];
econstructor 2; eauto; constructor...
Qed.

Lemma eval_sem_aref : forall t v, CallByName_Eval.eval t v <-> CallByName_RefEval_auto.RS.eval t v.
Proof with eauto.
split; intro H; inversion_clear H; econstructor; [ constructor; inversion H0; rewrite <- dec_sem_aref
| rewrite <- iter_sem_aref | constructor; inversion D_EM; rewrite dec_sem_aref | rewrite iter_sem_aref ]...
Qed.

Module CallByName_RefEval <: RED_REF_SEM CallByName.

Definition term := CallByName.term.
Definition value := CallByName.value.
Definition redex := CallByName.redex.
Definition context := CallByName.context.
Definition elem_context := CallByName.elem_context.
Definition var := CallByName.var.
Definition lam := CallByName.lam.
Definition appl := CallByName.appl.
Definition v_var := CallByName.v_var.
Definition v_lam := CallByName.v_lam.
Definition beta := CallByName.beta.
Definition empty := CallByName.empty.
Definition ap_r := CallByName.ap_r.
Definition value_to_term : value -> term := CallByName.value_to_term.
Definition redex_to_term : redex -> term := CallByName.redex_to_term.
Coercion value_to_term : value >-> term.
Coercion redex_to_term : redex >-> term.

Definition contract := CallByName.contract.
Definition plug := CallByName.plug.
Definition compose := CallByName.compose.
Definition atom_plug := CallByName.atom_plug.

Definition decomp := CallByName.decomp.
Definition d_val := CallByName.d_val.
Definition d_red := CallByName.d_red.

Definition interm_dec := CallByName.interm_dec.
Definition in_red := CallByName.in_red.
Definition in_val := CallByName.in_val.
Definition in_term := CallByName.in_term.
Definition decomp_to_term := CallByName.decomp_to_term.

(** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
Definition dec_term (t : term) : interm_dec :=
match t with
  | var vname => in_val (v_var vname)
  | lam vname s => in_val (v_lam vname s)
  | appl t s => in_term t (ap_r s)
end.

Definition dec_context (ec : elem_context) (v : value) : interm_dec :=
match ec with
  | ap_r t => in_red (beta v t)
end.

Lemma dec_term_value : forall (v:value), dec_term (v:term) = in_val v.
Proof.
intro v; case v; simpl; auto.
Qed.
Hint Resolve dec_term_value.

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

(** dec is left inverse of plug *)
Lemma dec_term_correct : forall t, match dec_term t with
  | in_red r => redex_to_term r = t
  | in_val v => value_to_term v = t
  | in_term t0 ec0 => CallByName.atom_plug t0 ec0 = t
end.
Proof.
induction t; simpl; auto.
Qed.
Lemma dec_context_correct : forall ec v, match dec_context ec v with
  | in_red r => redex_to_term r = atom_plug (value_to_term v) ec
  | in_val v0 => value_to_term v0 = atom_plug (value_to_term v) ec
  | in_term t ec0 => atom_plug t ec0 = atom_plug (value_to_term v) ec
end.
Proof.
destruct ec; simpl; auto.
Qed.

  Lemma dec_red_ref : forall t c d, CallByName_Eval.dec t c d <-> dec t c d.
  Proof with eauto.
    intros; split; intro.
    induction H using CallByName_Eval.dec_Ind with
    (P := fun t c d (H : CallByName_Eval.dec t c d) => dec t c d)
    (P0:= fun v c d (H : CallByName_Eval.decctx v c d) => decctx c v d);
    [ econstructor 2 | econstructor 3 | constructor | constructor ]; simpl...
    induction H using dec_Ind with
    (P := fun t c d (H : dec t c d) => CallByName_Eval.dec t c d)
    (P0:= fun v c d (H : decctx v c d) => CallByName_Eval.decctx c v d);
    try (destruct t; inversion e; subst; 
      try (change (CallByName_Eval.dec (value_to_term (v_var v0)) c d));
      try (change (CallByName_Eval.dec (value_to_term (v_lam v0 t)) c d));
    constructor); auto; try constructor; 
    destruct c; destruct ec; inversion e; subst; constructor...
  Qed.

Module RS <: RED_SEM CallByName with Definition dec := dec.

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
      intros; rewrite <- dec_red_ref; apply CallByName_Eval.dec_redex_self.
    Qed.

    (** dec is left inverse of plug *)
    Lemma dec_correct : forall t c d, dec t c d -> decomp_to_term d = plug t c.
    Proof.
      intros; apply CallByName_Eval.dec_correct; rewrite dec_red_ref; auto.
    Qed.

    Lemma dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
    Proof.
      intros; rewrite <- dec_red_ref; apply CallByName_Eval.dec_plug; rewrite dec_red_ref; auto.
    Qed.

    Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
    Proof.
      intros; rewrite <- dec_red_ref; apply CallByName_Eval.dec_plug_rev; rewrite dec_red_ref; auto.
    Qed.

    Definition decompose := CallByName.decompose.

End RS.

  Lemma iter_red_ref : forall d v, CallByName_Eval.iter d v <-> RS.iter d v.
  Proof.
    intros; split; intro; induction H; try constructor;
    constructor 2 with t d; auto; constructor; inversion_clear H0;
    [rewrite <- dec_red_ref | rewrite dec_red_ref]; auto.
  Qed.

  Lemma eval_red_ref : forall t v, CallByName_Eval.eval t v <-> RS.eval t v.
  Proof.
    intros; split; intro; inversion_clear H; constructor 1 with d.
    constructor; inversion_clear H0; rewrite <- dec_red_ref; auto.
    rewrite <- iter_red_ref; auto.
    constructor; inversion_clear H0; rewrite dec_red_ref; auto.
    rewrite iter_red_ref; auto.
  Qed.

  Lemma dec_val_self : forall v c d, dec (value_to_term v) c d <-> decctx v c d.
  Proof.
    split; intro.
    destruct v; inversion H; inversion H0; subst; auto.
    assert (hh := dec_term_value v); econstructor; eauto.
  Qed.

End CallByName_RefEval.

Module CallByName_PEEval <: PE_REF_SEM CallByName.

Module Red_Sem := CallByName_RefEval.

  Lemma dec_context_not_val : forall v v0 ec, ~(Red_Sem.dec_context ec v = Red_Sem.in_val v0).
  Proof.
    destruct ec; intros; discriminate.
  Qed.
  Hint Resolve dec_context_not_val.
  Definition dec_term_value := Red_Sem.dec_term_value.

End CallByName_PEEval.

Module CBN_PEM := ProperPEMachine CallByName CallByName_PEEval.

Module KrivineMachine : ABSTRACT_MACHINE.

Definition term := CallByName.term.
Definition value := CallByName.value.
Definition redex := CallByName.redex.
Definition context := CallByName.context.
Definition var := CallByName.var.
Definition lam := CallByName.lam.
Definition appl := CallByName.appl.
Definition v_var := CallByName.v_var.
Definition v_lam := CallByName.v_lam.
Definition beta := CallByName.beta.
Definition empty := CallByName.empty.
Definition ap_r := CallByName.ap_r.
Definition value_to_term : value -> term := CallByName.value_to_term.
Definition redex_to_term : redex -> term := CallByName.redex_to_term.
Coercion value_to_term : value >-> term.
Coercion redex_to_term : redex >-> term.

Definition contract := CallByName.contract.
Definition plug := CallByName.plug.
Definition compose := CallByName.compose.

Definition decomp := CallByName.decomp.
Definition d_val := CallByName.d_val.
Definition d_red := CallByName.d_red.

Definition configuration := CBN_PEM.configuration.
Definition c_init := CBN_PEM.c_init.
Definition c_eval := CBN_PEM.c_eval.
Definition c_final := CBN_PEM.c_final.

Inductive transition' : configuration -> configuration -> Prop :=
| t_init : forall t:term, transition' (c_init t) (c_eval t empty)
| t_mt   : forall v:value, transition' (c_eval (v:term) empty) (c_final v)
| t_app  : forall (t s:term) (c:context),
             transition' (c_eval (appl t s) c) (c_eval t (ap_r s :: c))
| t_val  : forall (v:value) (t0 t:term) (c:context),
             contract (beta v t0) = Some t -> transition' (c_eval (v:term) (ap_r t0 :: c)) (c_eval t c).

Definition transition := transition'.
Inductive trans_close : configuration -> configuration -> Prop :=
| one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
| multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

Lemma trPE_K : forall w w' : configuration, CBN_PEM.transition w w' -> transition w w'.
Proof.
intros c c0 H; inversion H; subst; try (destruct t; discriminate).
constructor.
destruct t; inversion DT; subst.
change (transition (c_eval (value_to_term (v_var v0)) empty) (c_final (v_var v0))); constructor.
change (transition (c_eval (value_to_term (v_lam v0 t)) empty) (c_final (v_lam v0 t))); constructor.
destruct t; inversion DT; subst; destruct ec; inversion DC; subst; try discriminate.
change (transition (c_eval (value_to_term (v_lam v0 t)) (ap_r t1 :: c1)) (c_eval t0 c1)); constructor; auto.
destruct ec; discriminate.
induction t; simpl in DT; inversion DT; subst; simpl; constructor.
Qed.
Hint Resolve trPE_K.

Lemma tcPE_K : forall w w' : configuration, CBN_PEM.AM.trans_close w w' -> trans_close w w'.
Proof with eauto.
intros w w' H; induction H; subst; [ constructor 1 | econstructor 2]...
Qed.

Lemma evalPE_K : forall t v, CBN_PEM.AM.eval t v -> eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcPE_K; auto.
Qed.
Hint Resolve evalPE_K.

Lemma trK_PE : forall w w' : configuration, transition w w' -> CBN_PEM.AM.transition w w'.
Proof with eauto.
intros c c0 H; inversion H; subst; try (constructor; simpl; auto; fail).
econstructor; eauto; simpl...
Qed.
Hint Resolve trK_PE.

Lemma tcK_PE : forall w w' : configuration, trans_close w w' -> CBN_PEM.AM.trans_close w w'.
Proof with eauto.
induction 1; [ constructor 1 | econstructor 2]...
Qed.

Lemma evalK_PE : forall t v, eval t v -> CBN_PEM.AM.eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcK_PE; auto.
Qed.
Hint Resolve evalK_PE.

Theorem KrivineMachineCorrect : forall t v, CallByName_Eval.eval t v <-> eval t v.
Proof with auto.
intros; rewrite CallByName_RefEval.eval_red_ref; rewrite CBN_PEM.push_enter_correct; split...
Qed.

End KrivineMachine.
