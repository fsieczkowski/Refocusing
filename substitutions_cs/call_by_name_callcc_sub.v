Require Import refocusing_substitutions_cs.

Module CallByName <: RED_LANG_CS.

Require Import List.

Parameter var_name : Set.

Inductive term' : Set :=
| Var : var_name -> term'
| Lam : var_name -> term' -> term'
| App : term' -> term' -> term'
| A   : term' -> term'
| C   : term' -> term'.
Definition term := term'.

Inductive value' : Set :=
| vVar : var_name -> value'
| vLam : var_name -> term -> value'.
Definition value := value'.

Inductive redex' : Set :=
| rApp  : value -> term -> redex'
| rAb   : term -> redex'
| rCall : term -> redex'.
Definition redex := redex'.

Definition value_to_term (v : value) : term :=
match v with
| vVar v' => Var v'
| vLam v' t => Lam v' t
end.
Coercion value_to_term : value >-> term.

Lemma value_to_term_injective : forall v v', value_to_term v = value_to_term v' -> v = v'.
Proof.
intros v v0; case v; case v0; simpl; intros; try discriminate; injection H;
intros; subst v1; try subst t; auto.
Qed.

Definition redex_to_term (r : redex) : term :=
match r with
| rApp v t => App (v:term) t
| rAb t => A t
| rCall t => C t
end.
Coercion redex_to_term : redex >-> term.

Lemma redex_to_term_injective : forall r r', redex_to_term r = redex_to_term r' -> r = r'.
Proof with auto.
intros r r0; case r; case r0; intros; try discriminate; simpl in *; injection H; intros; subst...
rewrite (value_to_term_injective _ _ H1)...
Qed.

Parameter subst : term -> var_name -> term -> term.
Parameter fresh_var : unit -> var_name.

Inductive elem_context' : Set :=
| ap_r : term -> elem_context'.
Definition elem_context := elem_context'.
Definition context := list elem_context.
Definition empty := nil : context.
Definition atom_plug (t : term) (ec : elem_context) : term :=
match ec with
| ap_r t0 => App t t0
end.
Definition plug (t : term) (c : context) := fold_left atom_plug c t.
Definition compose (c0 c1 : context) : context := app c0 c1.

Lemma plug_compose : forall c1 c2 r, plug r (compose c1 c2) = plug (plug r c1) c2.
Proof.
apply fold_left_app.
Qed.

Lemma plug_empty : forall t, plug t empty = t.
Proof.
auto.
Qed.

Lemma compose_empty : forall c, compose c empty = c.
Proof.
symmetry; apply app_nil_end.
Qed.

Definition contract (r : redex) (c : context) : option (term * context) :=
match r with
  | rApp v t => match v with
                   | vVar x => None
                   | vLam x t0 => Some (subst t0 x t, c)
                 end
  | rAb t => Some (t, empty)
  | rCall t => let z := fresh_var tt in Some (App t (Lam z (A (plug (Var z) c))), empty)
end.

(*Lemma decompose : forall t : term, (exists v : value, t = v) \/
                    (exists r : redex, exists c : context, plug r c = t).
Proof with auto.
induction t; simpl; [ left; split with (v_var v) | left; split with (v_lam v t) | right  | right | right ]; auto.
elim IHt1; intros.
destruct H as [v H]; exists (beta v t2); exists empty; simpl; subst; auto.
destruct H as [r [c H]]; exists r; exists (compose c (ap_r t2 empty)); rewrite plug_compose; simpl; subst; auto.
exists (ab_red t); exists empty...
exists (call_red t); exists empty...
Qed.
*)
Inductive decomp : Set :=
| d_val : value -> decomp
| d_red : redex -> context -> decomp.

  Inductive interm_dec : Set :=
  | in_red : redex -> interm_dec
  | in_val : value -> interm_dec
  | in_term: term -> elem_context -> interm_dec.

  Definition only_empty (t : term) : Prop := forall t' c, plug t' c = t -> c = empty.
  Definition only_trivial (t : term) : Prop := forall t' c, plug t' c = t -> c = empty \/ exists v, t' = value_to_term v.

Lemma value_trivial : forall v : value, only_trivial (value_to_term v).
Proof with auto.
intros v t c; generalize dependent t; induction c; simpl in *; auto; right.
destruct (IHc _ H) as [H0 | [v0 H0]]; subst; simpl in *;
match goal with [Hv : atom_plug ?t ?a = _ ?v |- _] => destruct a; destruct v; inversion Hv; subst end;
match goal with [ |- exists u, _ ?v = _ u] => exists v end...
Qed.

Lemma redex_trivial : forall r : redex, only_trivial (redex_to_term r).
Proof with auto.
intros r t c; generalize dependent t; induction c; simpl in *; auto; right.
destruct (IHc _ H) as [H0 | [v H0]]; subst; simpl in H; match goal with
[Hvr : atom_plug ?t ?a = _ ?v |- _] => destruct a; destruct v; inversion Hvr; subst end;
match goal with [ |- exists u, _ ?v = _ u] => exists v end...
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
  intros; destruct t.
  mlr (vVar v).
  mlr (vLam v t).
  ot_v t1 (ap_r t2); mlr (rApp v t2).
  mlr (rAb t).
  mlr (rCall t).
Qed.

Definition decomp_to_term (d : decomp) : term :=
  match d with
    | d_val v => value_to_term v
    | d_red r c0 => plug (redex_to_term r) c0
  end.

End CallByName.

Module CallByName_RefLang <: RED_REF_LANG_CS CallByName.

Module R := CallByName.

(** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
Definition dec_term : R.term -> R.interm_dec :=
fun t => match t with
  | R.Var vname => R.in_val (R.vVar vname)
  | R.Lam vname s => R.in_val (R.vLam vname s)
  | R.App t s => R.in_term t (R.ap_r s)
  | R.A t0 => R.in_red (R.rAb t0)
  | R.C t0 => R.in_red (R.rCall t0)
end.

Definition dec_context (ec : R.elem_context) (v : R.value) : R.interm_dec :=
match ec with
  | R.ap_r t => R.in_red (R.rApp v t)
end.

Lemma dec_term_value : forall (v:R.value), dec_term (v:R.term) = R.in_val v.
Proof.
destruct v; simpl; auto.
Qed.
Hint Resolve dec_term_value.

(*Lemma dec_context_not_value : forall (v v0 : value) (c c0 : context), ~dec_context v c = in_val v0 c0.
Proof with auto.
intros; destruct c; discriminate.
Qed.
Hint Resolve dec_context_not_value.*)

  Inductive subterm_one_step : R.term -> R.term -> Prop :=
  | st_1 : forall t t0 ec (DECT : t = R.atom_plug t0 ec), subterm_one_step t0 t.
  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    prove_st_wf.
  Qed.

  Definition subterm_order := clos_trans_n1 R.term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_r _ _ wf_st1.

  Definition ec_order : R.elem_context -> R.elem_context -> Prop := fun _ _ => False.
  Notation " a <: b " := (ec_order a b) (at level 40).
  Lemma wf_eco : well_founded ec_order.
  Proof.
    prove_ec_wf.
  Qed.

  Lemma dec_term_red_empty  : forall t r, dec_term t = R.in_red r -> R.only_empty t.
  Proof.
    intros t r H; destruct t; inversion H; subst; clear H;
    intros t0 c0; generalize dependent t0; induction c0; simpl in *; auto; intros;
    assert (hh := IHc0 _ H); subst c0; destruct a; inversion H.
  Qed.
  Lemma dec_term_val_empty  : forall t v, dec_term t = R.in_val v -> R.only_empty t.
    intros t v H; destruct t; inversion H; subst; clear H;
    intros t0 c0; generalize dependent t0; induction c0; simpl in *; auto; intros;
    assert (hh := IHc0 _ H); subst c0; destruct a; inversion H.
  Qed.
  Lemma dec_term_term_top   : forall t t' ec, dec_term t = R.in_term t' ec -> forall ec', ~ec <: ec'.
  Proof.
    intros t t' ec H; destruct t; inversion H; subst; clear H; destruct ec'; intro H; inversion H.
  Qed.
  Lemma dec_context_red_bot : forall ec v r, dec_context ec v = R.in_red r -> forall ec', ~ ec' <: ec.
  Proof.
    intros ec v r H; destruct ec; inversion H; subst; clear H; destruct ec'; intro H; inversion H.
  Qed.
  Lemma dec_context_val_bot : forall ec v v', dec_context ec v = R.in_val v' -> forall ec', ~ ec' <: ec.
  Proof.
    intros ec v v0 H; destruct ec; inversion H.
  Qed.
  Lemma dec_context_term_next : forall ec v t ec', dec_context ec v = R.in_term t ec' -> ec' <: ec /\ forall ec'', ec'' <: ec -> ~ ec' <: ec''.
  Proof.
    intros ec v t ec' H; destruct ec; inversion H.
  Qed.

  Lemma dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t' ec => R.atom_plug t' ec = t
    end.
  Proof.
    destruct t; simpl; auto.
  Qed.
  Lemma dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v' => R.value_to_term v' = R.atom_plug (R.value_to_term v) ec
    | R.in_term t ec' => R.atom_plug t ec' = R.atom_plug (R.value_to_term v) ec
    end.
  Proof.
    destruct ec; simpl; auto.
  Qed.

  Lemma ec_order_antisym : forall ec ec0, ec <: ec0 -> ~ ec0 <: ec.
  Proof.
    intros ec ec0 H; destruct ec; destruct ec0; inversion H.
  Qed.
  Lemma dec_ec_ord : forall t0 t1 ec0 ec1, R.atom_plug t0 ec0 = R.atom_plug t1 ec1 -> ec0 <: ec1 \/ ec1 <: ec0 \/ (t0 = t1 /\ ec0 = ec1).
  Proof.
    destruct ec0; destruct ec1; intro H; inversion H; subst; auto.
  Qed.
  Lemma elem_context_det : forall t0 t1 ec0 ec1, ec0 <: ec1 -> R.atom_plug t0 ec0 = R.atom_plug t1 ec1 ->
    exists v, t1 = R.value_to_term v.
  Proof.
    destruct ec0; destruct ec1; intro H; inversion H.
  Qed.

End CallByName_RefLang.

Module CallByNameCCRefSem := RedRefSemCS CallByName CallByName_RefLang.
Module CBNCC_PE_RefSem <: PE_REF_SEM (CallByName).

Module Red_Sem <: RED_REF_SEM_CS CallByName := CallByNameCCRefSem.

Lemma dec_context_not_val : forall v v0 ec, ~(Red_Sem.dec_context ec v = CallByName.in_val v0).
Proof.
  intro v; destruct v0; destruct ec; intro H; inversion H.
Qed.

Lemma dec_term_value : forall v, Red_Sem.dec_term (CallByName.value_to_term v) = CallByName.in_val v.
Proof.
  destruct v; auto.
Qed.

End CBNCC_PE_RefSem.

Module CBNCC_PEM := ProperPEMachineCS CallByName CBNCC_PE_RefSem.

(*Inductive dec : term -> context -> decomp -> Prop :=
| d_dec  : forall (t : term) (c : context) (d : decomp),
               dec_term t c = in_dec d -> dec t c d
| d_v    : forall (t : term) (c c0 : context) (v : value) (d : decomp),
               dec_term t c = in_val v c0 -> decctx v c0 d -> dec t c d
| d_term : forall (t t0 : term) (c c0 : context) (d : decomp),
               dec_term t c = in_term t0 c0 -> dec t0 c0 d -> dec t c d
with decctx : value -> context -> decomp -> Prop :=
| dc_dec  : forall (v : value) (c : context) (d : decomp),
              dec_context v c = in_dec d -> decctx v c d
| dc_val  : forall (v v0 : value) (c c0 : context) (d : decomp),
              dec_context v c = in_val v0 c0 -> decctx v0 c0 d -> decctx v c d
| dc_term : forall (v : value) (c c0 : context) (t : term) (d : decomp),
              dec_context v c = in_term t c0 -> dec t c0 d -> decctx v c d.

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

(** A redex in context will only ever be reduced to itself *)
Lemma dec_redex_self : forall (r : redex) (c : context), dec (redex_to_term r) c (d_red r c).
Proof with auto.
intros; induction r.
constructor 3 with (v:term) (ap_r t c); simpl...
constructor 2 with (ap_r t c) v; try apply dec_term_value; constructor 1; simpl...
constructor; simpl...
constructor; simpl...
Qed.

(** dec is left inverse of plug *)
Definition decomp_to_term (d : decomp) : term :=
match d with
  | d_val v => value_to_term v
  | d_red r c0 => plug (redex_to_term r) c0
end.
Lemma dec_term_correct : forall t c, match dec_term t c with
  | in_dec d => decomp_to_term d = plug t c
  | in_val v c0 => plug (value_to_term v) c0 = plug t c
  | in_term t0 c0 => plug t0 c0 = plug t c
end.
Proof with auto.
induction t; simpl...
Qed.

Lemma dec_context_correct : forall v c, match dec_context v c with
  | in_dec d => decomp_to_term d = plug (value_to_term v) c
  | in_val v0 c0 => plug (value_to_term v0) c0 = plug (value_to_term v) c
  | in_term t c0 => plug t c0 = plug (value_to_term v) c
end.
Proof with auto.
induction c; simpl...
Qed.

Lemma dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
Proof.
induction c; simpl; auto; intros c0 t0 d X; assert (hh := IHc _ _ _ X).
inversion hh; subst; inversion H; try discriminate; subst; auto.
Qed.

Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
Proof with auto.
induction c; simpl; auto; intros; apply IHc.
econstructor 3; eauto; simpl...
Qed.

End CallByName.

Module CBN_PEM := ProperPEMachine (CallByName).
Module CBN_Eval := Evaluator (CallByName).
Definition eval_CBN := CBN_Eval.eval.
Definition eval_CBN_PEM := CBN_PEM.REV.eval.

Lemma eval_equiv : forall t v, eval_CBN t v <-> eval_CBN_PEM t v.
Proof with eauto.
intros; split; intros; inversion_clear H; inversion_clear H0;
econstructor; try (econstructor; eauto; fail);
clear H; induction H1; try (constructor; fail);
inversion_clear H0; econstructor; eauto; constructor...
Qed.*)

Module KrivineMachineCallCC <: ABSTRACT_MACHINE.

Definition term := CallByName.term.
Definition value := CallByName.value.
Definition redex := CallByName.redex.
Definition context := CallByName.context.
Definition Var := CallByName.Var.
Definition Lam := CallByName.Lam.
Definition App := CallByName.App.
Definition A := CallByName.A.
Definition C := CallByName.C.
Definition vVar := CallByName.vVar.
Definition vLam := CallByName.vLam.
Definition rApp := CallByName.rApp.
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

Definition configuration := CBNCC_PEM.configuration.
Definition c_init := CBNCC_PEM.c_init.
Definition c_eval := CBNCC_PEM.c_eval.
Definition c_final := CBNCC_PEM.c_final.
Notation " [I a ] " := (c_init a) (at level 40).
Notation " [E a , b ] " := (c_eval a b) (at level 40).
Notation " [F a ] " := (c_final a) (at level 40).

Definition fresh_var := CallByName.fresh_var.

Reserved Notation " c1 → c2 " (at level 30).

Inductive trans : configuration -> configuration -> Prop :=
| t_init : forall t:term, [I t] → [E t, empty]
| t_mt   : forall v:value, [E v:term, empty] → [F v]
| t_abort: forall (t : term) (c : context), [E (A t), c] → [E t, empty]
| t_call : forall (t : term) (c : context),
             let x := fresh_var tt in [E (C t), c] → [E (App t (Lam x (A (plug (Var x) c)))), empty]
| t_app  : forall (t s:term) (c:context),
             [E (App t s), c] → [E t, ap_r s :: c]
| t_val  : forall (v:value) (t0 t:term) (c : context)
             (CONTR : contract (rApp v t0) c = Some (t, c)),
             [E v:term, ap_r t0 :: c] → [E t, c]
where " c1 → c2 " := (trans c1 c2).
Definition transition := trans.

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
| multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

Notation " c1 →+ c2 " := (trans_close c1 c2) (at level 35).
Notation " c1 >> c2 " := (CBNCC_PEM.AM.transition c1 c2) (at level 30).
Notation " c1 >>+ c2 " := (CBNCC_PEM.AM.trans_close c1 c2) (at level 35).

Lemma trPE_K : forall c c0, c >> c0 -> c → c0.
Proof with auto.
intros c c0 H; inversion H; subst.
(* init *)
constructor.
(* red *)
destruct t; simpl; simpl in DT; inversion DT; subst;
clear DT; simpl in CONTR; inversion CONTR; subst; clear CONTR; constructor.
(* val -> final *)
destruct t; simpl; simpl in DT; inversion DT; subst;
[cutrewrite (CallByName.Var v0 = value_to_term (vVar v0)) |
cutrewrite (CallByName.Lam v0 t = value_to_term (vLam v0 t))]; auto; constructor.
(* val -> red *)
destruct t; simpl in DT; inversion DT;
destruct ec; simpl in DC; inversion DC; subst;
inversion CONTR; subst.
cutrewrite (CallByName.Lam v0 t = value_to_term (vLam v0 t)); auto; constructor...
(* val -> term, nonexistent *)
destruct ec; discriminate DC.
(* term *)
destruct t; inversion DT; subst; constructor.
Qed.
Hint Resolve trPE_K.

Lemma tcPE_K : forall c c0, c >>+ c0 -> c →+ c0.
Proof.
intros c c0 H; induction H; subst; [ constructor 1 | econstructor 2]; try apply trPE_K; eauto.
Qed.

Lemma evalPE_K : forall t v, CBNCC_PEM.AM.eval t v -> eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcPE_K; auto.
Qed.
Hint Resolve evalPE_K.

Lemma trK_PE : forall c c0, c → c0 -> c >> c0.
Proof with eauto.
intros c c0 H; inversion H; subst; try (econstructor; simpl; eauto; fail);
[constructor | econstructor 4]; simpl...
Qed.
Hint Resolve trK_PE.

Lemma tcK_PE : forall c c0, c →+ c0 -> c >>+ c0.
Proof.
induction 1; [ constructor 1 | econstructor 2]; eauto.
Qed.

Lemma evalK_PE : forall t v, eval t v -> CBNCC_PEM.AM.eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcK_PE; auto.
Qed.
Hint Resolve evalK_PE.

Theorem KrivineMachineCorrect : forall t v, CallByNameCCRefSem.RS.eval t v <-> eval t v.
Proof.
intros t v; rewrite CBNCC_PEM.push_enter_correct; split; auto.
Qed.

End KrivineMachineCallCC.
