Require Import refocusing_substitutions_cs.

Module CallByValue <: RED_LANG_CS.

Require Import List.

Parameter var_name : Set.

Inductive term' : Set :=
| Var : var_name -> term'
| Lam : var_name -> term' -> term'
| App : term' -> term' -> term'
| A : term' -> term'
| C : term' -> term'.
Definition term := term'.

Inductive value' : Set :=
| vVar : var_name -> value'
| vLam : var_name -> term -> value'.
Definition value := value'.

Inductive redex' : Set :=
| rApp : value -> value -> redex'
| rA   : term -> redex'
| rC   : term -> redex'.
Definition redex := redex'.

Definition value_to_term (v : value) : term :=
match v with
| vVar v' => Var v'
| vLam v' t => Lam v' t
end.
Coercion value_to_term : value >-> term.

Lemma value_to_term_injective : forall v v', value_to_term v = value_to_term v' -> v = v'.
Proof.
destruct v; destruct v'; intro H; inversion H; auto.
Qed.

Definition redex_to_term (r : redex) : term :=
match r with
| rApp v v0 => App (v:term) (v0:term)
| rA t => A t
| rC t => C t
end.
Coercion redex_to_term : redex >-> term.

Lemma redex_to_term_injective : forall r r', redex_to_term r = redex_to_term r' -> r = r'.
Proof.
destruct r; destruct r'; intro H; inversion H; auto;
apply value_to_term_injective in H2; apply value_to_term_injective in H1; subst; auto.
Qed.

Ltac uncast_vr :=
match goal with
| [ H: value_to_term ?v = value_to_term ?v0 |- _ ] => apply value_to_term_injective in H
| [ H: redex_to_term ?r = redex_to_term ?r0 |- _ ] => apply redex_to_term_injective in H
| [ |- _ ] => idtac
end.

Parameter subst : term -> var_name -> term -> term.
Parameter fresh_var : unit -> var_name.

Inductive elem_context' :=
| ap_r : term  -> elem_context'
| ap_l : value -> elem_context'.
Definition elem_context := elem_context'.
Definition context := list elem_context.
Definition empty := nil : context.
Definition atom_plug (t : term) (ec : elem_context) : term :=
match ec with
| ap_r t0 => App t t0
| ap_l v  => App (v : term) t
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
  | rApp v v0 => match v with
                   | vVar x => None
                   | vLam x t0 => Some (subst t0 x v0, c)
                 end
  | rA t => Some (t, empty)
  | rC t => let z := fresh_var tt in Some (App t (Lam z (A (plug (Var z) c))), empty)
end.

(*
Lemma decompose : forall t : term, (exists v : value, t = v) \/
                    (exists r : redex, exists c : context, plug r c = t).
Proof with auto.
induction t; simpl; [ left; split with (v_var v) | left; split with (v_lam v t) | right | right | right ]...
elim IHt1; intros.
destruct H as [v H]; elim IHt2; intros.
destruct H0 as [v0 H0]; subst; split with (beta v v0); split with mt; auto.
destruct H0 as [r [c H0]]; subst; split with r; split with (compose c (ap_l v mt)); rewrite plug_compose; auto.
destruct H as [r [c H]]; split with r; split with (compose c (ap_r t2 mt)); rewrite plug_compose; rewrite H; auto.
exists (ab_red t); exists empty...
exists (call_red t); exists empty...
Qed.*)

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
destruct (IHc _ H) as [H0 | [v0 H0]]; subst; simpl in *; match goal with
[H: atom_plug ?t ?a = value_to_term ?v |- _ ] => destruct a; destruct v; discriminate
end.
Qed.

Lemma redex_trivial : forall r : redex, only_trivial (redex_to_term r).
Proof with eauto.
intros r t c; generalize dependent t; induction c; simpl in *; auto; right.
destruct (IHc _ H) as [H0 | [v H0]]; subst; simpl in H; match goal with
[H: atom_plug ?t ?a = _ ?vr |- _ ] => destruct a; destruct vr; inversion H
end...
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

Hint Constructors value' redex' term' elem_context'.

Lemma trivial_val_red : forall t : term, only_trivial t ->
    (exists v : value, t = value_to_term v) \/ (exists r : redex, t = redex_to_term r).
Proof.
  intros; destruct t.
  mlr (vVar v).
  mlr (vLam v t).
  ot_v t1 (ap_r t2); ot_v t2 (ap_l v); mlr (rApp v v0).
  mlr (rA t).
  mlr (rC t).
Qed.

Definition decomp_to_term (d : decomp) : term :=
  match d with
    | d_val v => value_to_term v
    | d_red r c0 => plug (redex_to_term r) c0
  end.

End CallByValue.

Module CallByValue_RefLang <: RED_REF_LANG_CS CallByValue.

  Import CallByValue.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term (t : term) : interm_dec :=
  match t with
    | Var vname => in_val (vVar vname)
    | Lam vname s => in_val (vLam vname s)
    | App t s => in_term t (ap_r s)
    | A t0 => in_red (rA t0)
    | C t0 => in_red (rC t0)
  end.

  Definition dec_context (ec : elem_context) (v : value) : interm_dec :=
  match ec with
    | ap_r t  => in_term t (ap_l v)
    | ap_l v0 => in_red (rApp v0 v)
  end.

  Lemma dec_term_value : forall (v:value), dec_term (v:term) = in_val v.
  Proof.
    destruct v; simpl; auto.
  Qed.
  Hint Resolve dec_term_value.

  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 ec (DECT : t = atom_plug t0 ec), subterm_one_step t0 t.
  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    prove_st_wf.
  Qed.

  Definition subterm_order := clos_trans_n1 term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_r _ _ wf_st1.

  Definition ec_order (ec ec0 : elem_context) : Prop :=
  match ec, ec0 with
  | ap_l v, ap_r t => True
  | _, _ => False
  end.
  Notation " a <: b " := (ec_order a b) (at level 40).
  Lemma wf_eco : well_founded ec_order.
  Proof.
    prove_ec_wf.
  Qed.

  Lemma dec_term_red_empty  : forall t r, dec_term t = in_red r -> only_empty t.
  Proof.
    destruct t; intros r H; inversion H; subst; clear H;
    intros t0 c0; generalize dependent t0; induction c0; simpl in *; auto; intros;
    assert (hh := IHc0 _ H); subst c0; destruct a; inversion H.
  Qed.
  Lemma dec_term_val_empty  : forall t v, dec_term t = in_val v -> only_empty t.
    intros t v H; destruct t; inversion H; subst; clear H;
    intros t0 c0; generalize dependent t0; induction c0; simpl in *; auto; intros;
    assert (hh := IHc0 _ H); subst c0; destruct a; inversion H.
  Qed.
  Lemma dec_term_term_top   : forall t t' ec, dec_term t = in_term t' ec -> forall ec', ~ec <: ec'.
  Proof.
    intros t t' ec H; destruct t; inversion H; subst; clear H; destruct ec'; intro H; inversion H.
  Qed.
  Lemma dec_context_red_bot : forall ec v r, dec_context ec v = in_red r -> forall ec', ~ ec' <: ec.
  Proof.
    intros ec v r H; destruct ec; inversion H; subst; clear H; destruct ec'; intro H; inversion H.
  Qed.
  Lemma dec_context_val_bot : forall ec v v', dec_context ec v = in_val v' -> forall ec', ~ ec' <: ec.
  Proof.
    intros ec v v0 H; destruct ec; inversion H.
  Qed.
  Lemma dec_context_term_next : forall ec v t ec', dec_context ec v = in_term t ec' -> ec' <: ec /\ forall ec'', ec'' <: ec -> ~ ec' <: ec''.
  Proof.
    intros ec v t ec' H; destruct ec; inversion H; subst; split; simpl; try destruct ec''; auto.
  Qed.

  Lemma dec_term_correct : forall t, match dec_term t with
  | in_red r => redex_to_term r = t
  | in_val v => value_to_term v = t
  | in_term t0 ec => atom_plug t0 ec = t
  end.
  Proof.
    destruct t; simpl; auto.
  Qed.

  Lemma dec_context_correct : forall ec v, match dec_context ec v with
  | in_red r  => redex_to_term r = atom_plug (value_to_term v) ec
  | in_val v0 => value_to_term v0 = atom_plug (value_to_term v) ec
  | in_term t ec0 => atom_plug t ec0 = atom_plug (value_to_term v) ec
  end.
  Proof.
    destruct ec; simpl; auto.
  Qed.

  Lemma ec_order_antisym : forall ec ec0, ec <: ec0 -> ~ ec0 <: ec.
  Proof.
    intros ec ec0 H; destruct ec; destruct ec0; inversion H; auto.
  Qed.
  Lemma dec_ec_ord : forall t0 t1 ec0 ec1, atom_plug t0 ec0 = atom_plug t1 ec1 -> ec0 <: ec1 \/ ec1 <: ec0 \/ (t0 = t1 /\ ec0 = ec1).
  Proof.
    destruct ec0; destruct ec1; intro H; inversion H; uncast_vr; subst; intuition constructor.
  Qed.
  Lemma elem_context_det : forall t0 t1 ec0 ec1, ec0 <: ec1 -> atom_plug t0 ec0 = atom_plug t1 ec1 ->
    exists v, t1 = value_to_term v.
  Proof.
    destruct ec0; destruct ec1; intros H H0; inversion H; simpl in *; injection H0; eauto.
  Qed.

End CallByValue_RefLang.

Module CallByValueCC_RefSem := RedRefSemCS CallByValue CallByValue_RefLang.
Module CBVCC_EAM := ProperEAMachineCS CallByValue CallByValueCC_RefSem.

Module CKMachine <: ABSTRACT_MACHINE.

Import CallByValue.

Definition term := term.
Definition value := value.
Definition value_to_term : value -> term := value_to_term.
Coercion value_to_term : value >-> term.

Definition configuration := CBVCC_EAM.configuration.
Definition c_init := CBVCC_EAM.c_init.
Definition c_eval := CBVCC_EAM.c_eval.
Definition c_apply := CBVCC_EAM.c_apply.
Definition c_final := CBVCC_EAM.c_final.

Definition fresh_var := CallByValue.fresh_var.

Notation " [I a ] " := (c_init a).
Notation " [E t , c ] " := (c_eval t c).
Notation " [A c , v ] " := (c_apply c v).
Notation " [F v ] " := (c_final v).

Reserved Notation " c → c0 " (at level 30, no associativity).

Inductive trans : configuration -> configuration -> Prop :=
| t_init : forall t : term, [I t ] → [E t, empty]
| t_val  : forall (v : value) (c : context), [E v:term, c] → [A c, v]
| t_app  : forall (t s : term) (c : context), [E App t s, c] → [E t, ap_r s :: c]
| t_abort: forall (t : term) (c : context), [E A t, c] → [E t, empty]
| t_call : forall (t : term) (c : context),
             let x := fresh_var tt in [E C t, c] → [E App t (Lam x (A (plug (Var x) c))), empty]
| t_empty: forall v : value, [A empty, v] → [F v]
| t_ap_r : forall (t : term) (v : value) (c : context), [A ap_r t :: c, v] → [E t, ap_l v :: c]
| t_ap_l : forall (v v0 : value) (c : context) (t : term)
             (CTR : contract (rApp v0 v) c = Some (t, c)),
             [A ap_l v0 :: c, v] → [E t, c]
where " c → c0 " := (trans c c0).
Definition transition := trans.

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
| multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

Notation " c1 →+ c2 " := (trans_close c1 c2) (at level 35).
Notation " c1 >> c2 " := (CBVCC_EAM.AM.transition c1 c2) (at level 30).
Notation " c1 >>+ c2 " := (CBVCC_EAM.AM.trans_close c1 c2) (at level 35).

Lemma trEA_CK : forall c c0 : configuration, c >> c0 -> c → c0.
Proof with eauto.
intros c c0 H; inversion H; subst.
(* init *)
constructor.
(* e -> red *)
destruct t; try discriminate; inversion DT; subst; inversion CONTR; subst; constructor.
(* e -> val *)
destruct t; inversion DT; subst;
[ cutrewrite (Var v0 = value_to_term (vVar v0))
| cutrewrite (Lam v0 t = value_to_term (vLam v0 t))]; auto; constructor.
(* e -> term *)
destruct t; inversion DT; subst; constructor.
(* a -> final *)
constructor.
(* a -> red *)
destruct ec; inversion DC; subst; destruct v0; inversion CONTR; subst; constructor...
(* a -> val (disc) *)
destruct ec; discriminate.
(* a -> term *)
destruct ec; inversion DC; subst; constructor.
Qed.
Hint Resolve trEA_CK.

Lemma tcEA_CK : forall c c0 : configuration, c >>+ c0 -> c →+ c0.
Proof.
intros w w' H; induction H; subst; [ constructor 1 | econstructor 2]; eauto; apply trEA_CK; auto.
Qed.

Lemma evalEA_CK : forall t v, CBVCC_EAM.AM.eval t v -> eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcEA_CK; auto.
Qed.
Hint Resolve evalEA_CK.

Hint Constructors CBVCC_EAM.transition.
Hint Unfold CBVCC_EAM.AM.transition.

Lemma trCK_EA : forall c c0 : configuration, c → c0 -> c >> c0.
Proof with eauto.
intros c c0 H; inversion H; subst; eauto; econstructor; simpl...
Qed.
Hint Resolve trCK_EA.

Lemma tcCK_EA : forall c c0 : configuration, c →+ c0 -> c >>+ c0.
Proof.
induction 1; [ constructor 1 | econstructor 2]; eauto.
Qed.

Lemma evalCK_EA : forall t v, eval t v -> CBVCC_EAM.AM.eval t v.
Proof.
intros t v H; inversion H; constructor; apply tcCK_EA; auto.
Qed.
Hint Resolve evalCK_EA.

Theorem CKMachineCorrect : forall (t : term) (v : value), CallByValueCC_RefSem.RS.eval t v <-> eval t v.
Proof.
intros t v; rewrite CBVCC_EAM.eval_apply_correct; split; auto.
Qed.

End CKMachine.
