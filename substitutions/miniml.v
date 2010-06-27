Require Import refocusing_substitutions.
Require Import Setoid.

Module MiniML <: RED_LANG.

Definition v_name := nat.

Inductive expr :=
| Z : expr
| S : expr -> expr
| App : expr -> expr -> expr
| Var : v_name -> expr
| Lam : v_name -> expr -> expr
| Case: expr -> expr -> v_name -> expr -> expr
| Letv: v_name -> expr -> expr -> expr
| Fix : v_name -> expr -> expr
| Pair: expr -> expr -> expr
| Fst : expr -> expr
| Snd : expr -> expr.
Definition term := expr.

Inductive val :=
| vZ : val
| vS : val -> val
| vLam : v_name -> term -> val
| vVar : v_name -> val
| vPair : val -> val -> val.
Definition value := val.

Inductive red :=
| rApp : value -> value -> red
| rLet : v_name -> value -> expr -> red
| rFix : v_name -> term -> red
| rFst : value -> red
| rSnd : value -> red
| rCase: value -> expr -> v_name -> expr -> red.
Definition redex := red.

Inductive ec :=
| s_c : ec
| ap_l : value -> ec
| ap_r : expr -> ec
| case_c : expr -> v_name -> expr -> ec
| let_c : v_name -> expr -> ec
| fst_c : ec
| snd_c : ec
| pair_l : value -> ec
| pair_r : expr -> ec.
Definition elem_context := ec.

Definition context := list elem_context.
Definition empty : context := nil.

Fixpoint value_to_term (v : value) : term :=
match v with
| vZ => Z
| vS v => S (value_to_term v)
| vLam x e => Lam x e
| vVar x => Var x
| vPair vl vr => Pair (value_to_term vl) (value_to_term vr)
end.
Coercion value_to_term : value >-> term.
Fixpoint redex_to_term (r : redex) : term :=
match r with
| rApp vl vr => App (vl:term) (vr:term)
| rLet x v t => Letv x (v:term) t
| rFix x v => Fix x (v:term)
| rFst v => Fst (v:term)
| rSnd v => Snd (v:term)
| rCase v ez x es => Case (v:term) ez x es
end.
Coercion redex_to_term : redex >-> term.
Lemma value_to_term_injective : forall v v' : value, value_to_term v = value_to_term v' -> v = v'.
Proof with auto.
induction v; destruct v'; simpl; intro H; inversion H; f_equal...
Qed.
Hint Resolve value_to_term_injective : miniml.
Lemma redex_to_term_injective : forall r r' : redex, redex_to_term r = redex_to_term r' -> r = r'.
Proof with auto with miniml.
induction r; destruct r'; simpl; intro H; inversion H; f_equal...
Qed.
Hint Resolve redex_to_term : miniml.

  (** The main functions of reduction semantics, defining plugging terms into contexts and
      composing contexts, effectively defining reduction semantics, and some properties. *)
  Definition compose (c0 c1 : context) : context := app c0 c1.
  Definition atom_plug (t : term) (ec : elem_context) : term :=
  match ec with
  | s_c => S t
  | ap_l v => App (v:term) t
  | ap_r e => App t e
  | case_c ez x es => Case t ez x es
  | let_c x e => Letv x t e
  | fst_c => Fst t
  | snd_c => Snd t
  | pair_l v => Pair (v:term) t
  | pair_r e => Pair t e
  end.
  Definition plug (t : term) (c : context) : term := fold_left atom_plug c t.

  Parameter subst : v_name -> expr -> expr -> expr.

  (** The other main function of reduction semantics -- contraction of a redex into a term *)
  Definition contract (r : redex) : option term :=
  match r with
  | rApp (vLam x e) vr => Some (subst x (vr:term) e)
  | rLet x v e => Some (subst x (v:term) e)
  | rFix x e => Some (subst x (Fix x e) e)
  | rFst (vPair vl vr) => Some (value_to_term vl)
  | rSnd (vPair vl vr) => Some (value_to_term vr)
  | rCase vZ ez x es => Some ez
  | rCase (vS v) ez x es => Some (subst x (value_to_term v) es)
  | _ => None
  end.

  (** Datatype of decompositions -- either a value or a redex in a context (analogous to the decompose lemma) *)
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
  Proof with auto.
    intros v t c; generalize dependent t; induction c; simpl in *; auto; right.
    intros; destruct (IHc _ H) as [H0 | [v0 H0]]; subst; simpl in *;
    match goal with [Hv : atom_plug ?t ?a = _ ?v |- _] => destruct a; destruct v; inversion Hv; subst end;
    match goal with [ |- exists u, _ ?v = _ u] => exists v end...
  Qed.
  Lemma redex_trivial : forall r : redex, only_trivial (redex_to_term r).
  Proof with auto.
    intros r t c; generalize dependent t; induction c; simpl in *; auto; intros; right;
    destruct (IHc _ H) as [H0 | [v H0]]; subst; simpl in H; match goal with
    [Hvr : atom_plug ?t ?a = _ ?v |- _] => destruct a; destruct v; inversion Hvr; subst end;
    match goal with [ |- exists u, _ ?v = _ u] => exists v end...
  Qed.
  Lemma value_redex : forall (v : value) (r : redex), value_to_term v <> redex_to_term r.
  Proof with auto.
    destruct v; destruct r; intro H; discriminate H.
  Qed.

  Lemma ot_subt : forall t t0 ec, only_trivial t -> atom_plug t0 ec = t -> exists v, t0 = value_to_term v.
  Proof with auto.
    intros; destruct (H t0 (ec0 :: nil)) as [H1 | [v H1]]...
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
  Proof with auto.
    intros; destruct t.
    mlr vZ.
    ot_v t s_c; mlr (vS v).
    ot_v t1 (ap_r t2); ot_v t2 (ap_l v); mlr (rApp v v0).
    mlr (vVar v).
    mlr (vLam v t).
    ot_v t1 (case_c t2 v t3); mlr (rCase v0 t2 v t3).
    ot_v t1 (let_c v t2); mlr (rLet v v0 t2).
    mlr (rFix v t).
    ot_v t1 (pair_r t2); ot_v t2 (pair_l v); mlr (vPair v v0).
    ot_v t fst_c; mlr (rFst v).
    ot_v t snd_c; mlr (rSnd v).
  Qed.

End MiniML.

Module MiniMLRef <: RED_REF_LANG.

  Module R := MiniML.

  Definition dec_term (t : R.term) : R.interm_dec :=
  match t with
  | R.Z              =>  R.in_val R.vZ
  | R.S t            =>  R.in_term t R.s_c
  | R.App t1 t2      =>  R.in_term t1 (R.ap_r t2)
  | R.Var x          =>  R.in_val (R.vVar x)
  | R.Lam x t        =>  R.in_val (R.vLam x t)
  | R.Case t ez x es =>  R.in_term t (R.case_c ez x es)
  | R.Letv x t e     =>  R.in_term t (R.let_c x e)
  | R.Fix x t        =>  R.in_red (R.rFix x t)
  | R.Pair t1 t2     =>  R.in_term t1 (R.pair_r t2)
  | R.Fst t          =>  R.in_term t R.fst_c
  | R.Snd t          =>  R.in_term t R.snd_c
  end.
  Definition dec_context (ec : R.elem_context) (v : R.value) : R.interm_dec :=
  match ec with
  | R.s_c            =>  R.in_val (R.vS v)
  | R.ap_l v0        =>  R.in_red (R.rApp v0 v)
  | R.ap_r t         =>  R.in_term t (R.ap_l v)
  | R.case_c ez x es =>  R.in_red (R.rCase v ez x es)
  | R.let_c x e      =>  R.in_red (R.rLet x v e)
  | R.fst_c          =>  R.in_red (R.rFst v)
  | R.snd_c          =>  R.in_red (R.rSnd v)
  | R.pair_l v0      =>  R.in_val (R.vPair v0 v)
  | R.pair_r t       =>  R.in_term t (R.pair_l v)
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

  Definition ec_order (ec ec0 : R.elem_context) : Prop :=
  match ec, ec0 with
  | R.ap_l _, R.ap_r _ => True
  | R.pair_l _, R.pair_r _ => True
  | _, _ => False
  end.
  Notation " a <: b " := (ec_order a b) (at level 40).
  Lemma wf_eco : well_founded ec_order.
  Proof.
    prove_ec_wf.
  Qed.

  Lemma dec_term_red_empty  : forall t r, dec_term t = R.in_red r -> R.only_empty t.
  Proof with auto.
    intros t r H; destruct t; inversion H; subst; clear H;
    intros t0 c; generalize dependent t0; induction c; intros; simpl in *; auto;
    assert (hh := IHc _ H); subst c; destruct a; inversion H.
  Qed.

  Lemma dec_term_val_empty  : forall t v, dec_term t = R.in_val v -> R.only_empty t.
  Proof.
    intros t r H; destruct t; inversion H; subst; clear H;
    intros t0 c; generalize dependent t0; induction c; intros; simpl in *; auto;
    assert (hh := IHc _ H); subst c; destruct a; inversion H.
  Qed.

  Lemma dec_term_term_top   : forall t t' ec, dec_term t = R.in_term t' ec -> forall ec', ~ec <: ec'.
  Proof.
    intros t t' ec H ec' H0; destruct t; inversion H; subst; destruct ec'; inversion H0.
  Qed.

  Lemma dec_context_red_bot : forall ec v r, dec_context ec v = R.in_red r -> forall ec', ~ ec' <: ec.
  Proof with auto.
    intros ec v r H ec' H0; destruct ec; inversion H; destruct ec'; inversion H0.
  Qed.

  Lemma dec_context_val_bot : forall ec v v', dec_context ec v = R.in_val v' -> forall ec', ~ ec' <: ec.
  Proof.
    intros ec v v' H ec' H0; destruct ec; inversion H; destruct ec'; inversion H0.
  Qed.

  Lemma eco_antirefl : forall ec, ~ec <: ec.
  Proof.
    destruct ec; intro H; destruct H.
  Qed.

  Lemma ec_order_antisym : forall ec ec0, ec <: ec0 -> ~ ec0 <: ec.
  Proof.
    intros ec ec0 H; destruct ec; destruct ec0; inversion H; subst; intro H0; inversion H0.
  Qed.

  Ltac inj_vr := match goal with
  | [Hv : R.value_to_term _ = R.value_to_term _ |- _] => apply R.value_to_term_injective in Hv
  | [Hr : R.redex_to_term _ = R.redex_to_term _ |- _] => apply R.redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.

  Lemma elem_context_det : forall t0 t1 ec0 ec1, ec0 <: ec1 -> R.atom_plug t0 ec0 = R.atom_plug t1 ec1 ->
    exists v, t1 = R.value_to_term v.
  Proof.
    intros; destruct ec0; destruct ec1; inversion H0; inj_vr;
    subst; try (contradiction (eco_antirefl _ H)); match goal with
    | [ |- exists v0, _ ?v = _ v0] => exists v; reflexivity
    | [ H : ( _ <: _) |- _] => inversion H
    end.
  Qed.

  Lemma dec_context_term_next : forall ec v t ec', dec_context ec v = R.in_term t ec' -> ec' <: ec /\ forall ec'', ec'' <: ec -> ~ ec' <: ec''.
  Proof with eauto.
    intros ec v t ec' H; destruct ec; inversion H; subst; split; try constructor; intros ec'' H0 H1; destruct ec''; inversion H0; inversion H1.
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

  Lemma dec_ec_ord : forall t0 t1 ec0 ec1, R.atom_plug t0 ec0 = R.atom_plug t1 ec1 -> ec0 <: ec1 \/ ec1 <: ec0 \/ (t0 = t1 /\ ec0 = ec1).
  Proof with eauto.
    intros t0 t1 ec0 ec1 H; destruct ec0; destruct ec1; inversion H; inj_vr; subst;
    intuition constructor.
  Qed.

End MiniMLRef.

Module MiniML_REF_SEM := RedRefSem MiniMLRef.
Module MiniML_EAM := ProperEAMachine MiniML MiniML_REF_SEM.

Module MiniML_Sem <: RED_SEM MiniML.

  Inductive dec' : MiniML.term -> MiniML.context -> MiniML.decomp -> Prop :=
  | d_z   : forall c d
              (DCTX : decctx MiniML.vZ c d),
              dec' MiniML.Z c d
  | d_s   : forall t c d
              (DEC  : dec' t (MiniML.s_c :: c) d),
              dec' (MiniML.S t) c d
  | d_case: forall t ez x es c d
              (DEC  : dec' t (MiniML.case_c ez x es :: c) d),
              dec' (MiniML.Case t ez x es) c d
  | d_var : forall x c d
              (DCTX : decctx (MiniML.vVar x) c d),
              dec' (MiniML.Var x) c d
  | d_lam : forall x t c d
              (DCTX : decctx (MiniML.vLam x t) c d),
              dec' (MiniML.Lam x t) c d
  | d_app : forall t1 t2 c d
              (DEC  : dec' t1 (MiniML.ap_r t2 :: c) d),
              dec' (MiniML.App t1 t2) c d
  | d_let : forall x t e c d
              (DEC  : dec' t (MiniML.let_c x e :: c) d),
              dec' (MiniML.Letv x t e) c d
  | d_fix : forall x t c,
              dec' (MiniML.Fix x t) c (MiniML.d_red (MiniML.rFix x t) c)
  | d_pair: forall t1 t2 c d
              (DEC  : dec' t1 (MiniML.pair_r t2 :: c) d),
              dec' (MiniML.Pair t1 t2) c d
  | d_fst : forall t c d
              (DEC  : dec' t (MiniML.fst_c :: c) d),
              dec' (MiniML.Fst t) c d
  | d_snd : forall t c d
              (DEC  : dec' t (MiniML.snd_c :: c) d),
              dec' (MiniML.Snd t) c d
  with decctx : MiniML.value -> MiniML.context -> MiniML.decomp -> Prop :=
  | dc_em : forall v,
              decctx v MiniML.empty (MiniML.d_val v)
  | dc_s  : forall v c d
              (DCTX : decctx (MiniML.vS v) c d),
              decctx v (MiniML.s_c :: c) d
  | dc_cs : forall v x ez es c,
              decctx v (MiniML.case_c ez x es :: c) (MiniML.d_red (MiniML.rCase v ez x es) c)
  | dc_apr: forall v t c d
              (DEC  : dec' t (MiniML.ap_l v :: c) d),
              decctx v (MiniML.ap_r t :: c) d
  | dc_apl: forall v v0 c,
              decctx v (MiniML.ap_l v0 :: c) (MiniML.d_red (MiniML.rApp v0 v) c)
  | dc_let: forall v x e c,
              decctx v (MiniML.let_c x e :: c) (MiniML.d_red (MiniML.rLet x v e) c)
  | dc_p_r: forall t v c d
              (DEC  : dec' t (MiniML.pair_l v :: c) d),
              decctx v (MiniML.pair_r t :: c) d
  | dc_p_l: forall v v0 c d
              (DCTX : decctx (MiniML.vPair v0 v) c d),
              decctx v (MiniML.pair_l v0 :: c) d
  | dc_fst: forall v c,
              decctx v (MiniML.fst_c :: c) (MiniML.d_red (MiniML.rFst v) c)
  | dc_snd: forall v c,
              decctx v (MiniML.snd_c :: c) (MiniML.d_red (MiniML.rSnd v) c).
  Definition dec := dec'.
  Scheme dec_Ind := Induction for dec' Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Lemma dec_val_self : forall v c d, dec (MiniML.value_to_term v) c d <-> decctx v c d.
  Proof with auto.
    induction v;(intros; split; intro H;
    [ inversion H; subst; auto; try rewrite IHv in DEC; try rewrite IHv1 in DEC; inversion DEC; auto; rewrite IHv2 in DEC0; inversion DEC0; subst
    | constructor; auto; try rewrite IHv; try rewrite IHv1; constructor; auto; rewrite IHv2; constructor])...
  Qed.

  (** A redex in context will only ever be reduced to itself *)
  Lemma dec_redex_self : forall (r : MiniML.redex) (c : MiniML.context), dec (MiniML.redex_to_term r) c (MiniML.d_red r c).
  Proof with auto.
    induction r; intros; constructor; rewrite dec_val_self; constructor; rewrite dec_val_self; constructor.
  Qed.

  Lemma decompose : forall t : MiniML.term, (exists v:MiniML.value, t = MiniML.value_to_term v) \/
      (exists r:MiniML.redex, exists c:MiniML.context, MiniML.plug (MiniML.redex_to_term r) c = t).
  Proof with auto with miniml.
    induction t.
    left; exists MiniML.vZ...
    destruct IHt as [[v H] | [r [c H]]]; [left; exists (MiniML.vS v) | right; exists r; exists (c ++ (MiniML.s_c :: nil))];
    subst; simpl; unfold MiniML.plug; auto; apply fold_left_app.
    right; destruct IHt1 as [[v1 H] | [r1 [c1 H]]]; [destruct IHt2 as [[v2 H2] | [r2 [c2 H2]]];
    [exists (MiniML.rApp v1 v2); exists MiniML.empty | exists r2; exists (c2 ++ (MiniML.ap_l v1 :: MiniML.empty))] |
    exists r1; exists (c1 ++ (MiniML.ap_r t2 :: MiniML.empty))]; simpl; subst; auto; unfold MiniML.plug; apply fold_left_app.
    left; exists (MiniML.vVar v)...
    left; exists (MiniML.vLam v t)...
    clear IHt2 IHt3; destruct IHt1 as [[v1 H] | [r [c H]]]; [ right; exists (MiniML.rCase v1 t2 v t3); exists MiniML.empty |
    right; exists r; exists (c ++ (MiniML.case_c t2 v t3 :: MiniML.empty))]; subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    clear IHt2; destruct IHt1 as [[v1 H] | [r [c H]]]; [right; exists (MiniML.rLet v v1 t2); exists MiniML.empty | right;
    exists r; exists (c ++ (MiniML.let_c v t2 :: MiniML.empty))]; subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    clear IHt; right; exists (MiniML.rFix v t); exists MiniML.empty; simpl; auto.
    destruct IHt1 as [[v1 H1] | [r1 [c1 H1]]]; [destruct IHt2 as [[v2 H2] | [r2 [c2 H2]]]; [left; exists (MiniML.vPair v1 v2) |
    right; exists r2; exists (c2 ++ (MiniML.pair_l v1 :: nil))] | right; exists r1; exists (c1 ++ (MiniML.pair_r t2 :: nil))];
    subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    destruct IHt as [[v H] | [r [c H]]]; right; [ exists (MiniML.rFst v); exists MiniML.empty | exists r; exists (c ++ (MiniML.fst_c :: nil)) ];
    subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
    destruct IHt as [[v H] | [r [c H]]]; right; [ exists (MiniML.rSnd v); exists MiniML.empty | exists r; exists (c ++ (MiniML.snd_c :: nil)) ];
    subst; simpl; auto; unfold MiniML.plug; apply fold_left_app.
  Qed.

  (** dec is left inverse of plug *)
  Lemma dec_correct : forall t c d, dec t c d -> MiniML.decomp_to_term d = MiniML.plug t c.
  Proof.
    induction 1 using dec_Ind with
    (P := fun t c d (H:dec t c d) => MiniML.decomp_to_term d = MiniML.plug t c)
    (P0 := fun v c d (H:decctx v c d) => MiniML.decomp_to_term d = MiniML.plug (MiniML.value_to_term v) c); intros; simpl; auto.
  Qed.

  Lemma dec_plug : forall c c0 t d, dec (MiniML.plug t c) c0 d -> dec t (MiniML.compose c c0) d.
  Proof.
    induction c; simpl; auto; destruct a; intros c0 t0 d DEC; assert (hh := IHc _ _ _ DEC); 
    inversion hh; subst; auto; rewrite dec_val_self in DEC0; inversion DEC0; subst; auto.
  Qed.

  Lemma dec_plug_rev : forall c c0 t d, dec t (MiniML.compose c c0) d -> dec (MiniML.plug t c) c0 d.
  Proof.
    induction c; simpl; auto; destruct a; intros; apply IHc;
    repeat (constructor; simpl; auto; try rewrite dec_val_self).
  Qed.

  Inductive decempty : MiniML.term -> MiniML.decomp -> Prop :=
  | d_intro : forall t d (DEC : dec t MiniML.empty d), decempty t d.

  Inductive iter : MiniML.decomp -> MiniML.value -> Prop :=
  | i_val : forall v, iter (MiniML.d_val v) v
  | i_red : forall r t c d v
              (CONTR : MiniML.contract r = Some t)
              (D_EM  : decempty (MiniML.plug t c) d)
              (R_IT  : iter d v),
              iter (MiniML.d_red r c) v.

  Inductive eval : MiniML.term -> MiniML.value -> Prop :=
  | e_intro : forall t d v
                (D_EM : decempty t d)
                (ITER : iter d v),
                eval t v.

End MiniML_Sem.

Lemma dec_sem_ref : forall t c d, MiniML_Sem.dec t c d -> MiniML_REF_SEM.dec t c d.
Proof.
  induction 1 using MiniML_Sem.dec_Ind with
  (P := fun t c d (H : MiniML_Sem.dec t c d) => MiniML_REF_SEM.dec t c d)
  (P0:= fun v c d (H : MiniML_Sem.decctx v c d) => MiniML_REF_SEM.decctx v c d); intros; simpl in *; auto;
  [ econstructor | econstructor 3 | econstructor 3 | econstructor | econstructor 2 | econstructor 3 | econstructor 3
  | econstructor | econstructor 3 | econstructor 3 | econstructor 3 | constructor | econstructor | constructor
  | econstructor 4 | constructor | constructor | econstructor 4 | econstructor | constructor | constructor]; simpl; eauto.
Qed.
Hint Resolve dec_sem_ref.

Lemma dec_ref_sem : forall t c d, MiniML_REF_SEM.dec t c d -> MiniML_Sem.dec t c d.
Proof.
  induction 1 using MiniML_REF_SEM.dec_Ind with
  (P := fun t c d (H : MiniML_REF_SEM.dec t c d) => MiniML_Sem.dec t c d)
  (P0:= fun v c d (H : MiniML_REF_SEM.decctx v c d) => MiniML_Sem.decctx v c d); intros; simpl in *; auto;
  try (constructor; fail);
  try (destruct t; inversion DT; subst; constructor; auto);
  destruct ec; inversion DC; subst; constructor; auto.
Qed.
Hint Resolve dec_ref_sem.

Lemma iter_sem_ref : forall d v, MiniML_Sem.iter d v <-> MiniML_REF_SEM.RS.iter d v.
Proof with eauto with miniml.
destruct d; split; intros H; induction H; subst; simpl in *; auto; try constructor;
inversion_clear D_EM; econstructor 2; simpl in *; eauto; constructor; unfold MiniML_REF_SEM.RS.dec...
Qed.

Lemma eval_sem_ref : forall t v, MiniML_Sem.eval t v <-> MiniML_REF_SEM.RS.eval t v.
Proof with auto.
split; intro H; inversion_clear H; econstructor; inversion_clear D_EM; [ constructor | 
rewrite <- iter_sem_ref | constructor | rewrite iter_sem_ref]; unfold MiniML_REF_SEM.RS.dec in *; eauto.
Qed.

Module MiniML_Machine <: ABSTRACT_MACHINE.

Definition term := MiniML.term.
Definition value := MiniML.value.

Definition configuration := MiniML_EAM.configuration.
Definition c_init := MiniML_EAM.c_init.
Definition c_final := MiniML_EAM.c_final.
Definition c_eval := MiniML_EAM.c_eval.
Definition c_apply := MiniML_EAM.c_apply.

Notation " [ a ] " := (c_init a) (at level 60, no associativity).
Notation " [: a :] " := (c_final a) (at level 60).
Notation " [ a , b ] " := (c_eval a b) (at level 60).
Notation " [: a , b :] " := (c_apply a b) (at level 60).

Reserved Notation " a → b " (at level 40).

Inductive trans : configuration -> configuration -> Prop :=
| t_init : forall t,           [ t ] →  [t, MiniML.empty]
| t_final: forall v,           [: MiniML.empty, v :] → [: v :]
| t_ez   : forall c,           [MiniML.Z, c] → [: c, MiniML.vZ :]
| t_es   : forall t c,         [MiniML.S t, c] → [t, MiniML.s_c :: c]
| t_evar : forall x c,         [MiniML.Var x, c] → [: c, MiniML.vVar x :]
| t_elam : forall x t c,       [MiniML.Lam x t, c] → [: c, MiniML.vLam x t :]
| t_eapp : forall t1 t2 c,     [MiniML.App t1 t2, c] → [t1, MiniML.ap_r t2 :: c]
| t_ecas : forall t ez x es c, [MiniML.Case t ez x es, c] → [t, MiniML.case_c ez x es :: c]
| t_efix : forall x t t0 c
             (CTR : MiniML.contract (MiniML.rFix x t) = Some t0),
             [MiniML.Fix x t, c] → [t0, c]
| t_elet : forall x t e c,     [MiniML.Letv x t e, c] → [t, MiniML.let_c x e :: c]
| t_epar : forall t1 t2 c,     [MiniML.Pair t1 t2, c] → [t1, MiniML.pair_r t2 :: c]
| t_efst : forall t c,         [MiniML.Fst t, c] → [t, MiniML.fst_c :: c]
| t_esnd : forall t c,         [MiniML.Snd t, c] → [t, MiniML.snd_c :: c]
| t_as   : forall v c,         [: MiniML.s_c :: c, v :] → [: c, MiniML.vS v :]
| t_aa_r : forall v t c,       [: MiniML.ap_r t :: c, v :] → [t, MiniML.ap_l v :: c]
| t_aa_l : forall v v0 t c
             (CTR : MiniML.contract (MiniML.rApp v0 v) = Some t),
             [: MiniML.ap_l v0 :: c, v :] → [t, c]
| t_acas : forall v ez x es c t
             (CTR : MiniML.contract (MiniML.rCase v ez x es) = Some t),
             [: MiniML.case_c ez x es :: c, v :] → [t, c]
| t_alet : forall v x e c t
             (CTR : MiniML.contract (MiniML.rLet x v e) = Some t),
             [: MiniML.let_c x e :: c, v :] → [t, c]
| t_ap_r : forall v t c,       [: MiniML.pair_r t :: c, v :] → [t, MiniML.pair_l v :: c]
| t_ap_l : forall v v0 c,      [: MiniML.pair_l v0 :: c, v :] → [: c, MiniML.vPair v0 v :]
| t_afst : forall v c t
             (CTR : MiniML.contract (MiniML.rFst v) = Some t),
             [: MiniML.fst_c :: c, v :] → [t, c]
| t_asnd : forall v c t
             (CTR : MiniML.contract (MiniML.rSnd v) = Some t),
             [: MiniML.snd_c :: c, v :] → [t, c]
where " a → b " := (trans a b).
Definition transition := trans.

Notation " a >> b " := (MiniML_EAM.transition a b) (at level 40).
Notation " a >>+ b " := (MiniML_EAM.AM.trans_close a b) (at level 40).

Reserved Notation " a →+ b " (at level 40, no associativity).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step   : forall c0 c1 (STEP : c0 → c1), c0 →+ c1
| multi_step : forall c0 c1 c2 (STEP : c0 → c1) (REC : c1 →+ c2), c0 →+ c2
where " a →+ b " := (trans_close a b).

Inductive eval : term -> value -> Prop :=
| e_intro : forall t v (TC : [ t ] →+ [: v :]), eval t v.

Lemma trans_eam_mlm : forall c0 c1, c0 >> c1 -> c0 → c1.
Proof with auto.
  intros c0 c1 T; inversion T; subst; match goal with
  | [ DT : MiniML_EAM.dec_term ?t = ?int |- _ ] => destruct t; inversion DT
  | [ DC : MiniML_EAM.dec_context ?ec ?v = ?int |- _ ] => destruct ec; inversion DC
  | [ |- _ ] => idtac
  end; subst; constructor...
Qed.
Hint Resolve trans_eam_mlm.

Lemma tcl_eam_mlm : forall c0 c1, c0 >>+ c1 -> c0 →+ c1.
Proof with eauto.
  intros c0 c1 TC; induction TC; subst; unfold MiniML_EAM.AM.transition in *;
  [econstructor | econstructor 2]...
Qed.

Lemma eval_eam_mlm : forall t v, MiniML_EAM.AM.eval t v -> eval t v.
Proof.
  intros t v E; inversion_clear E; constructor; apply tcl_eam_mlm; auto.
Qed.

Lemma trans_mlm_eam : forall c0 c1, c0 → c1 -> c0 >> c1.
Proof with auto.
  intros w w' H; inversion H; subst; econstructor; simpl...
Qed.
Hint Resolve trans_mlm_eam.

Lemma tcl_mlm_eam : forall c0 c1, c0 →+ c1 -> c0 >>+ c1.
Proof with eauto.
  induction 1; subst; [econstructor | econstructor 2]; unfold MiniML_EAM.AM.transition...
Qed.

Lemma eval_mlm_eam : forall t v, eval t v -> MiniML_EAM.AM.eval t v.
Proof.
  intros t v E; inversion_clear E; constructor; apply tcl_mlm_eam; auto.
Qed.

Theorem MiniML_Machine_correct : forall t v, MiniML_Sem.eval t v <-> eval t v.
Proof.
  intros; rewrite eval_sem_ref; rewrite MiniML_EAM.eval_apply_correct;
  split; [apply eval_eam_mlm | apply eval_mlm_eam].
Qed.

End MiniML_Machine.
