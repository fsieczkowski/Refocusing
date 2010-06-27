Require Import refocusing_trace_substitutions.
Require Import Setoid.

Module Arith_Lang <: RED_LANG.

  Parameter var_name : Set.

  Inductive term' : Set :=
  | num  : nat -> term'
  | plus : term' -> term' -> term'
  | times: term' -> term' -> term'
  | var  : var_name -> term'.
  Definition term := term'.

  Inductive value' : Set :=
  | v_num : nat -> value'.
  Definition value := value'.

  Inductive redex' : Set :=
  | r_plus  : value -> value -> redex'
  | r_times : value -> value -> redex'
  | r_var   : var_name -> redex'.
  Definition redex := redex'.

  Definition value_to_term (v : value) : term :=
  match v with
  | v_num v' => num v'
  end.
  Coercion value_to_term : value >-> term.

  Lemma value_to_term_injective : forall v v', value_to_term v = value_to_term v' -> v = v'.
  Proof.
  intros v v0; case v; case v0; simpl; intros; try discriminate; injection H;
  intros; subst; auto.
  Qed.

  Definition redex_to_term (r : redex) : term :=
  match r with
  | r_plus m n => plus (m:term) (n:term)
  | r_times m n => times (m:term) (n:term)
  | r_var x => var x
  end.
  Coercion redex_to_term : redex >-> term.

  Lemma redex_to_term_injective : forall r r', redex_to_term r = redex_to_term r' -> r = r'.
  Proof with auto.
  intros r r0; case r; case r0; intros; try discriminate; injection H; intros;
  try (rewrite (value_to_term_injective _ _ H1); rewrite (value_to_term_injective _ _ H0))...
  rewrite H0...
  Qed.

  Parameter env : var_name -> nat.

  Inductive elem_context' : Set :=
  | plus_r : term -> elem_context'
  | plus_l : value -> elem_context'
  | times_r : term -> elem_context'
  | times_l : value -> elem_context'.
  Definition elem_context := elem_context'.
  Definition context := list elem_context.
  Definition empty : context := nil.

  Definition atom_plug (t : term) (ec : elem_context) :=
  match ec with
  | plus_r t' => plus t t'
  | plus_l v => plus (v:term) t
  | times_r t' =>times t t'
  | times_l v => times (v:term) t
  end.
  Definition compose (c0 c1 : context) : context := app c0 c1.
  Definition plug (t : term) (c : context) : term := fold_left atom_plug c t.

  Lemma plug_compose : forall c1 c2 r, plug r (compose c1 c2) = plug (plug r c1) c2.
  Proof.
  induction c1; simpl; auto.
  Qed.

  Definition contract (r : redex) : option term :=
  match r with
  | r_plus (v_num n) (v_num m) => Some (num (n+m))
  | r_times (v_num n) (v_num m) => Some (num (n*m))
  | r_var x => Some (num (env x))
  end.

  Lemma decompose : forall t : term, (exists v : value, t = v) \/
                      (exists r : redex, exists c : context, plug r c = t).
  Proof with auto.
    induction t; simpl.
    left; exists (v_num n); auto.
    right; elim IHt1; intros.
    destruct H as [v1 H]; subst.
    elim IHt2; intros.
    destruct H as [v2 H]; subst.
    exists (r_plus v1 v2); exists empty; simpl...
    destruct H as [r [c H]]; exists r; exists (compose c (plus_l v1 :: empty)); rewrite plug_compose; simpl; subst; auto.
    destruct H as [r [c H]]; exists r; exists (compose c (plus_r t2 :: empty)); rewrite plug_compose; simpl; subst; auto.
    right; elim IHt1; intros.
    destruct H as [v1 H]; subst.
    elim IHt2; intros.
    destruct H as [v2 H]; subst.
    exists (r_times v1 v2); exists empty; simpl...
    destruct H as [r [c H]]; exists r; exists (compose c (times_l v1 :: empty)); rewrite plug_compose; simpl; subst; auto.
    destruct H as [r [c H]]; exists r; exists (compose c (times_r t2 :: empty)); rewrite plug_compose; simpl; subst; auto.
    right; exists (r_var v); exists empty; simpl...
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
    intros v t c; left; generalize dependent t; induction c; simpl in *; auto;
    destruct v; destruct a; destruct c; intros; simpl in *; try discriminate H; discriminate (IHc _ H).
  Qed.
  Lemma redex_trivial : forall r : redex, only_trivial (redex_to_term r).
  Proof.
    intros r t c; generalize dependent t; induction c; intros; [left; auto | right]; destruct a;( simpl in *;
    destruct (IHc _ H) as [H0 | [v0 H0]]; subst;[ destruct r; inversion H; subst;
    match goal with [ |- exists u, _ ?v = _ u ] => exists v; reflexivity end | destruct v0; discriminate]).
  Qed.
  Lemma value_redex : forall (v : value) (r : redex), value_to_term v <> redex_to_term r.
  Proof.
    destruct v; destruct r; intro; discriminate.
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
  Proof with auto.
    destruct t; intros.
    mlr (v_num n).
    ot_v t1 (plus_r t2); ot_v t2 (plus_l v); mlr (r_plus v v0).
    ot_v t1 (times_r t2); ot_v t2 (times_l v); mlr (r_times v v0).
    mlr (r_var v).
  Qed.

End Arith_Lang.

Module Arith_Sem <: RED_SEM_T Arith_Lang.
  Import Arith_Lang.

  Inductive dec' : term -> context -> decomp -> Prop :=
  | t_var : forall (x : var_name) (c : context), dec' (var x) c (d_red (r_var x) c)
  | t_num : forall (n : nat) (c : context) (d : decomp),
              decctx' (v_num n) c d -> dec' (num n) c d
  | t_plus: forall (t0 t1 : term) (c : context) (d : decomp),
              dec' t0 (plus_r t1 :: c) d -> dec' (plus t0 t1) c d
  | t_mul : forall (t0 t1 : term) (c : context) (d : decomp),
              dec' t0 (times_r t1 :: c) d -> dec' (times t0 t1) c d
  with decctx' : value -> context -> decomp -> Prop :=
  | c_empty : forall (v : value), decctx' v empty (d_val v)
  | c_plus_r: forall (v : value) (t : term) (c : context) (d : decomp),
                dec' t (plus_l v :: c) d -> decctx' v (plus_r t :: c) d
  | c_plus_l: forall (v v0 : value) (c : context), decctx' v (plus_l v0 :: c) (d_red (r_plus v0 v) c)
  | c_mul_r : forall (v : value) (t : term) (c : context) (d : decomp),
                dec' t (times_l v :: c) d -> decctx' v (times_r t :: c) d
  | c_mul_l : forall (v v0 : value) (c : context), decctx' v (times_l v0 :: c) (d_red (r_times v0 v) c).

  Definition dec := dec'.
  Definition decctx := decctx'.

  Scheme dec_Ind := Induction for dec' Sort Prop
  with decctx_Ind := Induction for decctx' Sort Prop.

  (** dec is left inverse of plug *)
  Lemma dec_correct : forall t c d, dec t c d -> decomp_to_term d = plug t c.
  Proof.
    induction 1 using dec_Ind with
    (P := fun t c d (H : dec t c d) => decomp_to_term d = plug t c)
    (P0:= fun v c d (H : decctx v c d) => decomp_to_term d = plug v c); simpl; auto.
  Qed.

  (** A redex in context will only ever be reduced to itself *)
  Lemma dec_redex_self : forall (r : redex) (c : context), dec (redex_to_term r) c (d_red r c).
  Proof.
    intro; case r; intros; constructor; destruct v; destruct v0; repeat constructor.
  Qed.

  Lemma dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
  Proof with auto.
    induction c; intros; simpl in *; auto; destruct a;
    assert (hh := IHc _ _ _ H); inversion hh; subst; auto;
    destruct v; inversion H4; subst; inversion H1; subst...
  Qed.

  Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
  Proof with auto.
    induction c; intros; simpl in *; auto; destruct a;
    try (destruct v); apply IHc; repeat constructor...
  Qed.

  Inductive decempty : term -> decomp -> Prop :=
  | d_intro : forall (t : term) (d : decomp), dec t empty d -> decempty t d.
  Definition trace := stream decomp.

  CoInductive gather : decomp -> trace -> Prop :=
  | i_val : forall (v : value), gather (d_val v) (s_cons (d_val v) s_nil)
  | i_red : forall (r : redex) (t : term) (c : context) (d : decomp) (tr : trace),
              contract r = Some t -> decempty (plug t c) d -> gather d tr -> gather (d_red r c) (s_cons (d_red r c) tr).

  CoInductive eval : term -> trace -> Prop :=
  | e_intro : forall (t : term) (d : decomp) (tr : trace), decempty t d -> gather d tr -> eval t tr.

  Definition decompose := Arith_Lang.decompose.

End Arith_Sem.

Module Arith_Ref_Lang <: RED_REF_LANG.

  Module R := Arith_Lang.
  Import Arith_Lang.

  Definition dec_term (t : term) : interm_dec :=
  match t with
  | var vname => in_red (r_var vname)
  | num n => in_val (v_num n)
  | plus n m => in_term n (plus_r m)
  | times n m => in_term n (times_r m)
  end.
  Definition dec_context : elem_context -> value -> interm_dec :=
  fun (ec : elem_context) (v : value) => match ec with
  | plus_r n => in_term n (plus_l v)
  | plus_l v' => in_red (r_plus v' v)
  | times_r n => in_term n (times_l v)
  | times_l v' => in_red (r_times v' v)
  end.

  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 ec (DECT : t = atom_plug t0 ec), subterm_one_step t0 t.
  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    prove_st_wf.
  Qed.

  Definition subterm_order := clos_trans_n1 term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40).
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_r _ _ wf_st1.

(*  Inductive elem_context_one_step : R.elem_context -> R.elem_context -> Prop :=
  | ec_1 : forall ec ec0 v t (DECEC : dec_context ec v = R.in_term t ec0), 
             elem_context_one_step ec0 ec.

  Ltac wf_ec_step :=
  constructor; match goal with
    | [ |- forall u (T:?eco u _), Acc ?eco u ] => intros y T; inversion T as [ec ec0 ?t ?v ?Hcc]; subst ec ec0; clear T
  end; match goal with 
    | [ Hcc : dec_context _ _ = R.in_term _ ?cc |- Acc ?eco ?cc] => inversion Hcc; subst; clear Hcc
  end.

  Ltac prove_ec_wf := intro a; destruct a; repeat wf_ec_step.

  Lemma wf_ec1 : well_founded elem_context_one_step.
  Proof.
    prove_ec_wf.
  Qed.

  Definition ec_order := clos_trans_1n _ elem_context_one_step.
  Notation " a <: b " := (ec_order a b) (at level 40).
  Definition wf_eco : well_founded ec_order := wf_clos_trans_l _ _ wf_ec1.*)

  Definition ec_order (ec0 ec1 : elem_context) : Prop :=
  match ec0, ec1 with
  | plus_l _, plus_r _ => True
  | times_l _, times_r _ => True
  | _, _ => False
  end.
  Notation " a <: b " := (ec_order a b) (at level 40).
  Lemma wf_eco : well_founded ec_order.
  Proof.
    prove_ec_wf.
  Qed.

  Lemma dec_term_red_empty  : forall t r, dec_term t = in_red r -> only_empty t.
  Proof.
    intros t r H; destruct t; inversion H; subst; intros t c; generalize t; induction c; intros;
    simpl in *; auto; clear H; assert (ht := IHc _ H0); subst c; destruct a; inversion H0.
  Qed.
  Lemma dec_term_val_empty : forall t v, dec_term t = in_val v -> only_empty t.
  Proof.
    intros t v H; destruct t; inversion H; subst; intros t c; generalize t; induction c; intros;
    simpl in *; auto; clear H; assert (ht := IHc _ H0); subst c; destruct a; inversion H0.
  Qed.

  Lemma dec_term_term_top   : forall t t' ec, dec_term t = in_term t' ec -> forall ec', ~ ec <: ec'.
  Proof.
    intros t t' ec H ec' H0; destruct t; inversion H; subst; destruct ec'; inversion H0.
  Qed.
  Lemma dec_context_red_bot : forall ec v r, dec_context ec v = in_red r -> forall ec', ~ec' <: ec.
  Proof.
    intros ec v r H ec' H0; destruct ec; inversion H; subst; destruct ec'; inversion H0.
  Qed.
  Lemma dec_context_val_bot : forall ec v v0, dec_context ec v = in_val v0 -> forall ec', ~ec' <: ec.
  Proof.
    intros ec v r H ec' H0; destruct ec; inversion H; subst; destruct ec'; inversion H0.
  Qed.
  Lemma dec_context_term_next : forall ec v t ec', dec_context ec v = in_term t ec' -> ec' <: ec /\ forall ec'', ec'' <: ec -> ~ec' <: ec''.
  Proof.
    intros; destruct ec; inversion H; subst; repeat constructor; intros; destruct ec''; inversion H0; intro; inversion H1.
  Qed.

  Lemma dec_term_correct : forall t, match dec_term t with
    | in_red r => redex_to_term r = t
    | in_val v => value_to_term v = t
    | in_term t' ec => atom_plug t' ec = t
    end.
  Proof.
    destruct t; simpl; auto.
  Qed.
  Lemma dec_context_correct : forall ec v, match dec_context ec v with
    | in_red r => redex_to_term r = atom_plug (value_to_term v) ec
    | in_val v0 => value_to_term v0 = atom_plug (value_to_term v) ec
    | in_term t ec' => atom_plug t ec' = atom_plug (value_to_term v) ec
    end.
  Proof.
    destruct ec; simpl; auto.
  Qed.

  Ltac inj_vr := match goal with
  | [Hv : value_to_term _ = value_to_term _ |- _] => apply value_to_term_injective in Hv
  | [Hr : redex_to_term _ = redex_to_term _ |- _] => apply redex_to_term_injective in Hr
  | [ |- _] => idtac
  end.

  Lemma ec_order_antisym : forall ec ec0, ec <: ec0 -> ~ec0 <: ec.
  Proof.
    destruct ec; destruct ec0; intros H H0; inversion H; inversion H0.
  Qed.
  Lemma dec_ec_ord : forall t0 t1 ec0 ec1, atom_plug t0 ec0 = atom_plug t1 ec1 -> ec0 <: ec1 \/ ec1 <: ec0 \/ (t0 = t1 /\ ec0 = ec1).
  Proof.
    destruct ec0; destruct ec1; intros; inversion H; inj_vr; subst; simpl in *; auto.
  Qed.
  Lemma elem_context_det : forall t0 t1 ec0 ec1, ec0 <: ec1 -> atom_plug t0 ec0 = atom_plug t1 ec1 ->
    exists v, t1 = value_to_term v.
  Proof.
    destruct ec0; destruct ec1; intros; inversion H; inversion H0; subst; exists v; auto.
  Qed.

End Arith_Ref_Lang.

(*Module Arith_Ref_Sem_Auto <: RED_REF_SEM Arith_Lang := RedRefSem Arith_Ref_Lang.*)

Module Arith_Ref_Sem <: RED_REF_SEM_T Arith_Lang.
  Import Arith_Lang.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Definition dec_term : term -> interm_dec :=
  fun (t : term) => match t with
  | var vname => in_red (r_var vname)
  | num n => in_val (v_num n)
  | plus n m => in_term n (plus_r m)
  | times n m => in_term n (times_r m)
  end.
  Definition dec_context : elem_context -> value -> interm_dec :=
  fun (ec : elem_context) (v : value) => match ec with
  | plus_r n => in_term n (plus_l v)
  | plus_l v' => in_red (r_plus v' v)
  | times_r n => in_term n (times_l v)
  | times_l v' => in_red (r_times v' v)
  end.

  Lemma dec_term_value : forall (v:value), dec_term (v:term) = in_val v.
  Proof.
    destruct v; simpl; auto.
  Qed.
  Hint Resolve dec_term_value.

  Lemma dec_term_correct : forall t, match dec_term t with
    | in_red r => redex_to_term r = t
    | in_val v => value_to_term v = t
    | in_term t0 c0 => atom_plug t0 c0 = t
  end.
  Proof.
    intro t; case t; intros; simpl; auto.
  Qed.
  Lemma dec_context_correct : forall c v, match dec_context c v with
    | in_red r => redex_to_term r = atom_plug (value_to_term v) c
    | in_val v0 => value_to_term v0 = atom_plug (value_to_term v) c
    | in_term t c0 => atom_plug t c0 = atom_plug (value_to_term v) c
  end.
  Proof.
    destruct c; intros; simpl; auto.
  Qed.
  
(*  (** A decomposition function specified in terms of the atomic functions above *)
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
                dec_context ec v = in_term t ec0 -> dec t (ec0 :: c) d -> decctx v (ec :: c) d.*)
  Inductive dec : term -> context -> decomp -> Prop :=
  | d_dec  : forall (t : term) (c : context) (r : redex),
                 dec_term t = in_red r -> dec t c (d_red r c)
  | d_v    : forall (t : term) (c : context) (v : value) (d : decomp),
                 dec_term t = in_val v -> decctx v c d -> dec t c d
  | d_term : forall (t t0 : term) (ec : elem_context) (c : context) (d : decomp),
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

  Lemma dec_red_ref : forall t c d, Arith_Sem.dec t c d <-> dec t c d.
  Proof with eauto.
    intros; split; intro.
    induction H using Arith_Sem.dec_Ind with
    (P := fun t c d (H : Arith_Sem.dec t c d) => dec t c d)
    (P0:= fun v c d (H : Arith_Sem.decctx v c d) => decctx v c d);
    [ constructor | econstructor 2 | econstructor 3 | econstructor 3 | constructor
    | econstructor 4 | constructor | econstructor 4 | constructor]; simpl...
    induction H using dec_Ind with
    (P := fun t c d (H : dec t c d) => Arith_Sem.dec t c d)
    (P0:= fun v c d (H : decctx v c d) => Arith_Sem.decctx v c d);
    try (destruct t; inversion e; subst; constructor); auto; try constructor;
    destruct ec; inversion e; subst; constructor...
  Qed.

  Module RS : RED_SEM_T Arith_Lang with Definition dec := dec.

    Definition dec := dec.

    Inductive decempty : term -> decomp -> Prop :=
    | d_intro : forall (t : term) (d : decomp), dec t empty d -> decempty t d.
    Definition trace := stream decomp.

    CoInductive gather : decomp -> trace -> Prop :=
    | i_val : forall (v : value), gather (d_val v) (s_cons (d_val v) s_nil)
    | i_red : forall (r : redex) (t : term) (c : context) (d : decomp) (tr : trace),
                contract r = Some t -> decempty (plug t c) d -> gather d tr -> gather (d_red r c) (s_cons (d_red r c) tr).

    CoInductive eval : term -> trace -> Prop :=
    | e_intro : forall (t : term) (d : decomp) (tr : trace), decempty t d -> gather d tr -> eval t tr.

    Lemma dec_redex_self : forall (r : redex) (c : context), dec (redex_to_term r) c (d_red r c).
    Proof.
      intros; rewrite <- dec_red_ref; apply Arith_Sem.dec_redex_self.
    Qed.

    (** dec is left inverse of plug *)
    Lemma dec_correct : forall t c d, dec t c d -> decomp_to_term d = plug t c.
    Proof.
      intros; apply Arith_Sem.dec_correct; rewrite dec_red_ref; auto.
    Qed.

    Lemma dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
    Proof.
      intros; rewrite <- dec_red_ref; apply Arith_Sem.dec_plug; rewrite dec_red_ref; auto.
    Qed.

    Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
    Proof.
      intros; rewrite <- dec_red_ref; apply Arith_Sem.dec_plug_rev; rewrite dec_red_ref; auto.
    Qed.
    Definition decompose := Arith_Sem.decompose.

  End RS.

  Lemma gather_red_ref : forall d v, Arith_Sem.gather d v <-> RS.gather d v.
  Proof.
    split; generalize dependent d; generalize dependent v; cofix; intros; inversion H; subst.
    repeat constructor.
    econstructor; eauto.
    constructor; rewrite <- dec_red_ref; inversion_clear H1; auto.
    repeat constructor.
    econstructor; eauto.
    inversion_clear H1; constructor; rewrite dec_red_ref; auto.
  Qed.

  Lemma eval_red_ref : forall t v, Arith_Sem.eval t v <-> RS.eval t v.
  Proof.
    split; intro; inversion_clear H; constructor 1 with d.
    constructor; inversion_clear H0; rewrite <- dec_red_ref; auto.
    rewrite <- gather_red_ref; auto.
    constructor; inversion_clear H0; rewrite dec_red_ref; auto.
    rewrite gather_red_ref; auto.
  Qed.

  Lemma dec_val_self : forall v c d, dec (Arith_Lang.value_to_term v) c d <-> decctx v c d.
  Proof.
    split; intro.
    destruct v; inversion H; inversion H0; subst; auto.
    assert (hh := dec_term_value v); econstructor; eauto.
  Qed.

End Arith_Ref_Sem.

Module Arith_PE_Sem <: PE_REF_SEM_T Arith_Lang.

  Module Red_Sem := Arith_Ref_Sem.

  Lemma dec_context_not_val : forall (v v0 : Arith_Lang.value) (ec : Arith_Lang.elem_context), ~Red_Sem.dec_context ec v = Arith_Lang.in_val v0.
  Proof.
    destruct ec; intros; simpl; intro; discriminate.
  Qed.
  Hint Resolve dec_context_not_val.
  Definition dec_term_value := Red_Sem.dec_term_value.

End Arith_PE_Sem.

Module EAM := ProperEAMachineT Arith_Lang Arith_Ref_Sem.
Module PEM := ProperPEMachineT Arith_Lang Arith_PE_Sem.

Module EAArithMachine <: ABSTRACT_MACHINE_T.
  Import Arith_Lang.

  Definition term := term.
  Definition value := value.
  Definition decomp := decomp.
  Definition configuration := EAM.configuration.
  Definition c_init := EAM.c_init.
  Definition c_eval := EAM.c_eval.
  Definition c_apply := EAM.c_apply.
  Definition c_final := EAM.c_final.

  Inductive transition' : configuration -> configuration -> option decomp -> Prop :=
  | t_init : forall t : term, transition' (c_init t) (c_eval t empty) None
  | t_val  : forall (v : value) (c : context), transition' (c_eval (value_to_term v) c) (c_apply c v) None
  | t_plus : forall (t s : term) (c : context), transition' (c_eval (plus t s) c) (c_eval t (plus_r s :: c)) None
  | t_times: forall (t s : term) (c : context), transition' (c_eval (times t s) c) (c_eval t (times_r s :: c)) None
  | t_var  : forall (x : var_name) (c : context), transition' (c_eval (var x) c) (c_eval (num (env x)) c) (Some (d_red (r_var x) c))
  | t_empty  : forall v : value, transition' (c_apply empty v) (c_final v) (Some (d_val v))
  | t_plus_r : forall (t : term) (v : value) (c : context), transition' (c_apply (plus_r t :: c) v) (c_eval t (plus_l v :: c)) None
  | t_plus_l : forall (v v0 : value) (c : context) (t : term),
                 contract (r_plus v0 v) = Some t -> transition' (c_apply (plus_l v0 :: c) v) (c_eval t c) (Some (d_red (r_plus v0 v) c))
  | t_times_r: forall (t : term) (v : value) (c : context), transition' (c_apply (times_r t :: c) v) (c_eval t (times_l v :: c)) None
  | t_times_l: forall (v v0 : value) (c : context) (t : term),
                 contract (r_times v0 v) = Some t -> transition' (c_apply (times_l v0 :: c) v) (c_eval t c) (Some (d_red (r_times v0 v) c)).

  Definition transition := transition'.
  Definition trace := stream decomp.

(*  Inductive trans_close : configuration -> configuration -> list decomp -> Prop :=
  | one_step_n   : forall (c0 c1 : configuration), transition c0 c1 None -> trans_close c0 c1 nil
  | one_step_s   : forall (c0 c1 : configuration) (d : decomp), transition c0 c1 (Some d) -> trans_close c0 c1 (d :: nil)
  | multi_step_e : forall (c0 c1 c2 : configuration) (ds : list decomp),
                     transition c0 c1 None -> trans_close c1 c2 ds -> trans_close c0 c2 ds
  | multi_step_s : forall (c0 c1 c2 : configuration) (d : decomp) (ds : list decomp),
                     transition c0 c1 (Some d) -> trans_close c1 c2 ds -> trans_close c0 c2 (d :: ds).

  Inductive eval : term -> list decomp -> Prop :=
  | e_intro : forall (t : term) (v : value) (ds : list decomp), trans_close (c_init t) (c_final v) ds -> eval t ds.*)
  Notation " a >>= b " := (match a with
    | None => b
    | Some d => (s_cons d b)
    end) (at level 40).

  CoInductive trace_m : configuration -> trace -> Prop :=
  | empty_trace : forall v : value, trace_m (c_final v) s_nil
  | trace_trans : forall (c0 c1 : configuration) (od : option decomp) (ds : trace), transition c0 c1 od -> trace_m c1 ds -> trace_m c0 (od >>= ds).

  CoInductive eval : term -> trace -> Prop :=
  | e_intro : forall (t : term) (ds : trace), trace_m (c_init t) ds -> eval t ds.

  Lemma trEA_M : forall (w w' : configuration) (d : option decomp), EAM.transition w w' d -> transition w w' d.
  Proof with eauto.
    intros w w' d H; inversion H; subst;
    try (destruct f; inversion H0; subst; constructor; auto); try constructor;
    destruct t; inversion H0; subst; try constructor.
    inversion H1; subst; constructor.
    cutrewrite (Arith_Lang.num n = value_to_term (Arith_Lang.v_num n)); [constructor | auto].
  Qed.
  Hint Resolve trEA_M.

  Lemma tcEA_M : forall (c : configuration) (ds : trace), EAM.AM.trace_m c ds -> trace_m c ds.
  Proof with eauto.
    cofix; intros; inversion H; subst; econstructor; eauto.
  Qed.

  Lemma evalEA_M : forall t ds, EAM.AM.eval t ds -> eval t ds.
  Proof.
    intros t v H; inversion H; econstructor; apply tcEA_M; eauto.
  Qed.
  Hint Resolve evalEA_M.

  Lemma trM_EA : forall (w w' : configuration) (d : option decomp), transition w w' d -> EAM.AM.transition w w' d.
  Proof with eauto.
    intros w w' d H; inversion H; subst;
    [ constructor | econstructor 3 | econstructor 4 | econstructor 4 | econstructor 2; simpl
    | constructor 5 | econstructor 8 | econstructor 6; simpl | econstructor 8 | econstructor 6; simpl]...
  Qed.
  Hint Resolve trM_EA.

  Lemma tcM_EA : forall (c : configuration) (ds : trace), trace_m c ds -> EAM.AM.trace_m c ds.
  Proof with eauto.
    cofix; intros; inversion H; econstructor...
  Qed.

  Lemma evalM_EA : forall t ds, eval t ds -> EAM.AM.eval t ds.
  Proof.
    intros t v H; inversion H; econstructor; apply tcM_EA; eauto.
  Qed.
  Hint Resolve evalM_EA.

  Theorem ArithMachineCorrect : forall (t : term) (ds : trace), Arith_Sem.eval t ds <-> eval t ds.
  Proof with auto.
    intros; rewrite Arith_Ref_Sem.eval_red_ref; rewrite EAM.eval_apply_correct; split...
  Qed.

End EAArithMachine.

Module PEArithMachine <: ABSTRACT_MACHINE_T.
  Import Arith_Lang.

  Definition term := term.
  Definition value := value.
  Definition decomp := decomp.
  Definition configuration := PEM.configuration.
  Definition c_init := PEM.c_init.
  Definition c_eval := PEM.c_eval.
  Definition c_final := PEM.c_final.

  Inductive transition' : configuration -> configuration -> option decomp -> Prop :=
  | t_init : forall t : term, transition' (c_init t) (c_eval t empty) None
  | t_plus : forall (t s : term) (c : context), transition' (c_eval (plus t s) c) (c_eval t (plus_r s :: c)) None
  | t_times: forall (t s : term) (c : context), transition' (c_eval (times t s) c) (c_eval t (times_r s :: c)) None
  | t_var  : forall (x : var_name) (c : context), transition' (c_eval (var x) c) (c_eval (num (env x)) c) (Some (d_red (r_var x) c))
  | t_empty  : forall v : value, transition' (c_eval (value_to_term v) empty) (c_final v) (Some (d_val v))
  | t_plus_r : forall (t : term) (v : value) (c : context), transition' (c_eval (value_to_term v) (plus_r t :: c)) (c_eval t (plus_l v :: c)) None
  | t_plus_l : forall (v v0 : value) (c : context) (t : term),
                 contract (r_plus v0 v) = Some t -> transition' (c_eval (value_to_term v) (plus_l v0 :: c)) (c_eval t c) (Some (d_red (r_plus v0 v) c))
  | t_times_r: forall (t : term) (v : value) (c : context), transition' (c_eval (value_to_term v) (times_r t :: c)) (c_eval t (times_l v :: c)) None
  | t_times_l: forall (v v0 : value) (c : context) (t : term),
                 contract (r_times v0 v) = Some t -> transition' (c_eval (value_to_term v) (times_l v0 :: c)) (c_eval t c) (Some (d_red (r_times v0 v) c)).

  Definition transition := transition'.
  Definition trace := stream decomp.
  Notation " a >>= b " := (match a with
    | None => b
    | Some d => (s_cons d b)
    end) (at level 40).

  CoInductive trace_m : configuration -> trace -> Prop :=
  | empty_trace : forall v : value, trace_m (c_final v) s_nil
  | trace_trans : forall (c0 c1 : configuration) (od : option decomp) (ds : trace), transition c0 c1 od -> trace_m c1 ds -> trace_m c0 (od >>= ds).

  CoInductive eval : term -> trace -> Prop :=
  | e_intro : forall (t : term) (ds : trace), trace_m (c_init t) ds -> eval t ds.

(*  Inductive trans_close : configuration -> configuration -> list decomp -> Prop :=
  | one_step_n   : forall (c0 c1 : configuration), transition c0 c1 None -> trans_close c0 c1 nil
  | one_step_s   : forall (c0 c1 : configuration) (d : decomp), transition c0 c1 (Some d) -> trans_close c0 c1 (d :: nil)
  | multi_step_e : forall (c0 c1 c2 : configuration) (ds : list decomp),
                     transition c0 c1 None -> trans_close c1 c2 ds -> trans_close c0 c2 ds
  | multi_step_s : forall (c0 c1 c2 : configuration) (d : decomp) (ds : list decomp),
                     transition c0 c1 (Some d) -> trans_close c1 c2 ds -> trans_close c0 c2 (d :: ds).

  Inductive eval : term -> list decomp -> Prop :=
  | e_intro : forall (t : term) (v : value) (ds : list decomp), trans_close (c_init t) (c_final v) ds -> eval t ds.
*)
  Lemma trPE_M : forall (w w' : configuration) (d : option decomp), PEM.transition w w' d -> transition w w' d.
  Proof with eauto.
    assert (numeq : forall (n : nat), Arith_Lang.num n = value_to_term (Arith_Lang.v_num n))...
    intros w w' d H; inversion H; subst; try constructor...
    destruct t; inversion H0; subst; inversion H1; subst; constructor.
    destruct t; inversion H0; subst; rewrite numeq; constructor.
    destruct t; inversion H0; destruct ec; inversion H1; subst; destruct v0; inversion H2; subst; rewrite numeq; constructor...
    destruct t; inversion H0; destruct ec; inversion H1; subst; rewrite numeq; constructor...
    destruct t; inversion H0; subst; constructor.
  Qed.
  Hint Resolve trPE_M.

  Lemma tcPE_M : forall (c : configuration) (ds : trace), PEM.AM.trace_m c ds -> trace_m c ds.
  Proof with eauto.
    cofix; intros; inversion H; econstructor...
  Qed.

  Lemma evalPE_M : forall t ds, PEM.AM.eval t ds -> eval t ds.
  Proof.
    intros t v H; inversion H; econstructor; apply tcPE_M; eauto.
  Qed.
  Hint Resolve evalPE_M.

  Lemma trM_PE : forall (w w' : configuration) (d : option decomp), transition w w' d -> PEM.AM.transition w w' d.
  Proof with eauto.
    intros w w' d H; inversion H; subst;
    [ constructor | econstructor 6 | econstructor 6 | econstructor 2 | econstructor 3
    | econstructor 5 | econstructor 4 | econstructor 5 | econstructor 4]; eauto; simpl...
  Qed.
  Hint Resolve trM_PE.

  Lemma tcM_PE : forall (c : configuration) (ds : trace), trace_m c ds -> PEM.AM.trace_m c ds.
  Proof with eauto.
    cofix; intros; inversion H; econstructor...
  Qed.

  Lemma evalM_PE : forall t ds, eval t ds -> PEM.AM.eval t ds.
  Proof.
    intros t ds H; inversion H; econstructor; apply tcM_PE; eauto.
  Qed.
  Hint Resolve evalM_PE.

  Theorem ArithMachineCorrect : forall (t : term) (ds : trace), Arith_Sem.eval t ds <-> eval t ds.
  Proof with auto.
    intros t v; rewrite Arith_Ref_Sem.eval_red_ref; rewrite PEM.push_enter_correct; split...
  Qed.

End PEArithMachine.
