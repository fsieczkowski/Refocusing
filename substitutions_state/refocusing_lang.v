Require Export List.
Require Export Util.

Set Implicit Arguments.
Unset Strict Implicit.

Module Type RED_LANG.

  (** The languages of terms, values, redex, and context, the empty context is also needed. *)
  Parameters term value redex frame : Set.
  Definition context := list frame.
  Definition empty : context := nil.

  (** The values and redexes are sublanguages of terms *)
  Parameter value_to_term : value -> term.
  Parameter redex_to_term : redex -> term.
  Axiom value_to_term_injective : forall v v' : value, 
    value_to_term v = value_to_term v' -> v = v'.
  Axiom redex_to_term_injective : forall r r' : redex,
    redex_to_term r = redex_to_term r' -> r = r'.

  (** The main functions of reduction semantics, defining plugging terms into contexts and
      composing contexts, effectively defining reduction semantics, and some properties. *)
  Definition compose (c0 c1 : context) : context := app c0 c1.
  Parameter atom_plug : term -> frame -> term.
  Definition plug (t : term) (c : context) : term := fold_left atom_plug c t.

  (** The other main function of reduction semantics -- contraction of a redex into a term *)
  Parameter state : Set.
  Parameter init : state.
  Definition answer := (value * state)%type.
  Parameter contract : redex -> state -> option (term * state).

  Notation " E '[' t ']'"   := (plug t E) (at level 40) : red_scope.
  Notation " E '·' E1 "     := (compose E E1)
    (at level 40, left associativity) : red_scope.
  Notation " f 'a[' t ']' " := (atom_plug t f) (at level 40) : red_scope.
  Notation " [] " := empty : red_scope.
  Delimit Scope red_scope with red.
  Open Scope red_scope.

  Definition only_empty (t : term)   := forall t' E, E [t'] = t -> E = [].
  Definition only_trivial (t : term) := forall t' E, E [t'] = t ->
    E = [] \/ exists v, t' = value_to_term v.

  Axiom value_trivial : forall v : value, only_trivial (value_to_term v).
  Axiom redex_trivial : forall r : redex, only_trivial (redex_to_term r).
  Axiom value_redex : forall (v : value) (r : redex), value_to_term v <> redex_to_term r.
  Axiom trivial_val_red : forall t : term, only_trivial t ->
    (exists v, t = value_to_term v) \/ (exists r, t = redex_to_term r).

  (** Datatype of decompositions -- either a value or a redex in a context (analogous to the decompose lemma) *)
  Inductive decomp : Set :=
  | d_val : value -> decomp
  | d_red : redex -> context -> decomp.

  Inductive interm_dec : Set :=
  | in_red : redex -> interm_dec
  | in_val : value -> interm_dec
  | in_term: term -> frame -> interm_dec.

  Definition decomp_to_term (d : decomp) : term :=
  match d with
    | d_val v => value_to_term v
    | d_red r c0 => plug (redex_to_term r) c0
  end.

  Close Scope red_scope.

End RED_LANG.

Module Type LANG_PROP (R : RED_LANG).

  Import R.
  Open Scope red_scope.

  Axiom plug_empty : forall t, [] [ t ] = t.
  Axiom compose_empty : forall E, E = E · [].
  Axiom plug_compose : forall E E0 t, E · E0 [ t ] = E0 [ E [ t ] ].

  Close Scope red_scope.

End LANG_PROP.

Module Type RED_REF_LANG.

  Declare Module R : RED_LANG.
  Import R.
  Open Scope red_scope.

  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 f (DECT : t = f a[ t0 ]), subterm_one_step t0 t.
  Axiom wf_st1 : well_founded subterm_one_step.

  Definition subterm_order := clos_trans_n1 term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40) : red_scope.
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_r _ _ wf_st1.

  Parameter frame_order : frame -> frame -> Prop.
  Notation " a <: b " := (frame_order a b) (at level 40) : red_scope.
  Axiom wf_eco : well_founded frame_order.

  Axiom dec_term_red_empty  : forall t r, dec_term t = in_red r -> only_empty t.
  Axiom dec_term_val_empty  : forall t v, dec_term t = in_val v -> only_empty t.
  Axiom dec_term_term_top   : forall t t' ec, dec_term t = in_term t' ec ->
    forall ec', ~ec <: ec'.
  Axiom dec_context_red_bot : forall ec v r, dec_context ec v = in_red r ->
    forall ec', ~ ec' <: ec.
  Axiom dec_context_val_bot : forall ec v v', dec_context ec v = in_val v' -> 
    forall ec', ~ ec' <: ec.
  Axiom dec_context_term_next : forall ec v t ec', dec_context ec v = in_term t ec' ->
    ec' <: ec /\ forall ec'', ec'' <: ec -> ~ ec' <: ec''.

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t' f => f a[ t' ] = t
    end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v'    => value_to_term v' = f a[ value_to_term v ]
    | in_term t f' => f' a[ t ]        = f a[ value_to_term v ]
    end.

  Axiom ec_order_antisym : forall f f0, f <: f0 -> ~ f0 <: f.
  Axiom dec_ec_ord : forall t0 t1 f0 f1, f0 a[ t0 ] = f1 a[ t1 ] ->
    f0 <: f1 \/ f1 <: f0 \/ (t0 = t1 /\ f0 = f1).
  Axiom elem_context_det : forall t0 t1 f0 f1, f0 <: f1 -> f0 a[ t0 ] = f1 a[ t1 ] ->
    exists v, t1 = value_to_term v.

End RED_REF_LANG.

  Ltac prove_st_wf := intro a; constructor; induction a; (intros y H; 
    inversion H as [t t0 ec DECT]; subst; destruct ec; inversion DECT; subst; constructor; auto).
  Ltac prove_ec_wf := intro a; destruct a; repeat (constructor; intros ec T; destruct ec; inversion T; subst; clear T).

Module Type ABSTRACT_MACHINE.

  Parameters term value configuration : Set.
  Parameter c_init : term -> configuration.
  Parameter c_final : value -> configuration.
  Parameter transition : configuration -> configuration -> Prop.

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
  | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

End ABSTRACT_MACHINE.

Module Type SOS_SEM.

  Parameters term value : Set.
  Parameter step : term -> term -> Prop.
  Parameter value_to_term : value -> term.

  Inductive step_close : term -> value -> Prop :=
  | s_val  : forall v, step_close (value_to_term v) v
  | s_step : forall t t0 v, step t t0 -> step_close t0 v -> step_close t v.

End SOS_SEM.

