Require Export List.
Require Export Util.

Implicit Arguments map_injective.

Module Type RED_LANG.

  Parameters term closure closureC value valueC redex frame frameC : Set.
  Definition context := list frame.
  Definition empty : context := nil.
  Definition contextC := list frameC.
  Definition emptyC : contextC := nil.

  Definition env  := list closure.
  Definition envC := list closureC.

  Parameter atom_plug : closure -> frame -> closure.
  Definition plug (c : closure) (E : context) : closure := fold_left atom_plug E c.
  Definition compose (E E0 : context) : context := E ++ E0.
  Definition composeC (E E0 : contextC) : contextC := E ++ E0.

  Parameter pair : term -> env -> closure.
  Parameter pairC : term -> envC -> closureC.

  Parameter value_to_closure : value -> closure.
  Parameter redex_to_closure : redex -> closure.

  Parameter valueC_to_closureC : valueC -> closureC.

  Parameter valueC_to_value : valueC -> value.
  Parameter closureC_to_closure : closureC -> closure.
  Parameter frameC_to_frame : frameC -> frame.

  Axiom value_to_closure_injective : forall v v0, value_to_closure v = value_to_closure v0 -> v = v0.
  Axiom redex_to_closure_injective : forall r r0, redex_to_closure r = redex_to_closure r0 -> r = r0.

  Axiom valueC_to_closureC_injective : forall v v0, valueC_to_closureC v = valueC_to_closureC v0 -> v = v0.

  Axiom closureC_to_closure_injective : forall c c0, closureC_to_closure c = closureC_to_closure c0 -> c = c0.
  Axiom valueC_to_value_injective : forall v v0, valueC_to_value v = valueC_to_value v0 -> v = v0.
  Axiom frameC_to_frame_injective : forall f f0, frameC_to_frame f = frameC_to_frame f0 -> f = f0.

  Axiom pairC_pair : forall t sC, closureC_to_closure (pairC t sC) = pair t (map closureC_to_closure sC).
  Axiom pairC_injective : forall t t0 sC sC0, pairC t sC = pairC t0 sC0 -> t = t0 /\ sC = sC0.
  Axiom valueC_to_closure_commutes : forall vC, value_to_closure (valueC_to_value vC) = closureC_to_closure (valueC_to_closureC vC).
  Definition envC_to_env : envC -> env := map closureC_to_closure.
  Definition envC_to_env_injective : forall sC sC0, envC_to_env sC = envC_to_env sC0 -> sC = sC0 :=
    map_injective closureC_to_closure closureC_to_closure_injective.
  Definition contextC_to_context : contextC -> context := map frameC_to_frame.
  Definition contextC_to_context_injective : forall E E0, contextC_to_context E = contextC_to_context E0 -> E = E0 :=
    map_injective frameC_to_frame frameC_to_frame_injective.

  Parameter contract : redex -> option closure.

  Definition only_empty (c : closure) : Prop := forall c0 E, plug c0 E = c -> E = empty.
  Definition only_trivial (c : closure) : Prop := forall c0 E, plug c0 E = c -> E = empty \/ exists v, c0 = value_to_closure v.

  Axiom closureC_only_empty : forall cC, only_empty (closureC_to_closure cC).
  Axiom value_trivial : forall v : value, only_trivial (value_to_closure v).
  Axiom redex_trivial : forall r : redex, only_trivial (redex_to_closure r).
  Axiom value_redex : forall (v : value) (r : redex), value_to_closure v <> redex_to_closure r.
  Axiom trivial_val_red : forall c : closure, only_trivial c ->
    (exists v : value, c = value_to_closure v) \/ (exists r : redex, c = redex_to_closure r).

  Parameter closureC_dec : forall cC : closureC,
    {p : term * envC + valueC | match p with
	| inl (t, sC) => cC = pairC t sC
	| inr vC => cC = valueC_to_closureC vC
    end}.
  Axiom dec_pairC : forall t sC, proj1_sig (closureC_dec (pairC t sC)) = inl _ (t, sC).

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

End RED_LANG.

Module Type LANG_PROP (R : RED_LANG).

  Import R.
  Notation " E · E0 " := (compose E E0) (at level 40) : red_scope.
  Notation " E × E0 " := (composeC E E0) (at level 40) : red_scope.
  Notation " E [ c ] " := (plug c E) (at level 50) : red_scope.
  Open Scope red_scope.

  Axiom plug_empty : forall c, empty [c] = c.
  Axiom compose_empty : forall c : context, c =  c · empty.
  Axiom composeC_emptyC : forall Ec : contextC, Ec = Ec × emptyC.
  Axiom plug_compose : forall (E E0 : context) (c : closure), E · E0 [ c ] = E0 [ E [ c ] ].
  Axiom composeC_compose : forall Ec Ec0, contextC_to_context (Ec × Ec0) = contextC_to_context Ec · contextC_to_context Ec0.

  Close Scope red_scope.

End LANG_PROP.

Module Type RED_REF_LANG.

  Declare Module Lang : RED_LANG.
  Import Lang.

  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Inductive subclosure_one_step : closure -> closure -> Prop :=
  | scl : forall cl cl0 f (AP : cl = atom_plug cl0 f), subclosure_one_step cl0 cl.
  Axiom subclosure_one_step_wf : well_founded subclosure_one_step.

  Definition closure_order : closure -> closure -> Prop := clos_trans_n1 _ subclosure_one_step.
  Notation " cl <| cl0 " := (closure_order cl cl0) (at level 40) : red_scope.
  Definition closure_order_wf : well_founded closure_order := wf_clos_trans_r _ _ subclosure_one_step_wf.

  Parameter frame_order : frame -> frame -> Prop.
  Notation " f <: f0 " := (frame_order f f0) (at level 40) : red_scope.
  Axiom frame_order_wf : well_founded frame_order.

  Open Scope red_scope.

  Axiom dec_closure_red_empty  : forall c r, dec_closure c = in_red r -> only_empty c.
  Axiom dec_closure_val_empty  : forall c v, dec_closure c = in_val v -> only_empty c.
  Axiom dec_closure_clo_top    : forall c c0 f, dec_closure c = in_clo c0 f -> forall f0, ~f <: f0.
  Axiom dec_context_red_bot    : forall f v r, dec_context f v = in_red r -> forall f0, ~ f0 <: f.
  Axiom dec_context_val_bot    : forall f v v0, dec_context f v = in_val v0 -> forall f0, ~ f0 <: f.
  Axiom dec_context_clo_next   : forall f f0 v c, dec_context f v = in_clo c f0 -> f0 <: f /\ forall f1, f1 <: f -> ~ f0 <: f1.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f =>  atom_plug c0 f = c
    end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c f0 => atom_plug c f0 = atom_plug (value_to_closure v) f
    end.

  Axiom frame_order_antisym : forall f f0, f <: f0 -> ~ f0 <: f.
  Axiom dec_frame_ord : forall c c0 f f0, atom_plug c f = atom_plug c0 f0 -> f <: f0 \/ f0 <: f \/ (c = c0 /\ f = f0).
  Axiom frame_det : forall c c0 f f0, f <: f0 -> atom_plug c f = atom_plug c0 f0 -> exists v, c0 = value_to_closure v.

  Definition dcl c cC ofC : Prop :=
  match ofC with
  | None => c = closureC_to_closure cC
  | Some fC => dec_closure c = in_clo (closureC_to_closure cC) (frameC_to_frame fC)
  end.

  Parameter closure_red : forall cC r cl (DCL : dec_closure (closureC_to_closure cC) = in_red r) (CTR : contract r = Some cl),
    {p : closureC * option frameC | match p with (cC, ofC) => dcl cl cC ofC end }.
  Parameter context_red : forall fC vC r cl (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r) (CTR : contract r = Some cl),
    {p : closureC * option frameC | match p with (cC, ofC) => dcl cl cC ofC end}.
  Parameter closure_val : forall cC v (DCL : dec_closure (closureC_to_closure cC) = in_val v), { vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    { p : closureC * frameC | match p with 
      (cC, fC) => cl = closureC_to_closure (cC) /\ f = frameC_to_frame fC
    end}.

  Close Scope red_scope.

End RED_REF_LANG.

  Ltac prove_st_wf := intro a; constructor; induction a; (intros y H; 
    inversion H as [c c0 f DECT]; subst; destruct f; inversion DECT; subst; constructor; auto).
  Ltac prove_ec_wf := intro a; destruct a; repeat (constructor; intros f T; destruct f; inversion T; subst; clear T).

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
