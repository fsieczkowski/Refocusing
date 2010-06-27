Require Export refocusing_lang.

Module Type RED_SEM_T (R : RED_LANG).

  Parameter dec : R.term -> R.context -> R.decomp -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self : forall (r : R.redex) (c : R.context), dec (R.redex_to_term r) c (R.d_red r c).

  Axiom decompose : forall t : R.term, (exists v:R.value, t = R.value_to_term v) \/
      (exists r:R.redex, exists c:R.context, R.plug (R.redex_to_term r) c = t).

  (** dec is left inverse of plug *)
  Axiom dec_correct : forall t c d, dec t c d -> R.decomp_to_term d = R.plug t c.

  Axiom dec_plug : forall c c0 t d, dec (R.plug t c) c0 d -> dec t (R.compose c c0) d.
  Axiom dec_plug_rev : forall c c0 t d, dec t (R.compose c c0) d -> dec (R.plug t c) c0 d.

  Definition trace := stream R.decomp.

  Inductive decempty : R.term -> R.decomp -> Prop :=
  | d_intro : forall (t : R.term) (d : R.decomp), dec t R.empty d -> decempty t d.

  CoInductive gather : R.decomp -> trace -> Prop :=
  | i_val : forall (v : R.value), gather (R.d_val v) (s_cons (R.d_val v) s_nil)
  | i_red : forall (r : R.redex) (t : R.term) (c : R.context) (d : R.decomp) (tr : trace),
              R.contract r = Some t -> decempty (R.plug t c) d -> gather d tr -> gather (R.d_red r c) (s_cons (R.d_red r c) tr).

  CoInductive eval : R.term -> trace -> Prop :=
  | e_intro : forall (t : R.term) (d : R.decomp) (tr : trace), decempty t d -> gather d tr -> eval t tr.

End RED_SEM_T.

Module Type RED_REF_SEM_T (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r  => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) ec
  end.
  
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

  Declare Module RS : RED_SEM_T R with Definition dec := dec.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

End RED_REF_SEM_T.

Module Type PE_REF_SEM_T (R : RED_LANG).

  Declare Module Red_Sem : RED_REF_SEM_T R.

  Axiom dec_context_not_val : forall v v0 ec, ~(Red_Sem.dec_context ec v = R.in_val v0).

End PE_REF_SEM_T.

Module Type RED_PROP_T (R : RED_LANG) (RS : RED_REF_SEM_T(R)).

  Axiom dec_is_function : forall t d d0, RS.RS.decempty t d -> RS.RS.decempty t d0 -> d = d0.
  Axiom gather_is_function : forall d ds ds0, RS.RS.gather d ds -> RS.RS.gather d ds0 -> bisim_stream ds ds0.
  Axiom eval_is_function : forall t tr tr0, RS.RS.eval t tr -> RS.RS.eval t tr0 -> bisim_stream tr tr0.
  Axiom dec_correct : forall t c d, RS.RS.dec t c d -> R.decomp_to_term d = R.plug t c.
  Axiom dec_total : forall t, exists d, RS.RS.decempty t d.
  Axiom unique_decomposition : forall t:R.term, (exists v:R.value, t = R.value_to_term v) \/ 
      (exists r:R.redex, exists c:R.context, R.plug (R.redex_to_term r) c = t /\ 
	  forall (r0:R.redex) c0, (R.plug (R.redex_to_term r0) c0 = t -> r=r0 /\ c= c0)).

End RED_PROP_T.

Module Type PRE_ABSTRACT_MACHINE_T (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r  => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) ec
  end.
  
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

End PRE_ABSTRACT_MACHINE_T.

Module Type STAGED_ABSTRACT_MACHINE_T (R : RED_LANG).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r  => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) ec
  end.

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

End STAGED_ABSTRACT_MACHINE_T.

Module Type EVAL_APPLY_MACHINE_T (R : RED_LANG).

  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r  => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) ec
  end.
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

End EVAL_APPLY_MACHINE_T.

Module Type ABSTRACT_MACHINE_T.

  Parameters term value configuration decomp : Set.
  Parameter c_init : term -> configuration.
  Parameter c_final : value -> configuration.
  Parameter transition : configuration -> configuration -> option decomp -> Prop.
  Definition trace := stream decomp.

  CoInductive trace_m : configuration -> trace -> Prop :=
  | empty_trace : forall v : value, trace_m (c_final v) s_nil
  | trace_trans : forall (c0 c1 : configuration) (od : option decomp) (ds : trace), transition c0 c1 od -> trace_m c1 ds -> trace_m c0 (match od with
    | None => ds
    | Some d => (s_cons d ds)
    end).

  CoInductive eval : term -> trace -> Prop :=
  | e_intro : forall (t : term) (ds : trace), trace_m (c_init t) ds -> eval t ds.

End ABSTRACT_MACHINE_T.

Module Type PROPER_EA_MACHINE_T (R : RED_LANG).

  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r  => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) ec
  end.

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

  Declare Module AM : ABSTRACT_MACHINE_T
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition decomp := R.decomp
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_EA_MACHINE_T.

Module Type PUSH_ENTER_MACHINE_T (R : RED_LANG).

  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.
  Axiom dec_context_not_val : forall v v0 ec, ~(dec_context ec v = R.in_val v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r  => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) ec
  end.
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

End PUSH_ENTER_MACHINE_T.


Module Type PROPER_PE_MACHINE_T (R : RED_LANG).

  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.
  Axiom dec_context_not_val : forall v v0 ec, ~(dec_context ec v = R.in_val v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 ec0 => R.atom_plug t0 ec0 = t
  end.
  Axiom dec_context_correct : forall ec v, match dec_context ec v with
    | R.in_red r  => R.redex_to_term r = R.atom_plug (R.value_to_term v) ec
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) ec
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) ec
  end.

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

  Declare Module AM : ABSTRACT_MACHINE_T
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition decomp := R.decomp
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_PE_MACHINE_T.
