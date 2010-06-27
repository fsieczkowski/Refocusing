Require Export refocusing_lang_cs.

Module Type RED_SEM_CS (R : RED_LANG_CS).

  Parameter dec : R.term -> R.context -> R.decomp -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self : forall (r : R.redex) (c : R.context), dec (R.redex_to_term r) c (R.d_red r c).

  Axiom decompose : forall t : R.term, (exists v:R.value, t = R.value_to_term v) \/
      (exists r:R.redex, exists c:R.context, R.plug (R.redex_to_term r) c = t).

  (** dec is left inverse of plug *)
  Axiom dec_correct : forall t c d, dec t c d -> R.decomp_to_term d = R.plug t c.

  Axiom dec_plug : forall c c0 t d, dec (R.plug t c) c0 d -> dec t (R.compose c c0) d.
  Axiom dec_plug_rev : forall c c0 t d, dec t (R.compose c c0) d -> dec (R.plug t c) c0 d.

  Inductive decempty : R.term -> R.decomp -> Prop :=
  | d_intro : forall (t : R.term) (d : R.decomp) (DEC : dec t R.empty d), decempty t d.

  Inductive iter : R.decomp -> R.value -> Prop :=
  | i_val : forall (v : R.value), iter (R.d_val v) v
  | i_red : forall (r : R.redex) (t : R.term) (c c0 : R.context) (d : R.decomp) (v : R.value)
              (CONTR : R.contract r c = Some (t, c0))
              (D_EM  : decempty (R.plug t c0) d)
              (R_IT  : iter d v),
              iter (R.d_red r c) v.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (d : R.decomp) (v : R.value)
                (D_EM : decempty t d)
                (ITER : iter d v),
                eval t v.

End RED_SEM_CS.

Module Type RED_REF_SEM_CS (R : RED_LANG_CS).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall c v, match dec_context c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) c
    | R.in_val v0 => R.value_to_term v0 = R.atom_plug (R.value_to_term v) c
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) c
  end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : R.term -> R.context -> R.decomp -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex)
               (DT  : dec_term t = R.in_red r),
               dec t c (R.d_red r c)
  | d_v    : forall (t : R.term) (c : R.context) (v : R.value) (d : R.decomp)
               (DT  : dec_term t = R.in_val v)
               (R_C : decctx v c d),
               dec t c d
  | d_term : forall (t t0 : R.term) (c : R.context) (ec : R.elem_context) (d : R.decomp)
               (DT  : dec_term t = R.in_term t0 ec)
               (R_T : dec t0 (ec :: c) d),
               dec t c d
  with decctx : R.value -> R.context -> R.decomp -> Prop :=
  | dc_end  : forall (v : R.value), decctx v R.empty (R.d_val v)
  | dc_dec  : forall (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
                (DC  : dec_context ec v = R.in_red r),
                decctx v (ec :: c) (R.d_red r c)
  | dc_val  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (d : R.decomp)
                (DC  : dec_context ec v = R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (ec :: c) d
  | dc_term : forall (v : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term) (d : R.decomp)
                (DC  : dec_context ec v = R.in_term t ec0)
                (R_T : dec t (ec0 :: c) d),
                decctx v (ec :: c) d.

  Axiom dec_val_self : forall v c d, dec (R.value_to_term v) c d <-> decctx v c d.
  Declare Module RS : RED_SEM_CS R with Definition dec := dec.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

End RED_REF_SEM_CS.

Module Type PE_REF_SEM (R : RED_LANG_CS).

  Declare Module Red_Sem : RED_REF_SEM_CS R.

  Axiom dec_context_not_val : forall v v0 ec, ~(Red_Sem.dec_context ec v = R.in_val v0).
  Axiom dec_term_value : forall v, Red_Sem.dec_term (R.value_to_term v) = R.in_val v.

End PE_REF_SEM.

Module Type RED_PROP (R : RED_LANG_CS) (RS : RED_REF_SEM_CS(R)).

  Axiom dec_is_function : forall t d d0, RS.RS.decempty t d -> RS.RS.decempty t d0 -> d = d0.
  Axiom iter_is_function : forall d v v0, RS.RS.iter d v -> RS.RS.iter d v0 -> v = v0.
  Axiom eval_is_function : forall t v v0, RS.RS.eval t v -> RS.RS.eval t v0 -> v = v0.
  Axiom dec_correct : forall t c d, RS.RS.dec t c d -> R.decomp_to_term d = R.plug t c.
  Axiom dec_total : forall t, exists d, RS.RS.decempty t d.
  Axiom unique_decomposition : forall t:R.term, (exists v:R.value, t = R.value_to_term v) \/ 
      (exists r:R.redex, exists c:R.context, R.plug (R.redex_to_term r) c = t /\ 
	  forall (r0:R.redex) c0, (R.plug (R.redex_to_term r0) c0 = t -> r=r0 /\ c= c0)).

End RED_PROP.

Module Type PRE_ABSTRACT_MACHINE_CS (R : RED_LANG_CS).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall c v, match dec_context c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) c
    | R.in_val v0 =>  R.value_to_term v0 = R.atom_plug (R.value_to_term v) c
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) c
  end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : R.term -> R.context -> R.decomp -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex)
                 (DT  : dec_term t = R.in_red r),
                 dec t c (R.d_red r c)
  | d_v    : forall (t : R.term) (c : R.context) (v : R.value) (d : R.decomp)
                 (DT  : dec_term t = R.in_val v)
                 (R_C : decctx v c d),
                 dec t c d
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (d : R.decomp)
                 (DT  : dec_term t = R.in_term t0 ec)
                 (R_T : dec t0 (ec :: c) d),
                 dec t c d
  with decctx : R.value -> R.context -> R.decomp -> Prop :=
  | dc_end  : forall (v : R.value), decctx v R.empty (R.d_val v)
  | dc_dec  : forall (v : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
                (DC  : dec_context ec v = R.in_red r),
                decctx v (ec :: c) (R.d_red r c)
  | dc_val  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (d : R.decomp)
                (DC  : dec_context ec v = R.in_val v0)
                (R_C : decctx v0 c d),
                decctx v (ec :: c) d
  | dc_term : forall (v : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term) (d : R.decomp)
                (DC  : dec_context ec v = R.in_term t ec0)
                (R_T : dec t (ec0 :: c) d),
                decctx v (ec :: c) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : R.decomp -> R.value -> Prop :=
  | i_val : forall (v : R.value), iter (R.d_val v) v
  | i_red : forall (r : R.redex) (t : R.term) (c c0 : R.context) (d : R.decomp) (v : R.value)
              (CONTR  : R.contract r c = Some (t, c0))
              (DEC    : dec t c0 d)
              (R_ITER : iter d v),
              iter (R.d_red r c) v.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (d : R.decomp) (v : R.value)
                (DEC  : dec t R.empty d)
                (ITER : iter d v),
                eval t v.

End PRE_ABSTRACT_MACHINE_CS.

Module Type STAGED_ABSTRACT_MACHINE_CS (R : RED_LANG_CS).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall c v, match dec_context c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) c
    | R.in_val v0 =>  R.value_to_term v0 = R.atom_plug (R.value_to_term v) c
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) c
  end.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | d_dec  : forall (t : R.term) (c : R.context) (r : R.redex) (v : R.value)
               (DT   : dec_term t = R.in_red r)
               (R_IT : iter (R.d_red r c) v),
               dec t c v
  | d_v    : forall (t : R.term) (c : R.context) (v v0 : R.value)
               (DT   : dec_term t = R.in_val v)
               (R_C  : decctx v c v0),
               dec t c v0
  | d_many : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
               (DT   : dec_term t = R.in_term t0 ec)
               (R_T  : dec t0 (ec :: c) v),
               dec t c v
  with decctx : R.value -> R.context -> R.value -> Prop :=
  | dc_end  : forall (v v0 : R.value)
               (IT_V : iter (R.d_val v) v0),
               decctx v R.empty v0
  | dc_dec  : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context) (r : R.redex)
               (DC   : dec_context ec v = R.in_red r)
               (R_IT : iter (R.d_red r c) v0),
               decctx v (ec :: c) v0
  | dc_val  : forall (v v0 v1 : R.value) (ec : R.elem_context) (c : R.context)
               (DC   : dec_context ec v = R.in_val v0)
               (R_C  : decctx v0 c v1),
               decctx v (ec :: c) v1
  | dc_term : forall (v v0 : R.value) (t : R.term) (ec ec0 : R.elem_context) (c : R.context)
               (DC   : dec_context ec v = R.in_term t ec0)
               (R_T  : dec t (ec0 :: c) v0),
               decctx v (ec :: c) v0
  with iter : R.decomp -> R.value -> Prop :=
  | i_val : forall (v : R.value), iter (R.d_val v) v
  | i_red : forall (r : R.redex) (c c0 : R.context) (t : R.term) (v : R.value)
               (CONTR: R.contract r c = Some (t, c0))
               (R_T  : dec t c0 v),
               iter (R.d_red r c) v.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

End STAGED_ABSTRACT_MACHINE_CS.

Module Type EVAL_APPLY_MACHINE_CS (R : RED_LANG_CS).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall c v, match dec_context c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) c
    | R.in_val v0 =>  R.value_to_term v0 = R.atom_plug (R.value_to_term v) c
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) c
  end.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | d_d_r  : forall (t t0 : R.term) (c c0 : R.context) (r : R.redex) (v : R.value)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r c = Some (t0, c0))
               (R_T   : dec t0 c0 v),
               dec t c v
  | d_v    : forall (t : R.term) (c : R.context) (v v0 : R.value)
               (DT    : dec_term t = R.in_val v)
               (R_C   : decctx v c v0),
               dec t c v0
  | d_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
               (DT    : dec_term t = R.in_term t0 ec) 
               (R_T   : dec t0 (ec :: c) v),
               dec t c v
  with decctx : R.value -> R.context -> R.value -> Prop :=
  | dc_end : forall (v : R.value), decctx v R.empty v
  | dc_red : forall (v v0 : R.value) (ec : R.elem_context) (c c0 : R.context) (r : R.redex) (t : R.term)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r c = Some (t, c0))
               (R_T   : dec t c0 v0),
               decctx v (ec :: c) v0
  | dc_rec : forall (v v0 v1 : R.value) (ec : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_val v0)
               (R_C   : decctx v0 c v1),
               decctx v (ec :: c) v1
  | dc_trm : forall (v v0 : R.value) (ec ec0 : R.elem_context) (c : R.context) (t : R.term)
               (DC    : dec_context ec v = R.in_term t ec0)
               (R_T   : dec t (ec0 :: c) v0),
               decctx v (ec :: c) v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

End EVAL_APPLY_MACHINE_CS.

Module Type PROPER_EA_MACHINE_CS (R : RED_LANG_CS).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall c v, match dec_context c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) c
    | R.in_val v0 =>  R.value_to_term v0 = R.atom_plug (R.value_to_term v) c
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) c
  end.

  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_apply : R.context -> R.value -> configuration
  | c_final : R.value -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).
  
  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term), transition (c_init t) (c_eval t R.empty)
  | t_red  : forall (t t0 : R.term) (c c0 : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r c = Some (t0, c0)),
               (c_eval t c) → (c_eval t0 c0)
  | t_val  : forall (t : R.term) (v : R.value) (c : R.context)
      	       (DT    : dec_term t = R.in_val v),
               (c_eval t c) → (c_apply c v)
  | t_term : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_term t0 ec),
               (c_eval t c) → (c_eval t0 (ec :: c))
  | t_cfin : forall (v : R.value),
               (c_apply R.empty v) → (c_final v)
  | t_cred : forall (v : R.value) (t : R.term) (ec : R.elem_context) (c c0 : R.context) (r : R.redex)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r c = Some (t, c0)),
               (c_apply (ec :: c) v) → (c_eval t c0)
  | t_cval : forall (v v0 : R.value) (ec : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_val v0),
               (c_apply (ec :: c) v) → (c_apply c v0)
  | t_cterm: forall (v : R.value) (t : R.term) (ec ec0 : R.elem_context) (c : R.context)
               (DC    : dec_context ec v = R.in_term t ec0),
               (c_apply (ec :: c) v) → (c_eval t (ec0 :: c))
  where " a → b " := (transition a b).

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_EA_MACHINE_CS.

Module Type PUSH_ENTER_MACHINE_CS (R : RED_LANG_CS).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.
  Axiom dec_context_not_val : forall v v0 ec, ~(dec_context ec v = R.in_val v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall c v, match dec_context c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) c
    | R.in_val v0 =>  R.value_to_term v0 = R.atom_plug (R.value_to_term v) c
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) c
  end.

  Inductive dec : R.term -> R.context -> R.value -> Prop :=
  | dec_r    : forall (t t0 : R.term) (c c0 : R.context) (r : R.redex) (v : R.value)
                 (DT    : dec_term t = R.in_red r)
                 (CONTR : R.contract r c = Some (t0, c0))
                 (R_T   : dec t0 c0 v),
                 dec t c v
  | dec_val  : forall (t : R.term) (v : R.value)
                 (DT    : dec_term t = R.in_val v),
                 dec t R.empty v
  | dec_v_t  : forall (t t0 : R.term) (ec ec0 : R.elem_context) (c : R.context) (v v0 : R.value)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_term t0 ec0)
                 (R_T   : dec t0 (ec0 :: c) v0),
                 dec t (ec :: c) v0
  | dec_red  : forall (t t0 : R.term) (ec : R.elem_context) (c c0 : R.context) (v v0 : R.value) (r : R.redex)
                 (DT    : dec_term t = R.in_val v)
                 (DC    : dec_context ec v = R.in_red r)
                 (CONTR : R.contract r c = Some (t0, c0))
                 (R_T   : dec t0 c0 v0),
                 dec t (ec :: c) v0
  | dec_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context) (v : R.value)
                 (DT    : dec_term t = R.in_term t0 ec)
                 (R_T   : dec t0 (ec :: c) v),
                 dec t c v.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : R.term -> R.value -> Prop :=
  | e_intro : forall (t : R.term) (v : R.value), dec t R.empty v -> eval t v.

End PUSH_ENTER_MACHINE_CS.


Module Type PROPER_PE_MACHINE_CS (R : RED_LANG_CS).

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : R.term -> R.interm_dec.
  Parameter dec_context : R.elem_context -> R.value -> R.interm_dec.
  Axiom dec_term_value : forall (v : R.value), dec_term (R.value_to_term v) = R.in_val v.
  Axiom dec_context_not_val : forall v v0 ec, ~(dec_context ec v = R.in_val v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | R.in_red r => R.redex_to_term r = t
    | R.in_val v => R.value_to_term v = t
    | R.in_term t0 c0 => R.atom_plug t0 c0 = t
  end.
  Axiom dec_context_correct : forall c v, match dec_context c v with
    | R.in_red r => R.redex_to_term r = R.atom_plug (R.value_to_term v) c
    | R.in_val v0 =>  R.value_to_term v0 = R.atom_plug (R.value_to_term v) c
    | R.in_term t c0 => R.atom_plug t c0 = R.atom_plug (R.value_to_term v) c
  end.

  Inductive configuration : Set :=
  | c_init  : R.term -> configuration 
  | c_eval  : R.term -> R.context -> configuration
  | c_final : R.value -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall (t : R.term),
               c_init t → c_eval t R.empty
  | t_red  : forall (t t0 : R.term) (c c0 : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_red r)
               (CONTR : R.contract r c = Some (t0, c0)),
               c_eval t c → c_eval t0 c0
  | t_cval : forall (t : R.term) (v : R.value)
               (DT    : dec_term t = R.in_val v),
               c_eval t R.empty → c_final v
  | t_cred : forall (t t0 : R.term) (v : R.value) (ec : R.elem_context) (c c0 : R.context) (r : R.redex)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_red r)
               (CONTR : R.contract r c = Some (t0, c0)),
               c_eval t (ec :: c) → c_eval t0 c0
  | t_crec : forall (t t0 : R.term) (v : R.value) (ec ec0 : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_val v)
               (DC    : dec_context ec v = R.in_term t0 ec0),
               c_eval t (ec :: c) → c_eval t0 (ec0 :: c)
  | t_rec  : forall (t t0 : R.term) (ec : R.elem_context) (c : R.context)
               (DT    : dec_term t = R.in_term t0 ec),
               c_eval t c → c_eval t0 (ec :: c)
  where " a →  b " := (transition a b).

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.value
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_PE_MACHINE_CS.
