Require Export refocusing_lang.

Module Type RED_SEM (R : RED_LANG).

  Import R.
  Declare Module P : LANG_PROP R.
  Import P.
  Open Scope red_scope.

  Parameter dec : term -> context -> decomp -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self : forall (r : redex) (c : context), dec (redex_to_term r) c (d_red r c).

  Axiom decompose : forall t : term, (exists v : value, t = value_to_term v) \/
      (exists r : redex, exists E : context, E [ redex_to_term r ] = t).

  (** dec is left inverse of plug *)
  Axiom dec_correct : forall t E d, dec t E d -> decomp_to_term d = E [ t ].

  Axiom dec_plug : forall E E0 t d, dec (E [ t ]) E0 d -> dec t (E · E0) d.
  Axiom dec_plug_rev : forall E E0 t d, dec t (E · E0) d -> dec (E [ t ]) E0 d.

  Inductive decempty : term -> decomp -> Prop :=
  | d_intro : forall (t : term) (d : decomp) (DEC : dec t [] d), decempty t d.

  Inductive iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G, iter (d_val v) G (v, G)
  | i_red : forall r G G0 t E d a
              (CONTR : contract r G = Some (t, G0))
              (D_EM  : decempty (E [ t ]) d)
              (R_IT  : iter d G0 a),
              iter (d_red r E) G a.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t d a
                (D_EM : decempty t d)
                (ITER : iter d init a),
                eval t a.

  Close Scope red_scope.

End RED_SEM.

Module Type RED_REF_SEM (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t0 f => f a[ t0 ] = t
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v0    => value_to_term v0 = f a[ value_to_term v ]
    | in_term t f0 => f0 a[ t ]        = f a[ value_to_term v ]
  end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> context -> decomp -> Prop :=
  | d_dec  : forall t E r
               (DT  : dec_term t = in_red r),
               dec t E (d_red r E)
  | d_v    : forall t E v d
               (DT  : dec_term t = in_val v)
               (R_C : decctx v E d),
               dec t E d
  | d_term : forall t t0 E f d
               (DT  : dec_term t = in_term t0 f)
               (R_T : dec t0 (f :: E) d),
               dec t E d
  with decctx : value -> context -> decomp -> Prop :=
  | dc_end  : forall v, decctx v [] (d_val v)
  | dc_dec  : forall v f E r
                (DC  : dec_context f v = in_red r),
                decctx v (f :: E) (d_red r E)
  | dc_val  : forall v v0 f E d
                (DC  : dec_context f v = in_val v0)
                (R_C : decctx v0 E d),
                decctx v (f :: E) d
  | dc_term : forall v f f0 E t d
                (DC  : dec_context f v = in_term t f0)
                (R_T : dec t (f0 :: E) d),
                decctx v (f :: E) d.

  Axiom dec_val_self : forall v E d, dec (value_to_term v) E d <-> decctx v E d.
  Declare Module RS : RED_SEM R with Definition dec := dec.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Close Scope red_scope.

End RED_REF_SEM.

Module Type PE_REF_SEM (R : RED_LANG).

  Declare Module Red_Sem : RED_REF_SEM R.
  Import R.
  Import Red_Sem.

  Axiom dec_context_not_val : forall v v0 f, ~(dec_context f v = in_val v0).
  Axiom dec_term_value : forall v, dec_term (value_to_term v) = in_val v.

End PE_REF_SEM.

Module Type RED_PROP (R : RED_LANG) (RS : RED_REF_SEM(R)).

  Import RS.RS.
  Import R.

  Open Scope red_scope.

  Axiom dec_is_function : forall t d d0, decempty t d -> decempty t d0 -> d = d0.
  Axiom iter_is_function : forall d G a a0, iter d G a -> iter d G a0 -> a = a0.
  Axiom eval_is_function : forall t a a0, eval t a -> eval t a0 -> a = a0.
  Axiom dec_correct : forall t E d, dec t E d -> decomp_to_term d = E [ t ].
  Axiom dec_total : forall t, exists d, decempty t d.
  Axiom unique_decomposition : forall t, (exists v : value, t = value_to_term v) \/ 
      (exists r : redex, exists E : context, E [ redex_to_term r ] = t /\ 
	  forall r0 E0, E0 [redex_to_term r0 ] = t -> (r = r0 /\ E = E0)).

  Close Scope red_scope.

End RED_PROP.

Module Type PRE_ABSTRACT_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t0 f => f a[ t0 ] = t
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v0    => value_to_term v0 = f a[ value_to_term v ]
    | in_term t f0 => f0 a[ t ]        = f a[ value_to_term v ]
  end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : term -> context -> decomp -> Prop :=
  | d_dec  : forall t E r
               (DT  : dec_term t = in_red r),
               dec t E (d_red r E)
  | d_v    : forall t E v d
               (DT  : dec_term t = in_val v)
               (R_C : decctx v E d),
               dec t E d
  | d_term : forall t t0 E f d
               (DT  : dec_term t = in_term t0 f)
               (R_T : dec t0 (f :: E) d),
               dec t E d
  with decctx : value -> context -> decomp -> Prop :=
  | dc_end  : forall v, decctx v [] (d_val v)
  | dc_dec  : forall v f E r
                (DC  : dec_context f v = in_red r),
                decctx v (f :: E) (d_red r E)
  | dc_val  : forall v v0 f E d
                (DC  : dec_context f v = in_val v0)
                (R_C : decctx v0 E d),
                decctx v (f :: E) d
  | dc_term : forall v f f0 E t d
                (DC  : dec_context f v = in_term t f0)
                (R_T : dec t (f0 :: E) d),
                decctx v (f :: E) d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G, iter (d_val v) G (v, G)
  | i_red : forall r G G0 t E d a
              (CONTR  : contract r G = Some (t, G0))
              (DEC    : dec t E d)
              (R_ITER : iter d G0 a),
              iter (d_red r E) G a.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t d a
                (DEC  : dec t [] d)
                (ITER : iter d init a),
                eval t a.

  Close Scope red_scope.

End PRE_ABSTRACT_MACHINE.

Module Type STAGED_ABSTRACT_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t0 f => f a[ t0 ] = t
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v0    => value_to_term v0 = f a[ value_to_term v ]
    | in_term t f0 => f0 a[ t ]        = f a[ value_to_term v ]
  end.

  Inductive dec : term -> context -> state -> answer -> Prop :=
  | d_dec  : forall t E r G a
               (DT   : dec_term t = in_red r)
               (R_IT : iter (d_red r E) G a),
               dec t E G a
  | d_v    : forall t E v G a
               (DT   : dec_term t = in_val v)
               (R_C  : decctx v E G a),
               dec t E G a
  | d_many : forall t t0 f E G a
               (DT   : dec_term t = in_term t0 f)
               (R_T  : dec t0 (f :: E) G a),
               dec t E G a
  with decctx : value -> context -> state -> answer -> Prop :=
  | dc_end  : forall v G a
               (IT_V : iter (d_val v) G a),
               decctx v [] G a
  | dc_dec  : forall v f E r G a
               (DC   : dec_context f v = in_red r)
               (R_IT : iter (d_red r E) G a),
               decctx v (f :: E) G a
  | dc_val  : forall v v0 f E G a
               (DC   : dec_context f v = in_val v0)
               (R_C  : decctx v0 E G a),
               decctx v (f :: E) G a
  | dc_term : forall v t f f0 E G a
               (DC   : dec_context f v = in_term t f0)
               (R_T  : dec t (f0 :: E) G a),
               decctx v (f :: E) G a
  with iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G, iter (d_val v) G (v, G)
  | i_red : forall r E G G0 t a
               (CONTR: contract r G = Some (t, G0))
               (R_T  : dec t E G0 a),
               iter (d_red r E) G a.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a, dec t [] init a -> eval t a.

  Close Scope red_scope.

End STAGED_ABSTRACT_MACHINE.

Module Type EVAL_APPLY_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t0 f => f a[ t0 ] = t
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v0    => value_to_term v0 = f a[ value_to_term v ]
    | in_term t f0 => f0 a[ t ]        = f a[ value_to_term v ]
  end.

  Inductive dec : term -> context -> state -> answer -> Prop :=
  | d_d_r  : forall t t0 E r G G0 a
               (DT    : dec_term t = in_red r)
               (CONTR : contract r G = Some (t0, G0))
               (R_T   : dec t0 E G0 a),
               dec t E G a
  | d_v    : forall t v E G a
               (DT    : dec_term t = in_val v)
               (R_C   : decctx v E G a),
               dec t E G a
  | d_term : forall t t0 f E G a
               (DT    : dec_term t = R.in_term t0 f) 
               (R_T   : dec t0 (f :: E) G a),
               dec t E G a
  with decctx : value -> context -> state -> answer -> Prop :=
  | dc_end : forall v G, decctx v [] G (v, G)
  | dc_red : forall v f E r G G0 t a
               (DC    : dec_context f v = in_red r)
               (CONTR : contract r G = Some (t, G0))
               (R_T   : dec t E G0 a),
               decctx v (f :: E) G a
  | dc_rec : forall v v0 f E G a
               (DC    : dec_context f v = in_val v0)
               (R_C   : decctx v0 E G a),
               decctx v (f :: E) G a
  | dc_trm : forall v f f0 E G t a
               (DC    : dec_context f v = in_term t f0)
               (R_T   : dec t (f0 :: E) G a),
               decctx v (f :: E) G a.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a, dec t [] init a -> eval t a.

  Close Scope red_scope.

End EVAL_APPLY_MACHINE.

Module Type PROPER_EA_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t0 f => f a[ t0 ] = t
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v0    => value_to_term v0 = f a[ value_to_term v ]
    | in_term t f0 => f0 a[ t ]        = f a[ value_to_term v ]
  end.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> context -> state -> configuration
  | c_apply : context -> value -> state -> configuration
  | c_final : answer -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      c_init t → c_eval t [] init
  | t_red  : forall t t0 G G0 r E
      (DT    : dec_term t = in_red r)
      (CONTR : contract r G = Some (t0, G0)),
      c_eval t E G → c_eval t0 E G0
  | t_val  : forall t v E G
      (DT    : dec_term t = in_val v),
      c_eval t E G → c_apply E v G
  | t_term : forall t t0 f E G
      (DT    : dec_term t = R.in_term t0 f),
      c_eval t E G → c_eval t0 (f :: E) G
  | t_cfin : forall v G,
      c_apply [] v G → c_final (v, G)
  | t_cred : forall v t f E G G0 r
      (DC    : dec_context f v = in_red r)
      (CONTR : contract r G = Some (t, G0)),
      c_apply (f :: E) v G → c_eval t E G0
  | t_cval : forall v v0 f E G
      (DC    : dec_context f v = in_val v0),
      c_apply (f :: E) v G → c_apply E v0 G
  | t_cterm: forall v t f f0 E G
      (DC    : dec_context f v = in_term t f0),
      c_apply (f :: E) v G → c_eval t (f0 :: E) G
  where " a → b " := (transition a b).

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answer
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

  Close Scope red_scope.

End PROPER_EA_MACHINE.

Module Type PUSH_ENTER_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_term_value : forall v, dec_term (value_to_term v) = in_val v.
  Axiom dec_context_not_val : forall v v0 f, ~(dec_context f v = in_val v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t0 f => f a[ t0 ] = t
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v0    => value_to_term v0 = f a[ value_to_term v ]
    | in_term t f0 => f0 a[ t ]        = f a[ value_to_term v ]
  end.

  Inductive dec : term -> context -> state -> answer -> Prop :=
  | dec_r    : forall t t0 E r G G0 a
                 (DT    : dec_term t = in_red r)
                 (CONTR : R.contract r G = Some (t0, G0))
                 (R_T   : dec t0 E G0 a),
                 dec t E G a
  | dec_val  : forall t G v
                 (DT    : dec_term t = in_val v),
                 dec t [] G (v, G)
  | dec_v_t  : forall t t0 f f0 E v G a
                 (DT    : dec_term t = in_val v)
                 (DC    : dec_context f v = in_term t0 f0)
                 (R_T   : dec t0 (f0 :: E) G a),
                 dec t (f :: E) G a
  | dec_red  : forall t t0 f E v r G G0 a
                 (DT    : dec_term t = in_val v)
                 (DC    : dec_context f v = in_red r)
                 (CONTR : contract r G = Some (t0, G0))
                 (R_T   : dec t0 E G0 a),
                 dec t (f :: E) G a
  | dec_rec  : forall t t0 f E G a
                 (DT    : dec_term t = in_term t0 f)
                 (R_T   : dec t0 (f :: E) G a),
                 dec t E G a.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a, dec t [] init a -> eval t a.

  Close Scope red_scope.

End PUSH_ENTER_MACHINE.

Module Type PROPER_PE_MACHINE (R : RED_LANG).

  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_term : term -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_term_value : forall v, dec_term (value_to_term v) = in_val v.
  Axiom dec_context_not_val : forall v v0 f, ~(dec_context f v = in_val v0).

  Axiom dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t0 f => f a[ t0 ] = t
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v0    => value_to_term v0 = f a[ value_to_term v ]
    | in_term t f0 => f0 a[ t ]        = f a[ value_to_term v ]
  end.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> context -> state -> configuration
  | c_final : answer -> configuration.

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      c_init t → c_eval t [] init
  | t_red  : forall t t0 E r G G0
      (DT    : dec_term t = in_red r)
      (CONTR : contract r G = Some (t0, G0)),
      c_eval t E G → c_eval t0 E G0
  | t_cval : forall t G v
      (DT    : dec_term t = in_val v),
      c_eval t [] G → c_final (v, G)
  | t_cred : forall t t0 v f E r G G0
      (DT    : dec_term t = in_val v)
      (DC    : dec_context f v = in_red r)
      (CONTR : contract r G = Some (t0, G0)),
      c_eval t (f :: E) G → c_eval t0 E G0
  | t_crec : forall t t0 v f f0 E G
      (DT    : dec_term t = in_val v)
      (DC    : dec_context f v = in_term t0 f0),
      c_eval t (f :: E) G → c_eval t0 (f0 :: E) G
  | t_rec  : forall t t0 f E G
      (DT    : dec_term t = in_term t0 f),
      c_eval t E G → c_eval t0 (f :: E) G
  where " a →  b " := (transition a b).

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answer
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

  Close Scope red_scope.

End PROPER_PE_MACHINE.
