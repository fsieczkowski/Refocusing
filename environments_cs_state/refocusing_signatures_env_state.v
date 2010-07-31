Require Export refocusing_lang_env_state.

Module Type RED_SEM (R : RED_LANG).

  Import R.
  Declare Module P : LANG_PROP R.
  Import P.
  Open Scope red_scope.

  Parameter dec : closure -> context -> decomp -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self :
    forall (r : redex) (c : context), dec (redex_to_closure r) c (d_red r c).

  Axiom decompose : forall c, 
    (exists v : value, c = R.value_to_closure v) \/
    (exists r : redex, exists E :context, c = E [ redex_to_closure r ]).

  (** dec is left inverse of plug *)
  Axiom dec_correct : forall c E d, dec c E d -> decomp_to_closure d = E [c].

  Axiom dec_plug : forall E E0 c d, dec (E [c]) E0 d -> dec c (E · E0) d.
  Axiom dec_plug_rev : forall E E0 c d, dec c (E · E0) d -> dec (E [c]) E0 d.

  Inductive decempty : closure -> decomp -> Prop :=
  | d_intro : forall (c : closure) (d : decomp) 
      (DEC : dec c empty d),
      decempty c d.

  Inductive iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G,
      iter (d_val v) G (v, G)
  | i_red : forall r c E E0 G G0 d a
      (CTR : contract r E G = Some (c, E0, G0))
      (DEC : decempty (E0 [c]) d)
      (ITR : iter d G0 a),
      iter (d_red r E) G a.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t d a
      (DEC : decempty (pair t nil) d)
      (ITR : iter d init a),
      eval t a.

End RED_SEM.

Module Type RED_REF_SEM (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- 
      needed to avoid explicit induction on terms and contexts in construction 
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.
  
  (** A decomposition function specified in terms of the atomic functions *)
  Inductive dec : closure -> context -> decomp -> Prop :=
  | dec_r : forall c E r
      (DCL : dec_closure c = in_red r),
      dec c E (d_red r E)
  | dec_v : forall c E v d
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v d),
      dec c E d
  | dec_c : forall c c0 E f d
      (DCL : dec_closure c = in_clo c0 f)
      (DEC : dec c0 (f :: E) d),
      dec c E d
  with decctx :  context -> value -> decomp -> Prop :=
  | dc_n : forall v,
      decctx empty v (d_val v)
  | dc_r : forall v f E r
      (DCT : dec_context f v = in_red r),
      decctx (f :: E) v (d_red r E)
  | dc_v : forall v v0 f E d
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 d),
      decctx (f :: E) v d
  | dc_c  : forall v f f0 E c d
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) d),
      decctx (f :: E) v d.

  Axiom dec_val_self : forall v E d,
    dec (value_to_closure v) E d <-> decctx E v d.

  Declare Module RS : RED_SEM R with Definition dec := dec.

  Definition eqP cE cEC : Prop :=
    match cE, cEC with
      (cl, E, G), (clC, EC, GC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
          /\ G = stateC_to_state GC
    end.

  Parameter closure_red : forall cC r EC cl E GC G
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter context_red : forall fC vC r EC cl E GC G
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter closure_val : forall cC v
    (DCL : dec_closure (closureC_to_closure cC) = in_val v),
    {vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    {p : closureC * frameC |
      match p with 
        (cC, fC) => cl = closureC_to_closure cC /\ f = frameC_to_frame fC
      end}.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Close Scope red_scope.

End RED_REF_SEM.

Module Type PE_REF_SEM (R : RED_LANG).

  Declare Module Red_Sem : RED_REF_SEM R.

  Axiom dec_context_not_val : forall v v0 ec,
    ~(Red_Sem.dec_context ec v = R.in_val v0).
  Axiom dec_closure_value : forall v,
    Red_Sem.dec_closure (R.value_to_closure v) = R.in_val v.
  Axiom closureC_dec_not_right : forall cC p,
    ~(proj1_sig (R.closureC_dec cC) = inr _ p).

End PE_REF_SEM.

Module Type RED_PROP (R : RED_LANG) (RS : RED_REF_SEM(R)).

  Import R.
  Import RS.RS.
  Declare Module P : LANG_PROP R.
  Import P.
  Open Scope red_scope.

  Axiom dec_is_function : forall c d d0,
    decempty c d -> decempty c d0 -> d = d0.
  Axiom iter_is_function : forall d G a a0,
    iter d G a -> iter d G a0 -> a = a0.
  Axiom eval_is_function : forall t a a0,
    eval t a -> eval t a0 -> a = a0.
  Axiom dec_correct : forall c E d,
    dec c E d -> decomp_to_closure d = E [c].
  Axiom dec_total : forall c, exists d, decempty c d.
  Axiom unique_decomposition : forall c : closure, 
    (exists v : value, c = value_to_closure v) \/ 
    (exists r : redex, exists E : context,
      c = E [redex_to_closure r] /\
      forall (r0 : redex) (E0 : context), 
        c = E0 [redex_to_closure r0] -> r = r0 /\ E = E0).

  Close Scope red_scope.

End RED_PROP.

Module Type PRE_ABSTRACT_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.

  (** A decomposition function specified in terms of the atomic functions *)
  Inductive dec : closure -> context -> decomp -> Prop :=
  | dec_r : forall c E r
      (DCL : dec_closure c = in_red r),
      dec c E (d_red r E)
  | dec_v : forall c E v d
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v d),
      dec c E d
  | dec_c : forall c c0 E f d
      (DCL : dec_closure c = in_clo c0 f)
      (DEC : dec c0 (f :: E) d),
      dec c E d
  with decctx :  context -> value -> decomp -> Prop :=
  | dc_n : forall v,
      decctx empty v (d_val v)
  | dc_r : forall v f E r
      (DCT : dec_context f v = in_red r),
      decctx (f :: E) v (d_red r E)
  | dc_v : forall v v0 f E d
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 d),
      decctx (f :: E) v d
  | dc_c  : forall v f f0 E c d
      (DCT : dec_context f v = R.in_clo c f0)
      (DEC : dec c (f0 :: E) d),
      decctx (f :: E) v d.    

  Inductive iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G,
      iter (d_val v) G (v, G)
  | i_red : forall r E E0 c d G G0 a
      (CTR : contract r E G = Some (c, E0, G0))
      (DEC : dec c E0 d)
      (ITR : iter d G0 a),
      iter (d_red r E) G a.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t d a
      (DEC : dec (pair t nil) empty d)
      (ITR : iter d init a),
      eval t a.

  Close Scope red_scope.

End PRE_ABSTRACT_MACHINE.

Module Type STAGED_ABSTRACT_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.

  Inductive dec : closure -> context -> state -> answer -> Prop :=
  | dec_r : forall c r E G a
      (DCL : dec_closure c = in_red r)
      (ITR : iter (d_red r E) G a),
      dec c E G a
  | dec_v : forall c E v G a
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v G a),
      dec c E G a
  | dec_c : forall c c0 f E G a
      (DCL : dec_closure c = in_clo c0 f)
      (DEC : dec c0 (f :: E) G a),
      dec c E G a
  with decctx : context -> value -> state -> answer -> Prop :=
  | dc_n : forall v G a
      (ITR  : iter (d_val v) G a),
      decctx empty v G a
  | dc_r : forall v f E G a r
      (DCT : dec_context f v = in_red r)
      (ITR : iter (d_red r E) G a),
      decctx (f :: E) v G a
  | dc_v : forall v v0 f E G a
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 G a),
      decctx (f :: E) v G a
  | dc_c : forall v c f f0 E G a
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) G a),
      decctx (f :: E) v G a
  with iter : decomp -> state -> answer -> Prop :=
  | i_val : forall v G,
      iter (d_val v) G (v, G)
  | i_red : forall r E E0 c G G0 a
      (CTR : contract r E G = Some (c, E0, G0))
      (DEC : dec c E0 G0 a),
      iter (d_red r E) G a.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind   := Induction for iter Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a
      (DEC : dec (pair t nil) empty init a),
      eval t a.

  Close Scope red_scope.

End STAGED_ABSTRACT_MACHINE.

Module Type EVAL_APPLY_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.
    
  Inductive dec : closure -> context -> state -> answer -> Prop :=
  | dec_r : forall c c0 E E0 r G G0 a
      (DCL : dec_closure c = in_red r)
      (CTR : contract r E G = Some (c0, E0, G0))
      (DEC : dec c0 E0 G0 a),
      dec c E G a
  | dec_v : forall c E v G a
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v G a),
      dec c E G a
  | dec_c : forall c c0 f E G a
      (DCL : dec_closure c = in_clo c0 f) 
      (DEC : dec c0 (f :: E) G a),
      dec c E G a
  with decctx : context -> value -> state -> answer -> Prop :=
  | dc_n : forall v G,
      decctx empty v G (v, G)
  | dc_r : forall v f E E0 G G0 r c a
      (DCT : dec_context f v = in_red r)
      (CTR : contract r E G = Some (c, E0, G0))
      (DEC : dec c E0 G0 a),
      decctx (f :: E) v G a
  | dc_v : forall v v0 f E G a
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 G a),
      decctx (f :: E) v G a
  | dc_c : forall v f f0 E c G a
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) G a),
      decctx (f :: E) v G a.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answer -> Prop :=
  | e_intro : forall t a
      (DEC : dec (pair t nil) empty init a),
      eval t a.

  Close Scope red_scope.

End EVAL_APPLY_MACHINE.

Module Type EVAL_APPLY_MACHINE_C (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.

  Definition eqP cE cEC : Prop :=
    match cE, cEC with
      (cl, E, G), (clC, EC, GC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
          /\ G = stateC_to_state GC
    end.

  Parameter closure_red : forall cC r EC cl E GC G
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter context_red : forall fC vC r EC cl E GC G
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter closure_val : forall cC v
    (DCL : dec_closure (closureC_to_closure cC) = in_val v),
    {vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    {p : closureC * frameC |
      match p with 
        (cC, fC) => cl = closureC_to_closure cC /\ f = frameC_to_frame fC
      end}.

  Inductive dec : closureC -> contextC -> stateC -> answerC -> Prop :=
  | dec_r : forall c c0 E E0 EE G G0 GG cc r a
      (DCL : dec_closure (closureC_to_closure c) = in_red r)
      (CTR : contract r (contextC_to_context E) (stateC_to_state G)
        = Some (cc, EE, GG))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (c0, E0, G0))
      (DEC : dec c0 E0 G0 a),
      dec c E G a
  | dec_v : forall c E vv v G a
      (DCL : dec_closure (closureC_to_closure c) = in_val vv)
      (TOC : proj1_sig (closure_val _ _ DCL) = v)
      (DEC : decctx E v G a),
      dec c E G a
  with decctx : contextC -> valueC -> stateC -> answerC -> Prop :=
  | dc_n : forall v G,
      decctx emptyC v G (v, G)
  | dc_r : forall v f E E0 G G0 c0 c EE GG r a
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context E) (stateC_to_state G)
        = Some (c, EE, GG))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (c0, E0, G0))
      (DEC : dec c0 E0 G0 a),
      decctx (f :: E) v G a
  | dc_v : forall v v0 vv f E G a
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_val vv)
      (TOC : proj1_sig (context_val _ _ _ DCT) = v0)
      (DEC : decctx E v0 G a),
      decctx (f :: E) v G a
  | dc_c : forall v f f0 ff E G c cC a
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_clo c ff)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, f0))
      (DEC : dec cC (f0 :: E) G a),
      decctx (f :: E) v G a.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answerC -> Prop :=
  | e_intro : forall t a
      (DEC : dec (pairC t nil) emptyC initC a),
      eval t a.

  Close Scope red_scope.

End EVAL_APPLY_MACHINE_C.

Module Type UNFOLDED_EVAL_APPLY_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.

  Definition eqP cE cEC : Prop :=
    match cE, cEC with
      (cl, E, G), (clC, EC, GC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
          /\ G = stateC_to_state GC
    end.

  Parameter closure_red : forall cC r EC cl E GC G
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter context_red : forall fC vC r EC cl E GC G
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter closure_val : forall cC v
    (DCL : dec_closure (closureC_to_closure cC) = in_val v),
    {vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    {p : closureC * frameC |
      match p with 
        (cC, fC) => cl = closureC_to_closure cC /\ f = frameC_to_frame fC
      end}.

  Inductive dec : term -> envC -> contextC -> stateC -> answerC -> Prop :=
  | dec_r_t : forall t t0 sC sC0 EC EC0 GC GC0 a EE GG r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, EE, GG))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t0, sC0))
      (DEC : dec t0 sC0 EC0 GC0 a),
      dec t sC EC GC a
  | dec_r_v : forall t sC EC EC0 GC GC0 v a EE GG r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, EE, GG))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v)
      (DEC : decctx EC0 v GC0 a),
      dec t sC EC GC a
  | dec_v   : forall t sC EC GC v vC a
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (TOC : proj1_sig (closure_val _ _ DCL) = vC)
      (DEC : decctx EC vC GC a),
      dec t sC EC GC a
  with decctx : contextC -> valueC -> stateC -> answerC -> Prop :=
  | dc_val : forall vC GC,
      decctx emptyC vC GC (vC, GC)
  | dc_r_t : forall fC EC EC0 GC GC0 vC aC t sC E G r c cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC))
      (DEC : dec t sC  EC0 GC0 aC),
      decctx (fC :: EC) vC GC aC
  | dc_r_v : forall fC EC EC0 vC vC0 GC GC0 aC cC E G c r
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC0)
      (DEC : decctx EC0 vC0 GC0 aC),
      decctx (fC :: EC) vC GC aC
  | dc_v   : forall fC EC vC GC vC0 aC v
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v)
      (TOC : proj1_sig (context_val _ _ _ DCT) = vC0)
      (DEC : decctx EC vC0 GC aC),
      decctx (fC :: EC) vC GC aC
  | dc_c_t : forall fC fC0 EC GC vC aC t sC c f cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC))
      (DEC : dec t sC (fC0 :: EC) GC aC),
      decctx (fC :: EC) vC GC aC
  | dc_c_v : forall fC fC0 EC GC vC vC0 aC c f cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC0)
      (DEC : decctx (fC0 :: EC) vC0 GC aC),
      decctx (fC :: EC) vC GC aC.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> answerC -> Prop :=
  | e_intro : forall t v
      (DEC : dec t nil emptyC initC v),
      eval t v.

End UNFOLDED_EVAL_APPLY_MACHINE.

Module Type PROPER_EA_MACHINE (R : RED_LANG).
  Import R.
  Declare Module P : LANG_PROP R.
  Import P.

  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.

  Definition eqP cE cEC : Prop :=
    match cE, cEC with
      (cl, E, G), (clC, EC, GC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
          /\ G = stateC_to_state GC
    end.

  Parameter closure_red : forall cC r EC cl E GC G
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter context_red : forall fC vC r EC cl E GC G
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter closure_val : forall cC v
    (DCL : dec_closure (closureC_to_closure cC) = in_val v),
    {vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    {p : closureC * frameC |
      match p with 
        (cC, fC) => cl = closureC_to_closure cC /\ f = frameC_to_frame fC
      end}.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> envC -> contextC -> stateC -> configuration
  | c_apply : contextC -> valueC -> stateC -> configuration
  | c_final : answerC -> configuration.
  Notation " '<<' t '>>' " := (c_init t) : eam_scope.
  Notation " '<<' t , s , E , G '>>' " := (c_eval t s E G) : eam_scope.
  Notation " '<<' E , v , G '>>' " := (c_apply E v G) : eam_scope.
  Notation " '<<' vC , GC '>>' " := (c_final (vC, GC)) : eam_scope.
  Open Scope red_scope.
  Open Scope eam_scope.

  Reserved Notation " a '|>' b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      << t >> |> << t, nil, emptyC, initC >>
  | t_redt : forall t t0 sC sC0 EC EC0 GC GC0 E G r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t0, sC0)),
      << t, sC, EC, GC >> |> << t0, sC0, EC0, GC0 >>
  | t_redv : forall t sC EC EC0 GC GC0 E G r c cC v
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v),
      << t, sC, EC, GC >> |> << EC0, v, GC0 >>
  | t_val  : forall t sC EC GC v vC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (TOC : proj1_sig (closure_val _ _ DCL) = vC),
      << t, sC, EC, GC >> |> << EC, vC, GC >>
  | t_cfin : forall v G,
      << emptyC, v, G >> |> << v, G >>
  | t_credt: forall f v r c t sC EC EC0 GC GC0 E G cC
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
      << f :: EC, v, GC >> |> << t, sC, EC0, GC0 >>
  | t_credv: forall f v v0 r c EC EC0 GC GC0 E G cC
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR) = (cC, EC0, GC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v0),
      << f :: EC, v, GC >> |> << EC0, v0, GC0 >>
  | t_cval : forall vC vC0 fC v0 EC GC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v0)
      (TOC : proj1_sig (context_val _ _ _ DCT) = vC0),
      << fC :: EC, vC, GC >> |> << EC, vC0, GC >>
  | t_cct  : forall fC fC0 vC t sC c f EC GC cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
      << fC :: EC, vC, GC >> |> << t, sC, fC0 :: EC, GC >>
  | t_ccv  : forall fC fC0 vC vC0 c f EC GC cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC0),
      << fC :: EC, vC, GC >> |> << fC0 :: EC, vC0, GC >>
  where " a '|>' b " := (transition a b) : eam_scope.

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answerC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

  Close Scope eam_scope.
  Close Scope red_scope.

End PROPER_EA_MACHINE.

Module Type PUSH_ENTER_MACHINE (R : RED_LANG).
  Import R.
  Declare Module P : LANG_PROP R.
  Import P.

  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.

  Definition eqP cE cEC : Prop :=
    match cE, cEC with
      (cl, E, G), (clC, EC, GC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
          /\ G = stateC_to_state GC
    end.

  Parameter closure_red : forall cC r EC cl E GC G
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter context_red : forall fC vC r EC cl E GC G
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter closure_val : forall cC v
    (DCL : dec_closure (closureC_to_closure cC) = in_val v),
    {vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    {p : closureC * frameC |
      match p with 
        (cC, fC) => cl = closureC_to_closure cC /\ f = frameC_to_frame fC
      end}.

  Open Scope red_scope.

  Inductive dec : term -> envC -> contextC -> stateC -> answerC -> Prop :=
  | dec_r   : forall t t0 sC sC0 EC EC0 GC GC0 E G r c a
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNF : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR)
        = (pairC t0 sC0, EC0, GC0))
      (DEC : dec t0 sC0 EC0 GC0 a),
      dec t sC EC GC a
  | dec_v_e : forall t sC v vC GC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNF : proj1_sig (closure_val _ _ DCL) = vC),
      dec t sC emptyC GC (vC, GC)
  | dec_v_r : forall t t0 sC sC0 EC EC0 GC GC0 fC vC aC v r c E G
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR)
        = (pairC t0 sC0, EC0, GC0))
      (DEC : dec t0 sC0 EC0 GC0 aC),
      dec t sC (fC :: EC) GC aC
  | dec_v_c  : forall t t0 sC sC0 vC aC fC fC0 EC GC v c f
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (UNC : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0))
      (DEC : dec t0 sC0 (fC0 :: EC) GC aC),
      dec t sC (fC :: EC) GC aC.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : term -> answerC -> Prop :=
  | e_intro : forall t a
      (DEC : dec t nil emptyC initC a),
      eval t a.

  Close Scope red_scope.

End PUSH_ENTER_MACHINE.

Module Type PROPER_PE_MACHINE (R : RED_LANG).
  Import R.
  Declare Module P : LANG_PROP R.
  Import P.


  (** Functions specifying atomic steps of induction on terms and contexts --
      needed to avoid explicit induction on terms and contexts in construction
      of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Open Scope red_scope.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => f0[ c0 ]a = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = f[ value_to_closure v ]a
    | in_val v0 => value_to_closure v0 = f[ value_to_closure v ]a
    | in_clo c0 f0 => f0[ c0 ]a        = f[ value_to_closure v ]a
  end.

  Definition eqP cE cEC : Prop :=
    match cE, cEC with
      (cl, E, G), (clC, EC, GC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
          /\ G = stateC_to_state GC
    end.

  Parameter closure_red : forall cC r EC cl E GC G
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter context_red : forall fC vC r EC cl E GC G
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) (stateC_to_state GC) 
      = Some (cl, E, G)),
    {p : closureC * contextC * stateC | eqP (cl, E, G) p}.
  Parameter closure_val : forall cC v
    (DCL : dec_closure (closureC_to_closure cC) = in_val v),
    {vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    {p : closureC * frameC |
      match p with 
        (cC, fC) => cl = closureC_to_closure cC /\ f = frameC_to_frame fC
      end}.

  Open Scope red_scope.

  Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> envC -> contextC -> stateC -> configuration
  | c_final : answerC -> configuration.

  Notation " '<<' t '>>' " := (c_init t) : pem_scope.
  Notation " '<<' t , s , E , G '>>' " := (c_eval t s E G) : pem_scope.
  Notation " '<<' vC , GC '>>' " := (c_final (vC, GC)) : pem_scope.

  Open Scope red_scope.
  Open Scope pem_scope.

  Reserved Notation " a '|>' b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      << t >> |> << t, nil, emptyC, initC >>
  | t_red  : forall t t0 sC sC0 EC EC0 GC GC0 E G r c
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNF : proj1_sig (closure_red _ _ _ _ _ _ _ DCL CTR)
        = (pairC t0 sC0, EC0, GC0)),
      << t, sC, EC, GC >> |> << t0, sC0, EC0, GC0 >>
  | t_cval : forall t sC v vC GC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNF : proj1_sig (closure_val _ _ DCL) = vC),
      << t, sC, emptyC, GC >> |> << vC, GC >>
  | t_cred : forall t t0 sC sC0 fC EC EC0 GC GC0 E G vC v r c
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) (stateC_to_state GC)
        = Some (c, E, G))
      (UNC : proj1_sig (context_red _ _ _ _ _ _ _ _ DCT CTR)
        = (pairC t0 sC0, EC0, GC0)),
      << t, sC, fC :: EC, GC >> |> << t0, sC0, EC0, GC0 >>
  | t_crec : forall t t0 sC sC0 fC fC0 EC GC vC v c f
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (UNC : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0)),
      << t, sC, fC :: EC, GC >> |> << t0, sC0, fC0 :: EC, GC >>
  where " c '|>' c0 " := (transition c c0) : pem_scope.

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := answerC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_PE_MACHINE.
