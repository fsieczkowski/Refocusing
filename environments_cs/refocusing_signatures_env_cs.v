Require Export refocusing_lang_env_cs.

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

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall v,
      iter (d_val v) v
  | i_red : forall r c E E0 d v
      (CTR : contract r E = Some (c, E0))
      (DEC : decempty (E0 [c]) d)
      (ITR : iter d v),
      iter (d_red r E) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t d v
      (DEC : decempty (pair t nil) d)
      (ITR : iter d v),
      eval t v.

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
      (cl, E), (clC, EC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
    end.

  Parameter closure_red : forall cC r EC cl E
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Parameter context_red : forall fC vC r EC cl E
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
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
  Axiom iter_is_function : forall d v v0,
    iter d v -> iter d v0 -> v = v0.
  Axiom eval_is_function : forall t v v0,
    eval t v -> eval t v0 -> v = v0.
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

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall v,
      iter (d_val v) v
  | i_red : forall r E E0 c d v
      (CTR : contract r E = Some (c, E0))
      (DEC : dec c E0 d)
      (ITR : iter d v),
      iter (d_red r E) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t d v
      (DEC : dec (pair t nil) empty d)
      (ITR : iter d v),
      eval t v.

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

  Inductive dec : closure -> context -> value -> Prop :=
  | dec_r : forall c r E v
      (DCL : dec_closure c = in_red r)
      (ITR : iter (d_red r E) v),
      dec c E v
  | dec_v : forall c E v v0
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v v0),
      dec c E v0
  | dec_c : forall c c0 f E v
      (DCL : dec_closure c = in_clo c0 f)
      (DEC : dec c0 (f :: E) v),
      dec c E v
  with decctx : context -> value -> value -> Prop :=
  | dc_n : forall v v0
      (ITR  : iter (d_val v) v0),
      decctx empty v v0
  | dc_r : forall v v0 f E r
      (DCT : dec_context f v = in_red r)
      (ITR : iter (d_red r E) v0),
      decctx (f :: E) v v0
  | dc_v : forall v v0 v1 f E
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 v1),
      decctx (f :: E) v v1
  | dc_c : forall v v0 c f f0 E
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) v0),
      decctx (f :: E) v v0
  with iter : decomp -> value -> Prop :=
  | i_val : forall v,
      iter (d_val v) v
  | i_red : forall r E E0 c v
      (CTR : contract r E = Some (c, E0))
      (DEC : dec c E0 v),
      iter (d_red r E) v.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind   := Induction for iter Sort Prop.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v
      (DEC : dec (pair t nil) empty v),
      eval t v.

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
    
  Inductive dec : closure -> context -> value -> Prop :=
  | dec_r : forall c c0 E E0 r v
      (DCL : dec_closure c = in_red r)
      (CTR : contract r E = Some (c0, E0))
      (DEC : dec c0 E0 v),
      dec c E v
  | dec_v : forall c E v v0
      (DCL : dec_closure c = in_val v)
      (DEC : decctx E v v0),
      dec c E v0
  | dec_c : forall c c0 f E v
      (DCL : dec_closure c = in_clo c0 f) 
      (DEC : dec c0 (f :: E) v),
      dec c E v
  with decctx : context -> value -> value -> Prop :=
  | dc_n : forall v,
      decctx empty v v
  | dc_r : forall v v0 f E E0 r c
      (DCT : dec_context f v = in_red r)
      (CTR : contract r E = Some (c, E0))
      (DEC : dec c E0 v0),
      decctx (f :: E) v v0
  | dc_v : forall v v0 v1 f E
      (DCT : dec_context f v = in_val v0)
      (DEC : decctx E v0 v1),
      decctx (f :: E) v v1
  | dc_c : forall v v0 f f0 E c
      (DCT : dec_context f v = in_clo c f0)
      (DEC : dec c (f0 :: E) v0),
      decctx (f :: E) v v0.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall t v
      (DEC : dec (pair t nil) empty v),
      eval t v.

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
      (cl, E), (clC, EC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
    end.

  Parameter closure_red : forall cC r EC cl E
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Parameter context_red : forall fC vC r EC cl E
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
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

  Inductive dec : closureC -> contextC -> valueC -> Prop :=
  | dec_r : forall c c0 E E0 EE cc r v
      (DCL : dec_closure (closureC_to_closure c) = in_red r)
      (CTR : contract r (contextC_to_context E) = Some (cc, EE))
      (TOC : proj1_sig (closure_red _ _ _ _ _ DCL CTR) = (c0, E0))
      (DEC : dec c0 E0 v),
      dec c E v
  | dec_v : forall c E vv v v0
      (DCL : dec_closure (closureC_to_closure c) = in_val vv)
      (TOC : proj1_sig (closure_val _ _ DCL) = v)
      (DEC : decctx E v v0),
      dec c E v0
  with decctx : contextC -> valueC -> valueC -> Prop :=
  | dc_n : forall v,
      decctx emptyC v v
  | dc_r : forall v v0 f E E0 c0 c EE r
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context E) = Some (c, EE))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ DCT CTR) = (c0, E0))
      (DEC : dec c0 E0 v0),
      decctx (f :: E) v v0
  | dc_v : forall v v0 v1 vv f E
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_val vv)
      (TOC : proj1_sig (context_val _ _ _ DCT) = v0)
      (DEC : decctx E v0 v1),
      decctx (f :: E) v v1
  | dc_c : forall v v0 f f0 ff E c cC
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_clo c ff)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, f0))
      (DEC : dec cC (f0 :: E) v0),
      decctx (f :: E) v v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall t v
      (DEC : dec (pairC t nil) emptyC v),
      eval t v.

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
      (cl, E), (clC, EC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
    end.

  Parameter closure_red : forall cC r EC cl E
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Parameter context_red : forall fC vC r EC cl E
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
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

  Inductive dec : term -> envC -> contextC -> valueC -> Prop :=
  | dec_r_t : forall t t0 sC sC0 EC EC0 EE v r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, EE))
      (TOC : proj1_sig (closure_red _ _ _ _ _ DCL CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t0, sC0))
      (DEC : dec t0 sC0 EC0 v),
      dec t sC EC v
  | dec_r_v : forall t sC EC EC0 v v0 EE r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, EE))
      (TOC : proj1_sig (closure_red _ _ _ _ _ DCL CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v0)
      (DEC : decctx EC0 v0 v),
      dec t sC EC v
  | dec_v   : forall t sC EC v vC v0
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (TOC : proj1_sig (closure_val _ _ DCL) = vC)
      (DEC : decctx EC vC v0),
      dec t sC EC v0
  with decctx : contextC -> valueC -> valueC -> Prop :=
  | dc_val : forall vC,
      decctx emptyC vC vC
  | dc_r_t : forall fC EC EC0 vC vC0 t sC E r c cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ DCT CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC))
      (DEC : dec t sC  EC0 vC0),
      decctx (fC :: EC) vC vC0
  | dc_r_v : forall fC EC EC0 vC vC0 vC1 cC E c r
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ DCT CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC1)
      (DEC : decctx EC0 vC1 vC0),
      decctx (fC :: EC) vC vC0
  | dc_v   : forall fC EC vC vC0 vC1 v
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v)
      (TOC : proj1_sig (context_val _ _ _ DCT) = vC0)
      (DEC : decctx EC vC0 vC1),
      decctx (fC :: EC) vC vC1
  | dc_c_t : forall fC fC0 EC vC vC0 t sC c f cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC))
      (DEC : dec t sC (fC0 :: EC) vC0),
      decctx (fC :: EC) vC vC0
  | dc_c_v : forall fC fC0 EC vC vC0 vC1 c f cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC1)
      (DEC : decctx (fC0 :: EC) vC1 vC0),
      decctx (fC :: EC) vC vC0.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall t v
      (DEC : dec t nil emptyC v),
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
      (cl, E), (clC, EC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
    end.

  Parameter closure_red : forall cC r EC cl E
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Parameter context_red : forall fC vC r EC cl E
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
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
  | c_eval  : term -> envC -> contextC -> configuration
  | c_apply : contextC -> valueC -> configuration
  | c_final : valueC -> configuration.
  Notation " <<i t >> " := (c_init t) : eam_scope.
  Notation " << t , s , E >> " := (c_eval t s E) : eam_scope.
  Notation " << E , v >> " := (c_apply E v) : eam_scope.
  Notation " <<f v >> " := (c_final v) : eam_scope.
  Open Scope red_scope.
  Open Scope eam_scope.

  Reserved Notation " a '|>' b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      <<i t >> |> << t, nil, emptyC >>
  | t_redt : forall t t0 sC sC0 EC EC0 E r c cC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (TOC : proj1_sig (closure_red _ _ _ _ _ DCL CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t0, sC0)),
      << t, sC, EC>> |> << t0, sC0, EC0 >>
  | t_redv : forall t sC EC EC0 E r c cC v
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (TOC : proj1_sig (closure_red _ _ _ _ _ DCL CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v),
      << t, sC, EC>> |> << EC0, v >>
  | t_val  : forall t sC E v vC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (TOC : proj1_sig (closure_val _ _ DCL) = vC),
      << t, sC, E >> |> << E, vC >>
  | t_cfin : forall v,
      << emptyC, v >> |> <<f v >>
  | t_credt: forall f v r c t sC EC EC0 E cC
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ DCT CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
      << f :: EC, v >> |> << t, sC, EC0 >>
  | t_credv: forall f v v0 r c EC EC0 E cC
      (DCT : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (TOC : proj1_sig (context_red _ _ _ _ _ _ DCT CTR) = (cC, EC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ v0),
      << f :: EC, v >> |> << EC0, v0 >>
  | t_cval : forall vC vC0 fC v0 E
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v0)
      (TOC : proj1_sig (context_val _ _ _ DCT) = vC0),
      << fC :: E, vC >> |> << E, vC0 >>
  | t_cct  : forall fC fC0 vC t sC c f E cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
      << fC :: E, vC >> |> << t, sC, fC0 :: E >>
  | t_ccv  : forall fC fC0 vC vC0 c f E cC
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (TOC : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
      (UNF : proj1_sig (closureC_dec cC) = inr _ vC0),
      << fC :: E, vC >> |> << fC0 :: E, vC0 >>
  where " a '|>' b " := (transition a b) : eam_scope.

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := term
    with Definition value := valueC
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
      (cl, E), (clC, EC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
    end.

  Parameter closure_red : forall cC r EC cl E
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Parameter context_red : forall fC vC r EC cl E
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
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

  Inductive dec : term -> envC -> contextC -> valueC -> Prop :=
  | dec_r   : forall t t0 sC sC0 EC EC0 E r c v
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (UNF : proj1_sig (closure_red _ _ _ _ _ DCL CTR) = (pairC t0 sC0, EC0))
      (DEC : dec t0 sC0 EC0 v),
      dec t sC EC v
  | dec_v_e : forall t sC v vC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNF : proj1_sig (closure_val _ _ DCL) = vC),
      dec t sC emptyC vC
  | dec_v_r : forall t t0 sC sC0 E EC EC0 fC vC vC0 v r c
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (UNC : proj1_sig (context_red _ _ _ _ _ _ DCT CTR) = (pairC t0 sC0, EC0))
      (DEC : dec t0 sC0 EC0 vC0),
      dec t sC (fC :: EC) vC0
  | dec_v_c  : forall t t0 sC sC0 vC vC0 fC fC0 E v c f
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (UNC : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0))
      (DEC : dec t0 sC0 (fC0 :: E) vC0),
      dec t sC (fC :: E) vC0.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall t v
      (DEC : dec t nil emptyC v),
      eval t v.

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
      (cl, E), (clC, EC) => 
        cl = closureC_to_closure clC /\ E = contextC_to_context EC
    end.

  Parameter closure_red : forall cC r EC cl E
    (DCL : dec_closure (closureC_to_closure cC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
  Parameter context_red : forall fC vC r EC cl E
    (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
    (CTR : contract r (contextC_to_context EC) = Some (cl, E)),
    {p : closureC * contextC | eqP (cl, E) p}.
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
  | c_eval  : term -> envC -> contextC -> configuration
  | c_final : valueC -> configuration.

  Notation " <<i t >> " := (c_init t) : pem_scope.
  Notation " << t , s , E >> " := (c_eval t s E) : pem_scope.
  Notation " <<f v >> " := (c_final v) : pem_scope.

  Open Scope red_scope.
  Open Scope pem_scope.

  Reserved Notation " a '|>' b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t,
      <<i t >> |> << t, nil, emptyC >>
  | t_red  : forall t t0 sC sC0 EC EC0 E r c
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (UNF : proj1_sig (closure_red _ _ _ _ _ DCL CTR) = (pairC t0 sC0, EC0)),
      << t, sC, EC >> |> << t0, sC0, EC0 >>
  | t_cval : forall t sC v vC
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNF : proj1_sig (closure_val _ _ DCL) = vC),
      << t, sC, emptyC >> |> <<f vC >>
  | t_cred : forall t t0 sC sC0 fC EC EC0 E vC v r c
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
      (CTR : contract r (contextC_to_context EC) = Some (c, E))
      (UNC : proj1_sig (context_red _ _ _ _ _ _ DCT CTR) = (pairC t0 sC0, EC0)),
      << t, sC, fC :: EC >> |> << t0, sC0, EC0 >>
  | t_crec : forall t t0 sC sC0 fC fC0 E vC v c f
      (DCL : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
      (UNV : proj1_sig (closure_val _ _ DCL) = vC)
      (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
      (UNC : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0)),
      << t, sC, fC :: E >> |> << t0, sC0, fC0 :: E >>
  where " c '|>' c0 " := (transition c c0) : pem_scope.

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.valueC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_PE_MACHINE.
