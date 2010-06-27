Require Export refocusing_lang_env.

Module Type RED_SEM (R : RED_LANG).

  Import R.
  Declare Module P : LANG_PROP R.
  Import P.
  Open Scope red_scope.

  Parameter dec : closure -> context -> decomp -> Prop.

  (** A redex in context will only ever be reduced to itself *)
  Axiom dec_redex_self : forall (r : redex) (c : context), dec (redex_to_closure r) c (d_red r c).

  Axiom decompose : forall c, (exists v : value, c = R.value_to_closure v) \/
      (exists r : redex, exists E :context, c = E [ redex_to_closure r ]).

  (** dec is left inverse of plug *)
  Axiom dec_correct : forall c E d, dec c E d -> decomp_to_closure d = E [c].

  Axiom dec_plug : forall E E0 c d, dec (E [c]) E0 d -> dec c (E · E0) d.
  Axiom dec_plug_rev : forall E E0 c d, dec c (E · E0) d -> dec (E [c]) E0 d.

  Inductive decempty : closure -> decomp -> Prop :=
  | d_intro : forall (c : closure) (d : decomp) (DEC : dec c empty d), decempty c d.

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall (v : value), iter (d_val v) v
  | i_red : forall (r : redex) (c : closure) (E : context) (d : decomp) (v : value)
              (CONTR : contract r = Some c)
              (D_EM  : decempty (E [c]) d)
              (R_IT  : iter d v),
              iter (R.d_red r E) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (d : decomp) (v : value)
                (D_EM : decempty (pair t nil) d)
                (ITER : iter d v),
                eval t v.

End RED_SEM.

Module Type RED_REF_SEM (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.
  
  (** A decomposition function specified in terms of the atomic functions above *)
  Inductive dec : closure -> context -> decomp -> Prop :=
  | d_r    : forall (c : closure) (E : context) (r : redex)
               (DCL  : dec_closure c = in_red r),
               dec c E (d_red r E)
  | d_v    : forall (c : closure) (E : context) (v : value) (d : decomp)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v d),
               dec c E d
  | d_clo  : forall (c c0 : closure) (E : context) (f : frame) (d : decomp)
               (DCL   : dec_closure c = in_clo c0 f)
               (DEC_C : dec c0 (f :: E) d),
               dec c E d
  with decctx :  context -> value -> decomp -> Prop :=
  | dc_val  : forall (v : value), decctx empty v (d_val v)
  | dc_r    : forall (v : value) (f : frame) (E : context) (r : redex)
                (DCT  : dec_context f v = in_red r),
                decctx (f :: E) v (d_red r E)
  | dc_v    : forall (v v0 : value) (f : frame) (E : context) (d : decomp)
                (DCT   : dec_context f v = in_val v0)
                (DEC_E : decctx E v0 d),
                decctx (f :: E) v d
  | dc_clo  : forall (v : value) (f f0 : frame) (E : context) (c : closure) (d : decomp)
                (DCT   : dec_context f v = R.in_clo c f0)
                (DEC_C : dec c (f0 :: E) d),
                decctx (f :: E) v d.

  Axiom dec_val_self : forall v E d, dec (value_to_closure v) E d <-> decctx E v d.
  Declare Module RS : RED_SEM R with Definition dec := dec.
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

(*  Definition dcl c t sC ofC : Prop :=
  match ofC with
  | None => c = closureC_to_closure (pairC t sC)
  | Some fC => dec_closure c = in_clo (closureC_to_closure (pairC t sC)) (frameC_to_frame fC)
  end.

  Parameter closure_red : forall cC r cl (DCL : dec_closure (closureC_to_closure cC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end}.
  Parameter context_red : forall fC vC r cl (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end }.
  Parameter closure_val : forall cC v (DCL : dec_closure (closureC_to_closure cC) = in_val v), { vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    { p : term * envC * frameC | match p with 
      (t, sC, fC) => cl = closureC_to_closure (pairC t sC) /\ f = frameC_to_frame fC
    end}.*)

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

End RED_REF_SEM.

Module Type PE_REF_SEM (R : RED_LANG).

  Declare Module Red_Sem : RED_REF_SEM R.

  Axiom dec_context_not_val : forall v v0 ec, ~(Red_Sem.dec_context ec v = R.in_val v0).
  Axiom dec_closure_value : forall v, Red_Sem.dec_closure (R.value_to_closure v) = R.in_val v.
  Axiom closureC_dec_not_right : forall cC p, ~(proj1_sig (R.closureC_dec cC) = inr _ p).

End PE_REF_SEM.

Module Type RED_PROP (R : RED_LANG) (RS : RED_REF_SEM(R)).

  Import R.
  Import RS.RS.
  Declare Module P : LANG_PROP R.
  Import P.
  Open Scope red_scope.

  Axiom dec_is_function : forall c d d0, decempty c d -> decempty c d0 -> d = d0.
  Axiom iter_is_function : forall d v v0, iter d v -> iter d v0 -> v = v0.
  Axiom eval_is_function : forall t v v0, eval t v -> eval t v0 -> v = v0.
  Axiom dec_correct : forall c E d, dec c E d -> decomp_to_closure d = E [c].
  Axiom dec_total : forall c, exists d, decempty c d.
  Axiom unique_decomposition : forall c : closure, (exists v : value, c = value_to_closure v) \/ 
      (exists r : redex, exists E : context, c = E [redex_to_closure r] /\
	  forall (r0 : redex) (E0 : context), c = E0 [redex_to_closure r0] -> r = r0 /\ E = E0).

End RED_PROP.

Module Type PRE_ABSTRACT_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.
    
  (** A decomposition relation specified in terms of the atomic functions above *)
  Inductive dec : closure -> context -> decomp -> Prop :=
  | d_r    : forall (c : closure) (E : context) (r : redex)
               (DCL  : dec_closure c = in_red r),
               dec c E (d_red r E)
  | d_v    : forall (c : closure) (E : context) (v : value) (d : decomp)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v d),
               dec c E d
  | d_clo  : forall (c c0 : closure) (E : context) (f : frame) (d : decomp)
               (DCL   : dec_closure c = in_clo c0 f)
               (DEC_C : dec c0 (f :: E) d),
               dec c E d
  with decctx :  context -> value -> decomp -> Prop :=
  | dc_val  : forall (v : value), decctx empty v (d_val v)
  | dc_r    : forall (v : value) (f : frame) (E : context) (r : redex)
                (DCT  : dec_context f v = in_red r),
                decctx (f :: E) v (d_red r E)
  | dc_v    : forall (v v0 : value) (f : frame) (E : context) (d : decomp)
                (DCT   : dec_context f v = in_val v0)
                (DEC_E : decctx E v0 d),
                decctx (f :: E) v d
  | dc_clo  : forall (v : value) (f f0 : frame) (E : context) (c : closure) (d : decomp)
                (DCT   : dec_context f v = R.in_clo c f0)
                (DEC_C : dec c (f0 :: E) d),
                decctx (f :: E) v d.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive iter : decomp -> value -> Prop :=
  | i_val : forall (v : value), iter (d_val v) v
  | i_red : forall (r : redex) (c : closure) (E : context) (d : decomp) (v : value)
              (CONTR  : contract r = Some c)
              (DEC    : dec c E d)
              (R_ITER : iter d v),
              iter (d_red r E) v.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (d : decomp) (v : value)
                (DEC  : dec (pair t nil) empty d)
                (ITER : iter d v),
                eval t v.

End PRE_ABSTRACT_MACHINE.

Module Type STAGED_ABSTRACT_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.

  Inductive dec : closure -> context -> value -> Prop :=
  | d_dec  : forall (c : closure) (E : context) (r : redex) (v : value)
               (DCL   : dec_closure c = in_red r)
               (ITER  : iter (d_red r E) v),
               dec c E v
  | d_v    : forall (c : closure) (E : context) (v v0 : R.value)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v v0),
               dec c E v0
  | d_clo  : forall (c c0 : closure) (f : frame) (E : context) (v : value)
               (DCL   : dec_closure c = in_clo c0 f)
               (DEC_C : dec c0 (f :: E) v),
               dec c E v
  with decctx : context -> value -> value -> Prop :=
  | dc_end  : forall (v v0 : value)
               (ITER  : iter (d_val v) v0),
               decctx empty v v0
  | dc_dec  : forall (v v0 : value) (f : frame) (E : context) (r : redex)
               (DCT   : dec_context f v = in_red r)
               (ITER  : iter (d_red r E) v0),
               decctx (f :: E) v v0
  | dc_val  : forall (v v0 v1 : value) (f : frame) (E : context)
               (DCT   : dec_context f v = in_val v0)
               (DEC_E : decctx E v0 v1),
               decctx (f :: E) v v1
  | dc_term : forall (v v0 : value) (c : closure) (f f0 : frame) (E : context)
               (DCT   : dec_context f v = in_clo c f0)
               (DEC_C : dec c (f0 :: E) v0),
               decctx (f :: E) v v0
  with iter : decomp -> value -> Prop :=
  | i_val : forall (v : value), iter (d_val v) v
  | i_red : forall (r : redex) (E : context) (c : closure) (v : value)
               (CONTR : contract r = Some c)
               (DEC_C : dec c E v),
               iter (d_red r E) v.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop
  with iter_Ind := Induction for iter Sort Prop.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value), dec (pair t nil) empty v -> eval t v.

End STAGED_ABSTRACT_MACHINE.

Module Type EVAL_APPLY_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.
    
  Inductive dec : closure -> context -> value -> Prop :=
  | d_d_r  : forall (c c0 : closure) (E : context) (r : redex) (v : value)
               (DCL   : dec_closure c = in_red r)
               (CONTR : contract r = Some c0)
               (DEC_C : dec c0 E v),
               dec c E v
  | d_v    : forall (c : closure) (E : context) (v v0 : value)
               (DCL   : dec_closure c = in_val v)
               (DEC_E : decctx E v v0),
               dec c E v0
  | d_clo  : forall (c c0 : closure) (f : frame) (E : context) (v : value)
               (DCL   : dec_closure c = in_clo c0 f) 
               (DEC_C : dec c0 (f :: E) v),
               dec c E v
  with decctx : context -> value -> value -> Prop :=
  | dc_end : forall (v : value), decctx empty v v
  | dc_red : forall (v v0 : value) (f : frame) (E : context) (r : redex) (c : closure)
               (DCT   : dec_context f v = in_red r)
               (CONTR : contract r = Some c)
               (DEC_C : dec c E v0),
               decctx (f :: E) v v0
  | dc_rec : forall (v v0 v1 : value) (f : frame) (E : context)
               (DCT   : dec_context f v = in_val v0)
               (DEC_E : decctx E v0 v1),
               decctx (f :: E) v v1
  | dc_clo : forall (v v0 : value) (f f0 : frame) (E : context) (c : closure)
               (DCT   : dec_context f v = in_clo c f0)
               (DEC_C : dec c (f0 :: E) v0),
               decctx (f :: E) v v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value), dec (pair t nil) empty v -> eval t v.

End EVAL_APPLY_MACHINE.

Module Type EVAL_APPLY_MACHINE_C (R : RED_LANG).
  Import R.

  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.

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

  Inductive dec : closureC -> contextC -> valueC -> Prop :=
  | d_d_r  : forall (c c0 : closureC) (cc : closure) (E : contextC) (ofc : option frameC) (r : redex) (v : valueC)
               (DCL   : dec_closure (closureC_to_closure c) = in_red r)
               (CONTR : contract r = Some cc)
               (TO_C  : proj1_sig (closure_red _ _ _ DCL CONTR) = (c0, ofc))
               (DEC_C : dec c0 (opt_to_list ofc ++ E) v),
               dec c E v
  | d_v    : forall (c : closureC) (E : contextC) (vv : value) (v v0 : valueC)
               (DCL   : dec_closure (closureC_to_closure c) = in_val vv)
               (TO_C  : proj1_sig (closure_val _ _ DCL) = v)
               (DEC_E : decctx E v v0),
               dec c E v0
(*  | d_clo  : forall (c c0 : closureC) (cc : closure) (f : frame) (fC : frameC) (E : contextC) (v : valueC)
               (DCL   : dec_closure c = in_clo cc f)
               (TO_C  : closure_val
               (DEC_C : dec c0 (f :: E) v),
               dec c E v*)
  with decctx : contextC -> valueC -> valueC -> Prop :=
  | dc_end : forall (v : valueC), decctx emptyC v v
  | dc_red : forall (v v0 : valueC) (f : frameC) (E : contextC) (r : redex) (c : closure) (cC : closureC) (ofc : option frameC)
               (DCT   : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
               (CONTR : contract r = Some c)
               (TO_C  : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, ofc))
               (DEC_C : dec cC (opt_to_list ofc ++ E) v0),
               decctx (f :: E) v v0
  | dc_rec : forall (v v0 v1 : valueC) (vv : value) (f : frameC) (E : contextC)
               (DCT   : dec_context (frameC_to_frame f) (valueC_to_value v) = in_val vv)
               (TO_C  : proj1_sig (context_val _ _ _ DCT) = v0)
               (DEC_E : decctx E v0 v1),
               decctx (f :: E) v v1
  | dc_clo : forall (v v0 : valueC) (f f0 : frameC) (ff : frame) (E : contextC) (c : closure) (cC : closureC)
               (DCT   : dec_context (frameC_to_frame f) (valueC_to_value v) = in_clo c ff)
               (TO_C  : proj1_sig (context_clo _ _ _ _ DCT) = (cC, f0))
               (DEC_C : dec cC (f0 :: E) v0),
               decctx (f :: E) v v0.

  Scheme dec_Ind := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall (t : term) (v : valueC), dec (pairC t nil) emptyC v -> eval t v.

End EVAL_APPLY_MACHINE_C.

Module Type UNFOLDED_EVAL_APPLY_MACHINE (R : RED_LANG).
  Import R.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame   -> value -> interm_dec.

(*  Definition dcl c t sC ofC : Prop :=
  match ofC with
  | None => c = closureC_to_closure (pairC t sC)
  | Some fC => dec_closure c = in_clo (closureC_to_closure (pairC t sC)) (frameC_to_frame fC)
  end.

  Parameter closure_red : forall cC r cl (DCL : dec_closure (closureC_to_closure cC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end }.
  Parameter context_red : forall fC vC r cl (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end}.
  Parameter closure_val : forall cC v (DCL : dec_closure (closureC_to_closure cC) = in_val v), { vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    { p : term * envC * frameC | match p with 
      (t, sC, fC) => cl = closureC_to_closure (pairC t sC) /\ f = frameC_to_frame fC
    end}.*)
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

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.

  Inductive dec : term -> envC -> contextC -> valueC -> Prop :=
  | d_r_t : forall t t0 sC sC0 EC front v r c cC
            (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
            (CONTR  : contract r = Some c)
            (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, front))
            (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t0, sC0))
            (DEC_C  : dec t0 sC0 (opt_to_list front ++ EC) v),
            dec t sC EC v
  | d_r_v : forall t sC EC front v v0 r c cC
            (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
            (CONTR  : contract r = Some c)
            (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, front))
            (UNFOLD : proj1_sig (closureC_dec cC) = inr _ v0)
            (DEC_C  : decctx (opt_to_list front ++ EC) v0 v),
            dec t sC EC v
  | d_v   : forall t sC EC v vC v0
            (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
            (TO_C   : proj1_sig (closure_val _ _ DCL) = vC)
            (DEC_E  : decctx EC vC v0),
            dec t sC EC v0
  with decctx : contextC -> valueC -> valueC -> Prop :=
  | dc_val : forall vC, decctx emptyC vC vC
  | dc_r_t : forall fC EC vC vC0 t sC front r c cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
             (CONTR  : contract r = Some c)
             (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, front))
             (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC))
             (DEC_C  : dec t sC (opt_to_list front ++ EC) vC0),
             decctx (fC :: EC) vC vC0
  | dc_r_v : forall fC EC vC vC0 vC1 front r c cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
             (CONTR  : contract r = Some c)
             (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, front))
             (UNFOLD : proj1_sig (closureC_dec cC) = inr _ vC1)
             (DEC_C  : decctx (opt_to_list front ++ EC) vC1 vC0),
             decctx (fC :: EC) vC vC0
  | dc_v   : forall fC EC vC vC0 vC1 v
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v)
             (TO_C   : proj1_sig (context_val _ _ _ DCT) = vC0)
             (DEC_E  : decctx EC vC0 vC1),
             decctx (fC :: EC) vC vC1
  | dc_c_t : forall fC fC0 EC vC vC0 t sC c f cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
             (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
             (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC))
             (DEC_C  : dec t sC (fC0 :: EC) vC0),
             decctx (fC :: EC) vC vC0             
  | dc_c_v : forall fC fC0 EC vC vC0 vC1 c f cC
             (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
             (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
             (UNFOLD : proj1_sig (closureC_dec cC) = inr _ vC1)
             (DEC_C  : decctx (fC0 :: EC) vC1 vC0),
             decctx (fC :: EC) vC vC0.

  Scheme dec_Ind  := Induction for dec Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall t v, dec t nil emptyC v -> eval t v.

End UNFOLDED_EVAL_APPLY_MACHINE.

Module Type PROPER_EA_MACHINE (R : RED_LANG).
  Import R.
  Declare Module P : LANG_PROP R.
  Import P.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.
(*  Definition dcl c t sC ofC : Prop :=
  match ofC with
  | None => c = closureC_to_closure (pairC t sC)
  | Some fC => dec_closure c = in_clo (closureC_to_closure (pairC t sC)) (frameC_to_frame fC)
  end.

  Parameter closure_red : forall cC r cl (DCL : dec_closure (closureC_to_closure cC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end }.
  Parameter context_red : forall fC vC r cl (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end}.
  Parameter closure_val : forall cC v (DCL : dec_closure (closureC_to_closure cC) = in_val v), { vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    { p : term * envC * frameC | match p with 
      (t, sC, fC) => cl = closureC_to_closure (pairC t sC) /\ f = frameC_to_frame fC
    end}.*)
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

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.

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

  Reserved Notation " a → b " (at level 40, no associativity).
  
  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t, <<i t >> → << t, nil, emptyC >>
  | t_redt : forall t t0 sC sC0 E ofC r c cC
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t0, sC0)),
               << t, sC, E>> → << t0, sC0, opt_to_list ofC × E >>
  | t_redv : forall t sC E ofC r c cC v
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (closure_red _ _ _ DCL CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inr _ v),
               << t, sC, E>> → << opt_to_list ofC × E, v >>
  | t_val  : forall t sC E v vC
  	       (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (TO_C   : proj1_sig (closure_val _ _ DCL) = vC),
               << t, sC, E >> → << E, vC >>
  | t_cfin : forall v, << emptyC, v >> → <<f v >>
  | t_credt: forall f v r c t sC ofC E cC
               (DCT    : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
               << f :: E, v >> → << t, sC, opt_to_list ofC × E >>
  | t_credv: forall f v v0 r c ofC E cC
               (DCT    : dec_context (frameC_to_frame f) (valueC_to_value v) = in_red r)
               (CONTR  : contract r = Some c)
               (TO_C   : proj1_sig (context_red _ _ _ _ DCT CONTR) = (cC, ofC))
               (UNFOLD : proj1_sig (closureC_dec cC) = inr _ v0),
               << f :: E, v >> → << opt_to_list ofC × E, v0 >>
  | t_cval : forall vC vC0 fC v0 E
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v0)
               (TO_C   : proj1_sig (context_val _ _ _ DCT) = vC0),
               << fC :: E, vC >> → << E, vC0 >>
  | t_cct  : forall fC fC0 vC t sC c f E cC
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
               (UNFOLD : proj1_sig (closureC_dec cC) = inl _ (t, sC)),
               << fC :: E, vC >> → << t, sC, fC0 :: E >>
  | t_ccv  : forall fC fC0 vC vC0 c f E cC
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (TO_C   : proj1_sig (context_clo _ _ _ _ DCT) = (cC, fC0))
               (UNFOLD : proj1_sig (closureC_dec cC) = inr _ vC0),
               << fC :: E, vC >> → << fC0 :: E, vC0 >>
  where " a → b " := (transition a b).

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

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.
(*  Definition dcl c t sC ofC : Prop :=
  match ofC with
  | None => c = closureC_to_closure (pairC t sC)
  | Some fC => dec_closure c = in_clo (closureC_to_closure (pairC t sC)) (frameC_to_frame fC)
  end.

  Parameter closure_red : forall cC r cl (DCL : dec_closure (closureC_to_closure cC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end }.
  Parameter context_red : forall fC vC r cl (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end}.
  Parameter closure_val : forall cC v (DCL : dec_closure (closureC_to_closure cC) = in_val v), { vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    { p : term * envC * frameC | match p with 
      (t, sC, fC) => cl = closureC_to_closure (pairC t sC) /\ f = frameC_to_frame fC
    end}.*)
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

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.

  Open Scope red_scope.

  Inductive dec : term -> envC -> contextC -> valueC -> Prop :=
  | dec_r    : forall t t0 sC sC0 ofC E r c v
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
                 (CONTR  : contract r = Some c)
                 (UNFOLD : proj1_sig (closure_red _ _ _ DCL CONTR) = (pairC t0 sC0, ofC))
                 (DEC    : dec t0 sC0 (opt_to_list ofC × E) v),
                 dec t sC E v
  | dec_val  : forall t sC v vC
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNFOLD : proj1_sig (closure_val _ _ DCL) = vC),
                 dec t sC emptyC vC
  | dec_v_r  : forall t t0 sC sC0 E ofC fC vC vC0 v r c
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
                 (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
                 (CONTR  : contract r = Some c)
                 (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = (pairC t0 sC0, ofC))
                 (DEC    : dec t0 sC0 (opt_to_list ofC × E) vC0),
                 dec t sC (fC :: E) vC0
  | dec_v_c  : forall t t0 sC sC0 vC vC0 fC fC0 E v c f
                 (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
                 (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
                 (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
                 (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0))
                 (DEC    : dec t0 sC0 (fC0 :: E) vC0),
                 dec t sC (fC :: E) vC0.

  Scheme dec_Ind := Induction for dec Sort Prop.

  Inductive eval : term -> valueC -> Prop :=
  | e_intro : forall t v, dec t nil emptyC v -> eval t v.

  Close Scope red_scope.

End PUSH_ENTER_MACHINE.

Module Type PROPER_PE_MACHINE (R : RED_LANG).
  Import R.
  Declare Module P : LANG_PROP R.
  Import P.

  (** Functions specifying atomic steps of induction on terms and contexts -- needed to avoid explicit induction on terms and contexts in construction of the AM *)
  Parameter dec_closure : closure -> interm_dec.
  Parameter dec_context : frame -> value -> interm_dec.
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
(*  Definition dcl c t sC ofC : Prop :=
  match ofC with
  | None => c = closureC_to_closure (pairC t sC)
  | Some fC => dec_closure c = in_clo (closureC_to_closure (pairC t sC)) (frameC_to_frame fC)
  end.

  Parameter closure_red : forall cC r cl (DCL : dec_closure (closureC_to_closure cC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end }.
  Parameter context_red : forall fC vC r cl (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r) (CTR : contract r = Some cl),
    {p : term * envC * option frameC | match p with (t, sC, ofC) => dcl cl t sC ofC end}.
  Parameter closure_val : forall cC v (DCL : dec_closure (closureC_to_closure cC) = in_val v), { vC : valueC | v = valueC_to_value vC}.
  Parameter context_val : forall fC vC v (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_val v),
    {vC0 : valueC | v = valueC_to_value vC0}.
  Parameter context_clo : forall fC vC cl f (DCT : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo cl f),
    { p : term * envC * frameC | match p with 
      (t, sC, fC) => cl = closureC_to_closure (pairC t sC) /\ f = frameC_to_frame fC
    end}.*)

  Axiom dec_closure_correct : forall c, match dec_closure c with
    | in_red r => redex_to_closure r = c
    | in_val v => value_to_closure v = c
    | in_clo c0 f0 => atom_plug c0 f0 = c
  end.
  Axiom dec_context_correct : forall f v, match dec_context f v with
    | in_red r  => redex_to_closure r  = atom_plug (value_to_closure v) f
    | in_val v0 => value_to_closure v0 = atom_plug (value_to_closure v) f
    | in_clo c0 f0 => atom_plug c0 f0  = atom_plug (value_to_closure v) f
  end.

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

  Reserved Notation " a → b " (at level 40, no associativity).

  Inductive transition : configuration -> configuration -> Prop :=
  | t_init : forall t, <<i t >> → << t, nil, emptyC >>
  | t_red  : forall t t0 sC sC0 ofC E r c
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (closure_red _ _ _ DCL CONTR) = (pairC t0 sC0, ofC)),
               << t, sC, E >> → << t0, sC0, opt_to_list ofC × E >>
  | t_cval : forall t sC v vC
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNFOLD : proj1_sig (closure_val _ _ DCL) = vC),
               << t, sC, emptyC >> → <<f vC >>
  | t_cred : forall t t0 sC sC0 fC ofC E vC v r c
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_red r)
               (CONTR  : contract r = Some c)
               (UNFOLD : proj1_sig (context_red _ _ _ _ DCT CONTR) = (pairC t0 sC0, ofC)),
               << t, sC, fC :: E >> → << t0, sC0, opt_to_list ofC × E >>
  | t_crec : forall t t0 sC sC0 fC fC0 E vC v c f
               (DCL    : dec_closure (closureC_to_closure (pairC t sC)) = in_val v)
               (UNF_C  : proj1_sig (closure_val _ _ DCL) = vC)
               (DCT    : dec_context (frameC_to_frame fC) (valueC_to_value vC) = in_clo c f)
               (UNFOLD : proj1_sig (context_clo _ _ _ _ DCT) = (pairC t0 sC0, fC0)),
               << t, sC, fC :: E >> → << t0, sC0, fC0 :: E >>
  where " c → c0 " := (transition c c0).

  Declare Module AM : ABSTRACT_MACHINE
    with Definition term := R.term
    with Definition value := R.valueC
    with Definition configuration := configuration
    with Definition transition := transition
    with Definition c_init := c_init
    with Definition c_final := c_final.

End PROPER_PE_MACHINE.
