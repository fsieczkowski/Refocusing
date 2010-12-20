Require Import refocusing_substitutions.
Require Import Arith.

Module Imp <: RED_LANG.

  Parameter var_name : Set.
  Parameter var_eq_dec : forall x y : var_name, {x = y}+{x<>y}.

  Definition store := var_name -> nat.

  Inductive expr : Set :=
  | enat : nat -> expr
  | evar : var_name -> expr
  | eplus : expr -> expr -> expr
  | eiszero : expr -> expr.

  Fixpoint eval_expr (e : expr) (s : store) : nat :=
    match e with
      | enat n => n
      | evar x => s x
      | eplus e1 e2 => eval_expr e1 s + eval_expr e2 s
      | eiszero e => match eval_expr e s with
                       | O => 1
                       | S _ => O
                     end
    end.

  Inductive comm : Set :=
  | cskip  : comm
  | cassn  : var_name -> expr -> comm
  | cseq   : comm -> comm -> comm
  | cif    : expr -> comm -> comm -> comm
  | cwhile : expr -> comm -> comm.
  Definition term := comm.

  Inductive val : Set :=
  | v_skip : val.
  Definition value := val.

  Inductive redex' : Set :=
  | r_seq   : value -> term -> redex'
  | r_assn  : var_name -> expr -> redex'
  | r_if    : expr -> term -> term -> redex'
  | r_while : expr -> term -> redex'.
  Definition redex := redex'.

  Inductive frame' : Set :=
  | f_seqL : term  -> frame'.
  Definition frame := frame'.

  Definition value_to_term (v : value) : term :=
    match v with v_skip => cskip end.
  Coercion value_to_term : value >-> term.
  Definition redex_to_term (r : redex) : term :=
    match r with
      | r_seq v t    => cseq (v : term) t
      | r_assn x e   => cassn x e
      | r_if e c1 c2 => cif e c1 c2
      | r_while e c  => cwhile e c
    end.
  Coercion redex_to_term : redex >-> term.

  Lemma value_to_term_injective : forall v v' : value, 
    value_to_term v = value_to_term v' -> v = v'.
  Proof.
    destruct v; destruct v'; trivial.
  Qed.
  Lemma redex_to_term_injective : forall r r' : redex,
    redex_to_term r = redex_to_term r' -> r = r'.
  Proof.
    destruct r; destruct r'; intro H; inversion H; subst; f_equal;
      auto using value_to_term_injective.
  Qed.
  Definition context := list frame.
  Definition empty : context := nil.

  Definition compose (c0 c1 : context) : context := c0 ++ c1.
  Definition atom_plug (t : term) (f : frame) : term :=
    match f with
      | f_seqL t0 => cseq t t0
    end.
  Definition plug (t : term) (c : context) : term := fold_left atom_plug c t.

  Definition state := store.
  Definition init : state := fun x => 0.
  Definition answer := (value * state)%type.
  Definition contract (r : redex) (G : state) : option (term * state) :=
    match r with
      | r_seq (v_skip) t => Some (t, G)
      | r_assn x e       =>
          Some (cskip, fun y => if var_eq_dec x y then eval_expr e G else G y)
      | r_if e c1 c2     =>
          Some (if eq_nat_dec (eval_expr e G) 0 then c1 else c2, G)
      | r_while e c      => Some (if eq_nat_dec (eval_expr e G) 0
          then cskip else cseq c (cwhile e c), G)
    end.

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

  Lemma value_trivial : forall v : value, only_trivial (value_to_term v).
  Proof.
    unfold only_trivial; intros v t E; revert t; induction E; intros;
      [left; reflexivity | right].
    destruct a; simpl in *; destruct (IHE _ H) as [HEq | [v1 HEq]]; subst;
      simpl in *; destruct v; try discriminate; destruct v1; discriminate.
  Qed.  
  Lemma redex_trivial : forall r : redex, only_trivial (redex_to_term r).
    unfold only_trivial; intros r t E; revert t; induction E; intros;
      [left; reflexivity | right].
    destruct a; simpl in *; (destruct (IHE _ H) as [HEq | [v1 HEq]]; subst;
      [| destruct v1; discriminate]); destruct r; inversion H; subst; eauto.
  Qed.
  Lemma value_redex : forall v r,
    value_to_term v <> redex_to_term r.
  Proof.
    destruct v; destruct r; intro HD; discriminate.
  Qed.

  Lemma ot_subt : forall c c0 f, 
    only_trivial c -> f a[ c0 ] = c ->
    exists v, c0 = value_to_term v.
  Proof with eauto.
    intros; destruct (H c0 (f :: nil)) as [H1 | [v H1]]; try discriminate...
  Qed.

  Ltac ot_v c f :=
    match goal with
      | [Hot : (only_trivial ?H1) |- _] => 
          destruct (ot_subt _ c f Hot) as [?v HV]; [auto | subst c]
    end.

  Ltac mlr rv :=
  match goal with
    | [ |- (exists v, ?H1 = value_to_term v)
        \/ (exists r, ?H1 = redex_to_term r)] =>
      match rv with
        | (?v : value) => left; exists v
        | (?r : redex) => right; exists r
      end; simpl; auto
  end.

  Lemma trivial_val_red : forall t : term, only_trivial t ->
    (exists v, t = value_to_term v) \/ (exists r, t = redex_to_term r).
  Proof.
    destruct t; intros.
    mlr v_skip.
    mlr (r_assn v e).
    ot_v t1 (f_seqL t2); mlr (r_seq v t2).
    mlr (r_if e t1 t2).
    mlr (r_while e t).
  Qed.

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

End Imp.

Module Imp_Eval <: RED_SEM Imp.

  Import Imp.
  Module P : LANG_PROP Imp := Lang_Prop Imp.
  Import P.
  Open Scope red_scope.

  Inductive dec' : term -> context -> decomp -> Prop :=
  | val_ctx   : forall E d
      (HDec : decctx v_skip E d),
      dec' cskip E d
  | asn_dec   : forall x e E, dec' (cassn x e) E (d_red (r_assn x e) E)
  | if_dec    : forall e c1 c2 E, dec' (cif e c1 c2) E (d_red (r_if e c1 c2) E)
  | while_dec : forall e c E, dec' (cwhile e c) E (d_red (r_while e c) E)
  | seq_ctx   : forall c1 c2 E d
      (HDec : dec' c1 (f_seqL c2 :: E) d),
      dec' (cseq c1 c2) E d
  with decctx : value -> context -> decomp -> Prop :=
  | empty_dec : decctx v_skip [] (d_val v_skip)
  | seq_dec   : forall t E,
      decctx v_skip (f_seqL t :: E) (d_red (r_seq v_skip t) E).
  Definition dec := dec'.

  Scheme dec_Ind := Induction for dec' Sort Prop
  with decctx_Ind := Induction for decctx Sort Prop.

  Lemma dec_redex_self : forall r E, dec (redex_to_term r) E (d_red r E).
  Proof with eauto using dec', decctx.
    destruct r; unfold dec; simpl; intros...
    destruct v...
  Qed.

  Lemma decompose : forall t, (exists v, t = value_to_term v) \/
      (exists r, exists E : context, E [ redex_to_term r ] = t).
  Proof.
    induction t.
    left; exists v_skip; reflexivity.
    right; exists (r_assn v e); exists []; reflexivity.
    right; clear IHt2; destruct IHt1 as [[v HEq] | [r [E HEq]]]; subst.
    exists (r_seq v t2); exists []; reflexivity.
    exists r; exists (E · (f_seqL t2 :: [])); apply plug_compose.
    right; exists (r_if e t1 t2); exists []; reflexivity.
    right; exists (r_while e t); exists []; reflexivity.
  Qed.

  (** dec is left inverse of plug *)
  Lemma dec_correct : forall t E d, dec t E d -> decomp_to_term d = E [ t ].
  Proof.
    induction 1 using dec_Ind with
      (P := fun t E d (HDec : dec t E d) => decomp_to_term d = E [ t ])
      (P0:= fun v E d (HDec : decctx v E d) => decomp_to_term d = E [ v ]);
      auto.
  Qed.

  Lemma dec_plug : forall E E0 t d, dec (E [ t ]) E0 d -> dec t (E · E0) d.
    induction E; simpl; intros; [assumption |].
    apply IHE in H; destruct a; destruct t; inversion H; subst; auto.
  Qed.
  Lemma dec_plug_rev : forall E E0 t d, dec t (E · E0) d -> dec (E [ t ]) E0 d.
    induction E; simpl; intros; [assumption |].
    apply IHE; destruct a; destruct t; constructor; assumption.
  Qed.

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

End Imp_Eval.

Module Imp_Ref <: RED_REF_LANG.

  Module R := Imp.
  Import R.
  Open Scope red_scope.

  Definition dec_term (t : term) :=
    match t with
      | cskip       => in_val v_skip
      | cassn x e   => in_red (r_assn x e)
      | cseq c1 c2  => in_term c1 (f_seqL c2)
      | cif e c1 c2 => in_red (r_if e c1 c2)
      | cwhile e c  => in_red (r_while e c)
    end.
  Definition dec_context (f : frame) (v : value) :=
    match f with f_seqL c => in_red (r_seq v c) end.

  Inductive subterm_one_step : term -> term -> Prop :=
  | st_1 : forall t t0 f (DECT : t = f a[ t0 ]), subterm_one_step t0 t.
  Lemma wf_st1 : well_founded subterm_one_step.
  Proof.
    prove_st_wf.
  Qed.

  Definition subterm_order := clos_trans_n1 term subterm_one_step.
  Notation " a <| b " := (subterm_order a b) (at level 40) : red_scope.
  Definition wf_sto : well_founded subterm_order := wf_clos_trans_r _ _ wf_st1.

  Definition frame_order (f0 f1 : frame) := False.
  Notation " a <: b " := (frame_order a b) (at level 40) : red_scope.
  Lemma wf_eco : well_founded frame_order.
  Proof.
    prove_ec_wf.
  Qed.
  Lemma dec_term_red_empty  : forall t r, dec_term t = in_red r -> only_empty t.
  Proof.
    destruct t; intros r H; inversion H; subst; clear H;
      (intros t0 E; revert t0; induction E; intros; [reflexivity | simpl in H];
      specialize (IHE _ H); subst; destruct a; destruct t0; discriminate).
  Qed.
  Lemma dec_term_val_empty  : forall t v, dec_term t = in_val v -> only_empty t.
    destruct t; intros r H; inversion H; subst; clear H.
    intros t0 E; revert t0; induction E; intros; [reflexivity | simpl in H].
    specialize (IHE _ H); subst; destruct a; destruct t0; discriminate.
  Qed.
  Lemma dec_term_term_top   : forall t t' ec, dec_term t = in_term t' ec ->
    forall ec', ~ec <: ec'.
  Proof. intuition. Qed.
  Lemma dec_context_red_bot : forall ec v r, dec_context ec v = in_red r ->
    forall ec', ~ ec' <: ec.
  Proof. intuition. Qed.
  Lemma dec_context_val_bot : forall ec v v', dec_context ec v = in_val v' -> 
    forall ec', ~ ec' <: ec.
  Proof. intuition. Qed.
  Lemma dec_context_term_next : forall ec v t ec', dec_context ec v = in_term t ec' ->
    ec' <: ec /\ forall ec'', ec'' <: ec -> ~ ec' <: ec''.
  Proof.
    destruct ec; intros v t0 f H; inversion H.
  Qed.

  Lemma dec_term_correct : forall t, match dec_term t with
    | in_red r     => redex_to_term r = t
    | in_val v     => value_to_term v = t
    | in_term t' f => f a[ t' ] = t
    end.
  Proof.
    destruct t; simpl; reflexivity.
  Qed.
  Lemma dec_context_correct : forall f v, match dec_context f v with
    | in_red r     => redex_to_term r  = f a[ value_to_term v ]
    | in_val v'    => value_to_term v' = f a[ value_to_term v ]
    | in_term t f' => f' a[ t ]        = f a[ value_to_term v ]
    end.
  Proof.
    destruct f; simpl; reflexivity.
  Qed.

  Lemma ec_order_antisym : forall f f0, f <: f0 -> ~ f0 <: f.
  Proof. intuition. Qed.
  Lemma dec_ec_ord : forall t0 t1 f0 f1, f0 a[ t0 ] = f1 a[ t1 ] ->
    f0 <: f1 \/ f1 <: f0 \/ (t0 = t1 /\ f0 = f1).
  Proof.
    destruct f0; destruct f1; intros; inversion H; subst; auto.
  Qed.
  Lemma elem_context_det : forall t0 t1 f0 f1, f0 <: f1 -> f0 a[ t0 ] = f1 a[ t1 ] ->
    exists v, t1 = value_to_term v.
  Proof.
    intros t0 t1 f0 f1 H; contradiction H.
  Qed.

End Imp_Ref.

Module Imp_RefEvalA <: RED_REF_SEM Imp := RedRefSem Imp_Ref.

Lemma dec_sem_aref : forall t E d, Imp_Eval.dec t E d <-> Imp_RefEvalA.dec t E d.
Proof with auto.
  split; intro HDec.
  induction HDec using Imp_Eval.dec_Ind with
    (P := fun t E d (HDec : Imp_Eval.dec t E d) => Imp_RefEvalA.dec t E d)
    (P0:= fun v E d (HDec : Imp_Eval.decctx v E d) => Imp_RefEvalA.decctx v E d);
    simpl in *; eauto using Imp_RefEvalA.dec, Imp_RefEvalA.decctx.
  econstructor; [reflexivity | assumption].
  econstructor 3; [reflexivity | assumption].
  induction HDec using Imp_RefEvalA.dec_Ind with
    (P := fun t E d (HDec : Imp_RefEvalA.dec t E d) => Imp_Eval.dec t E d)
    (P0:= fun v E d (HDec : Imp_RefEvalA.decctx v E d) => Imp_Eval.decctx v E d);
    simpl in *; try (destruct t; inversion DT); try (destruct f; inversion DC);
      subst; unfold Imp_Eval.dec; eauto using Imp_Eval.dec', Imp_Eval.decctx;
        destruct v; constructor.
Qed.  

Lemma iter_sem_aref : forall d G a, Imp_Eval.iter d G a <-> Imp_RefEvalA.RS.iter d G a.
Proof with eauto using Imp_Eval.iter, Imp_Eval.decempty, Imp_RefEvalA.RS.iter,
  Imp_RefEvalA.RS.decempty.
  split; induction 1...
  inversion_clear D_EM; rewrite dec_sem_aref in DEC...
  inversion_clear D_EM; rewrite <- dec_sem_aref in DEC...
Qed.

Lemma eval_sem_aref : forall t a, Imp_Eval.eval t a <-> Imp_RefEvalA.RS.eval t a.
Proof.
  split; intro H; inversion_clear H; inversion_clear D_EM.
  rewrite dec_sem_aref in DEC; rewrite iter_sem_aref in ITER;
    eauto using Imp_RefEvalA.RS.eval, Imp_RefEvalA.RS.decempty.
  rewrite <- dec_sem_aref in DEC; rewrite <- iter_sem_aref in ITER;
    eauto using Imp_Eval.eval, Imp_Eval.decempty.
Qed.

Module Imp_PEEval <: PE_REF_SEM Imp.

  Module Red_Sem := Imp_RefEvalA.
  Import Red_Sem.
  Import Imp.

  Lemma dec_context_not_val : forall v v0 f, ~(dec_context f v = in_val v0).
  Proof.
    destruct f; destruct v0; intros HF; inversion HF.
  Qed.
  Lemma dec_term_value : forall v, dec_term (value_to_term v) = in_val v.
    destruct v; simpl; reflexivity.
  Qed.

End Imp_PEEval.

Module Imp_PEM := ProperPEMachine Imp Imp_PEEval.

Module Imp_Mach : ABSTRACT_MACHINE.

  Import Imp.
  Open Scope red_scope.

  Definition term  := term.
  Definition value := answer.
  Definition configuration := Imp_PEM.configuration.
  Definition c_init  := Imp_PEM.c_init.
  Definition c_final := Imp_PEM.c_final.
  Definition c_eval  := Imp_PEM.c_eval.

  Inductive trans : configuration -> configuration -> Prop :=
  | t_init  : forall t,
      trans (c_init t) (c_eval t [] init)
  | t_seq   : forall t1 t2 E G,
      trans (c_eval (cseq t1 t2) E G) (c_eval t1 (f_seqL t2 :: E) G)
  | t_skip  : forall t E G,
      trans (c_eval cskip (f_seqL t :: E) G) (c_eval t E G)
  | t_assn  : forall x e E G,
      trans (c_eval (cassn x e) E G)
        (c_eval cskip E (fun y => if var_eq_dec x y then eval_expr e G else G y))
  | t_if    : forall e t1 t2 E G,
      trans (c_eval (cif e t1 t2) E G)
        (c_eval (if eq_nat_dec (eval_expr e G) 0 then t1 else t2) E G)
  | t_while : forall e t E G,
      trans (c_eval (cwhile e t) E G)
        (c_eval (if eq_nat_dec (eval_expr e G) 0 then cskip else cseq t (cwhile e t)) E G)
  | t_final : forall G, trans (c_eval cskip [] G) (c_final (v_skip, G)).
  Definition transition := trans.

  Inductive trans_close : configuration -> configuration -> Prop :=
  | one_step   : forall (c0 c1 : configuration), transition c0 c1 -> trans_close c0 c1
  | multi_step : forall (c0 c1 c2 : configuration), transition c0 c1 -> trans_close c1 c2 -> trans_close c0 c2.

  Inductive eval : term -> value -> Prop :=
  | e_intro : forall (t : term) (v : value), trans_close (c_init t) (c_final v) -> eval t v.

  Lemma trPE_M : forall c c0 : configuration, Imp_PEM.transition c c0 -> transition c c0.
  Proof.
    intros c c0 H; inversion H; subst; clear H.
    constructor.
    destruct t; inversion DT; subst; inversion CONTR; subst; constructor.
    destruct t; inversion DT; subst; constructor.
    destruct t; inversion DT; subst; destruct f; inversion DC; subst;
      inversion CONTR; subst; constructor.
    destruct t; inversion DT; subst; destruct f; inversion DC.
    destruct t; inversion DT; subst; constructor.
  Qed.

  Lemma tcPE_M : forall c c0 : configuration,
    Imp_PEM.AM.trans_close c c0 -> trans_close c c0.
  Proof.
    induction 1; subst; eauto using trans_close, trPE_M.
  Qed.

  Lemma evalPE_M : forall t a, Imp_PEM.AM.eval t a -> eval t a.
  Proof.
    intros t v H; inversion_clear H; auto using eval, tcPE_M.
  Qed.

  Lemma trM_PE : forall c c0 : configuration,
    transition c c0 -> Imp_PEM.AM.transition c c0.
  Proof.
    intros c c0 H; inversion H; subst; clear H; econstructor; reflexivity.
  Qed.

  Lemma tcM_PE : forall c c0 : configuration,
    trans_close c c0 -> Imp_PEM.AM.trans_close c c0.
  Proof.
    induction 1; eauto using Imp_PEM.AM.trans_close, trM_PE.
  Qed.

  Lemma evalM_PE : forall t a, eval t a -> Imp_PEM.AM.eval t a.
  Proof.
    destruct 1; eauto using Imp_PEM.AM.eval, tcM_PE.
  Qed.

  Theorem MachineCorrect : forall t a, Imp_Eval.eval t a <-> eval t a.
  Proof.
    intros; rewrite eval_sem_aref, Imp_PEM.push_enter_correct; split;
      auto using evalM_PE, evalPE_M.
  Qed.

End Imp_Mach.
