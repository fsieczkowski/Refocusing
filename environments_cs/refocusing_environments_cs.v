Require Export List.

Module Type RED_LANG.

Parameters term value redex context closure closureC valueC redexC contextC : Set.
Parameter emptyC : contextC.
Parameter empty : context.

Definition substitution := list closure.

Parameter plug : closure -> context -> closure.
Parameter compose : context -> context -> context.
Definition substitutionC := list closureC.

Parameter pair : term -> substitution -> closure.
Parameter pairC : term -> substitutionC -> closureC.

Parameter value_to_closure : value -> closure.
Parameter redex_to_closure : redex -> closure.
Parameter closureC_to_closure : closureC -> closure.
Definition subC_to_sub : substitutionC -> substitution := map closureC_to_closure.
Parameter valueC_to_value : valueC -> value.
Parameter redexC_to_redex : redexC -> redex.
Parameter valueC_to_closureC : valueC -> closureC.
Parameter contextC_to_context : contextC -> context.
Parameter composeC : contextC -> contextC -> contextC.
Axiom composeC_compose : forall c c0, contextC_to_context (composeC c c0) = compose (contextC_to_context c) (contextC_to_context c0).
Axiom contextC_to_context_injective : forall (ct ct0 : contextC), contextC_to_context ct = contextC_to_context ct0 -> ct = ct0.
Parameter contract : redex -> context -> option (closure * context).
Axiom closureC_to_closure_injective : forall (cl cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0.
Axiom commutes : forall v : valueC, closureC_to_closure (valueC_to_closureC v) = value_to_closure (valueC_to_value v).

Axiom plug_compose  : forall c1 c2 r, plug r (compose c1 c2) = plug (plug r c1) c2.
Axiom plug_empty    : forall c, plug c empty = c.
Axiom compose_empty : forall c, compose c empty = c.
Axiom empty_compose : forall c, compose empty c = c.
Axiom empty_composeC : forall c, composeC emptyC c = c.
Axiom emptyC_empty  : contextC_to_context emptyC = empty.

Axiom decompose : forall t:closure, (exists v:value, t = value_to_closure v) \/ 
    (exists r:redex, exists c:context, plug (redex_to_closure r) c = t).

Inductive decomp : Set :=
| d_val : value -> decomp
| d_red : redex -> context -> decomp.

Inductive interm_dec : Set :=
| in_dec : decomp -> interm_dec
| in_val : value -> context -> interm_dec
| in_term: closure -> context -> interm_dec.

Parameter dec_term : closure -> context -> interm_dec.
Parameter dec_context : value -> context -> interm_dec.
Axiom dec_context_empty : forall (v : value), dec_context v empty = in_dec (d_val v).
Axiom dec_term_value : forall (v : value) (c : context), dec_term (value_to_closure v) c = in_val v c.

Definition recons (p:term * substitutionC * contextC) : closure :=
match p with
| (t, s, c) => plug (closureC_to_closure (pairC t s)) (contextC_to_context c)
end.

Inductive dec_by_cls : closure -> context -> (term * substitutionC * contextC) + (valueC * contextC) -> Prop :=
| dbc_pair : forall (t : term) (s : substitutionC) (c : contextC),
             dec_by_cls (closureC_to_closure (pairC t s)) (contextC_to_context c) (inl (valueC * contextC) (t,s,c))
| dbc_val  : forall (v : valueC) (c : contextC),
             (forall t s, (valueC_to_closureC v) <> pairC t s) ->
             dec_by_cls (closureC_to_closure (valueC_to_closureC v)) (contextC_to_context c) (inr (term * substitutionC * contextC) (v, c))
| dbc_many : forall (cl cl' : closure) (c c' : context) (p : (term * substitutionC * contextC)+(valueC * contextC)),
             dec_term cl c = in_term cl' c' -> dec_by_cls cl' c' p -> dec_by_cls cl c p.


Axiom dec_by_cls_folds_left : forall t s ct cl c, dec_by_cls cl c (inl _ (t, s, ct)) -> plug cl c = plug (closureC_to_closure (pairC t s)) (contextC_to_context ct).
Axiom dec_by_cls_folds_right : forall v ct cl c, dec_by_cls cl c (inr _ (v, ct)) -> plug cl c = plug (closureC_to_closure (valueC_to_closureC v)) (contextC_to_context ct).
Axiom dec_by_cls_function : forall cl c p p', dec_by_cls cl c p -> dec_by_cls cl c p' -> p = p'.

Parameter unfold_c_red :
forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl, ct1)) ->
  {p : (term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct1 p}.

Parameter unfold_red :
forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl0, ct1)) ->
  {p:(term * substitutionC * contextC)+(valueC * contextC) | dec_by_cls cl0 ct1 p}.

Parameter unfold_c_cls :
forall (v : valueC) (ct : contextC) (cl : closure) (ct0 : context),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_term cl ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct0 p}.

Parameter unfold_cls :
forall (cl : closureC) (ct : contextC) (cl0 : closure) (ct0 : context),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_term cl0 ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl0 ct0 p}.

Axiom dec_Val :
forall t s (ct : contextC) c v,
  dec_term (closureC_to_closure (pairC t s)) (contextC_to_context ct) = in_val v c ->
  exists v0 : valueC, exists ct1 : contextC,
    (valueC_to_value v0) = v /\ c = (contextC_to_context ct1).

Axiom dec_c_Val :
forall v (ct:contextC) v0 c,
  dec_context (valueC_to_value v) (contextC_to_context ct) = in_val v0 c ->
  exists ct0 : contextC, exists v1 : valueC, (valueC_to_value v1) = v0 /\ c = (contextC_to_context ct0).

Inductive dec : closure -> context -> decomp -> Prop :=
| d_one  : forall (t : closure) (c : context) (d : decomp),
             dec_term t c = in_dec d -> dec t c d
| d_ctx  : forall (t : closure) (c c0 : context) (v : value) (d : decomp),
             dec_term t c = in_val v c0 -> decctx v c0 d -> dec t c d
| d_many : forall (t t0 : closure) (c c0 : context) (d : decomp),
             dec_term t c = in_term t0 c0 -> dec t0 c0 d -> dec t c d
with decctx : value -> context -> decomp -> Prop :=
| dc_one  : forall (v : value) (c : context) (d : decomp), dec_context v c = in_dec d -> decctx v c d
| dc_ctx  : forall (v v0 : value) (c c0 : context) (d : decomp),
              dec_context v c = in_val v0 c0 -> decctx v0 c0 d -> decctx v c d
| dc_many : forall (v : value) (c c0 : context) (t : closure) (d : decomp),
              dec_context v c = in_term t c0 -> dec t c0 d -> decctx v c d.

Axiom dec_redex_self : forall (r : redex) (c : context), dec (redex_to_closure r) c (d_red r c).

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

(** correctness of atomic decompositions *)
Definition decomp_to_term (d : decomp) : closure :=
match d with
  | d_val v => value_to_closure v
  | d_red r c0 => plug (redex_to_closure r) c0
end.
Axiom dec_term_correct : forall t c, match dec_term t c with
  | in_dec d => decomp_to_term d = plug t c
  | in_val v c0 => plug (value_to_closure v) c0 = plug t c
  | in_term t0 c0 => plug t0 c0 = plug t c
end.
Axiom dec_context_correct : forall v c, match dec_context v c with
  | in_dec d => decomp_to_term d = plug (value_to_closure v) c
  | in_val v0 c0 => plug (value_to_closure v0) c0 = plug (value_to_closure v) c
  | in_term t c0 => plug t c0 = plug (value_to_closure v) c
end.

Axiom dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
Axiom dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.

End RED_LANG.

Module Evaluator (R : RED_LANG).
Definition term := R.term.
Definition closure := R.closure.
Definition value := R.value.
Definition redex := R.redex.
Definition context := R.context.
Definition empty := R.empty.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.
Coercion R.closureC_to_closure : R.closureC >-> R.closure.
Coercion R.contextC_to_context : R.contextC >-> R.context.
Coercion R.valueC_to_value : R.valueC >-> R.value.

Definition pairC := R.pairC.
Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.

Definition dec_term := R.dec_term.
Definition dec_context := R.dec_context.

Definition dec := R.dec.
Definition decctx := R.decctx.
Definition d_one := R.d_one.
Definition d_many := R.d_many.
Definition dc_one := R.dc_one.
Definition dc_many := R.dc_many.

Definition decomp := R.decomp.
Definition d_val := R.d_val.
Definition d_red := R.d_red.

Inductive decempty : closure -> decomp -> Prop :=
| d_intro : forall (t : closure) (d : decomp), dec t empty d -> decempty t d.

Inductive iter : decomp -> value -> Prop :=
| i_val : forall (v : value), iter (d_val v) v
| i_red : forall (r : redex) (t : closure) (c c0 : context) (d : decomp) (v : value),
            contract r c = Some (t, c0) -> decempty (plug t c0) d -> iter d v -> iter (d_red r c) v.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (d : decomp) (v : value), decempty ((pairC t nil):closure) d -> iter d v -> eval t v.



(** Evaluation functions are functions :) *)
Lemma dec_is_function : forall t d d0, decempty t d -> decempty t d0 -> d = d0.
Proof with subst; auto.
intros; inversion_clear H; inversion_clear H0.
refine (R.dec_Ind (fun t c d (H:dec t c d) => forall d0, dec t c d0 -> d = d0)
(fun c v d (H:decctx c v d) => forall d0, decctx c v d0 -> d = d0)
_  _ _ _ _ _ t empty d H1 d0 H); intros; simpl...
inversion H0; rewrite H2 in e; inversion e...
apply H0; inversion H2; rewrite H3 in e; inversion e...
apply H0; inversion H2; rewrite H3 in e; inversion e...
inversion H0; rewrite H2 in e; inversion e...
apply H0; inversion H2; rewrite H3 in e; inversion e...
apply H0; inversion H2; rewrite H3 in e; inversion e...
Qed.

Lemma iter_is_function : forall d v v0, iter d v -> iter d v0 -> v = v0.
Proof.
intros; induction H; inversion H0; subst; auto; rewrite H5 in H; inversion H; subst;
assert (hh:=dec_is_function _ _ _ H1 H6); subst; apply IHiter; auto.
Qed.

Lemma eval_is_function : forall t v v0, eval t v -> eval t v0 -> v = v0.
Proof.
intros; induction H; inversion H0; subst;assert (hh := dec_is_function _ _ _ H H2);
subst; apply iter_is_function with d0; auto.
Qed.

(** dec is left inverse of plug *)
Lemma dec_correct : forall t c d, dec t c d -> R.decomp_to_term d = plug t c.
Proof.
induction 1 using R.dec_Ind with
(P := fun t c d (H:dec t c d) => R.decomp_to_term d = plug t c)
(P0:= fun v c d (H:decctx v c d) => R.decomp_to_term d = plug (value_to_closure v) c); simpl; auto;
try (assert (hh := R.dec_term_correct t c); rewrite e in hh; simpl in hh; try rewrite IHdec; auto);
assert (hh := R.dec_context_correct v c); rewrite e in hh; simpl in hh; try rewrite IHdec; auto.
Qed.

Lemma dec_total : forall t, exists d, decempty t d.
Proof.
intro t; elim (R.decompose t); intros.
destruct H as [v H]; exists (d_val v); rewrite H; constructor; econstructor 2; [ eapply R.dec_term_value | constructor ]; apply R.dec_context_empty.
destruct H as [r [c H]]; rewrite <- H; exists (d_red r c); constructor; apply R.dec_plug_rev; rewrite R.compose_empty; apply R.dec_redex_self.
Qed.

Lemma unique_decomposition : forall (cl : closure), (exists v:value, value_to_closure v = cl) \/
                               (exists r:redex, exists ct:context, cl = plug (r : closure) ct /\
                                 forall (r0:redex) ct0, (plug (r0:closure) ct0 = cl -> r=r0 /\ ct = ct0)).
Proof.
intro t; elim (R.decompose t); intros; destruct H; [left | right];
split with x; auto; destruct H; split with x0; split; auto; intros.
assert (decempty t (d_red x x0)).
constructor; rewrite <- H; apply R.dec_plug_rev; rewrite R.compose_empty; apply R.dec_redex_self.
assert (decempty t (d_red r0 ct0)).
constructor; rewrite <- H0; apply R.dec_plug_rev; rewrite R.compose_empty; apply R.dec_redex_self.
assert (hh := dec_is_function _ _ _ H1 H2); injection hh; intros; auto.
Qed.

End Evaluator.

Module PreAbstractMachine (L : RED_LANG).

Module R := Evaluator (L).
Definition term := R.term.
Definition closure := R.closure.
Definition value := R.value.
Definition redex := R.redex.
Definition context := R.context.
Definition empty := R.empty.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.

Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.
Definition pairC := R.pairC.

Definition dec_term := R.dec_term.
Definition dec_context := R.dec_context.

Definition dec := R.dec.
Definition decctx := R.decctx.
Definition d_one := R.d_one.
Definition d_many := R.d_many.
Definition dc_one := R.dc_one.
Definition dc_many := R.dc_many.

Definition decomp := R.decomp.
Definition d_val := R.d_val.
Definition d_red := R.d_red.

Inductive iter : decomp -> value -> Prop :=
| i_val : forall (v : value), iter (d_val v) v
| i_red : forall (r : redex) (t : closure) (c c0 : context) (d : decomp) (v : value),
            contract r c = Some (t, c0) -> dec t c0 d -> iter d v -> iter (d_red r c) v.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (d : decomp) (v : value), dec (pairC t nil) empty d -> iter d v -> eval t v.

Lemma iterRedPam : forall (d : decomp) (v : value), R.iter d v -> iter d v.
Proof.
induction 1; [constructor | constructor 2 with t c0 d]; auto;
inversion_clear H0; rewrite <- L.compose_empty with (c:=c0); apply L.dec_plug; auto.
Qed.

Lemma evalRedPam : forall (t : term) (v : value), R.eval t v -> eval t v.
Proof.
intros t v H; inversion_clear H; constructor 1 with d; [inversion_clear H0 | apply iterRedPam]; auto.
Qed.

Lemma iterPamRed : forall (d : decomp) (v : value), iter d v -> R.iter d v.
Proof.
induction 1; [constructor |
constructor 2 with t c0 d; auto; constructor; apply L.dec_plug_rev; rewrite L.compose_empty; auto ].
Qed.

Lemma evalPamRed : forall (t : term) (v : value), eval t v -> R.eval t v.
Proof.
intros t v H; inversion_clear H; constructor 1 with d; [ constructor | apply iterPamRed]; auto.
Qed.

End PreAbstractMachine.

Module StagedAbstractMachine (L : RED_LANG).

Module PAM := PreAbstractMachine (L).
Module R := PAM.R.
Definition term := R.term.
Definition closure := R.closure.
Definition value := R.value.
Definition redex := R.redex.
Definition context := R.context.
Definition empty := R.empty.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.

Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.
Definition pairC := R.pairC.

Definition dec_term := L.dec_term.
Definition dec_context := L.dec_context.

Definition decomp := PAM.decomp.
Definition d_val := PAM.d_val.
Definition d_red := PAM.d_red.

Definition interm_dec := L.interm_dec.
Definition in_dec := L.in_dec.
Definition in_val := L.in_val.
Definition in_term:= L.in_term.

Inductive dec : closure -> context -> value -> Prop :=
| d_one  : forall (t : closure) (c : context) (d : decomp) (v : value),
             dec_term t c = in_dec d -> iter d v -> dec t c v
| d_ctx  : forall (t : closure) (c c0 : context) (v v0 : value),
             dec_term t c = in_val v c0 -> decctx v c0 v0 -> dec t c v0
| d_many : forall (t t0 : closure) (c c0 : context) (v : value),
             dec_term t c = in_term t0 c0 -> dec t0 c0 v -> dec t c v
with decctx : value -> context -> value -> Prop :=
| dc_one  : forall (v v0 : value) (c : context) (d : decomp),
              dec_context v c = in_dec d -> iter d v0 -> decctx v c v0
| dc_ctx  : forall (v v0 v1: value) (c c0 : context),
              dec_context v c = in_val v0 c0 -> decctx v0 c0 v1 -> decctx v c v1
| dc_many : forall (v v0 : value) (t : closure) (c c0 : context),
              dec_context v c = in_term t c0 -> dec t c0 v0 -> decctx v c v0
with iter : decomp -> value -> Prop :=
| i_val : forall (v : value), iter (d_val v) v
| i_red : forall (r : redex) (c c0 : context) (t : closure) (v : value),
            contract r c = Some (t, c0) -> dec t c0 v -> iter (d_red r c) v.

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop
with iter_Ind := Induction for iter Sort Prop.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (v : value), dec (pairC t nil) empty v -> eval t v.

Lemma decPamSam : forall (t : closure) (c : context) (d : decomp),
  PAM.dec t c d -> forall (v : value), iter d v -> dec t c v.
Proof.
induction 1 using L.dec_Ind with
(P := fun t c d (H:PAM.dec t c d) => forall v, iter d v -> dec t c v)
(P0 := fun c v d (H:PAM.decctx c v d) => forall v', iter d v' -> decctx c v v');
intros; simpl;
[constructor 1 with d | constructor 2 with c0 v | constructor 3 with t0 c0 |
 constructor 1 with d | constructor 2 with v0 c0| constructor 3 with t c0  ]; auto.
Qed.

Lemma iterPamSam : forall (d : decomp) (v : value), PAM.iter d v -> iter d v.
Proof.
induction 1 as [ | r t c c0 d v H Hd H0 IH];
[constructor | constructor 2 with c0 t; try apply decPamSam with d; auto].
Qed.

Lemma evalPamSam : forall (t : term) (v : value), PAM.eval t v -> eval t v.
Proof.
intros t v H; inversion_clear H; constructor; apply decPamSam with d; try apply iterPamSam; auto.
Qed.

Lemma decSamPam : forall (t : closure) (c : context) (v : value),
  dec t c v -> forall (d : decomp), PAM.dec t c d -> PAM.iter d v.
Proof.
induction 1 using dec_Ind with
(P  := fun t c v (H:dec t c v) => forall d, PAM.dec t c d -> PAM.iter d v)
(P0 := fun v c v' (H:decctx v c v') => forall d, PAM.decctx v c d -> PAM.iter d v')
(P1 := fun d v (H:iter d v) => PAM.iter d v); intros; simpl.
(* Case 1 *)
change (L.dec_term t c = in_dec d) in e; inversion H; subst; rewrite H0 in e; try discriminate;
injection e; intros; subst; auto.
(* Case 2 *)
apply IHdec; change (L.dec_term t c = in_val v c0) in e; inversion H;
subst; rewrite H0 in e; try discriminate; injection e; intros; subst; auto.
(* Case 3 *)
apply IHdec; change (L.dec_term t c = in_term t0 c0) in e;
inversion H0; subst; rewrite H1 in e; try discriminate;
injection e; intros; subst; auto.
(* Case 4 *)
change (L.dec_context v c = in_dec d) in e; inversion H; subst;
rewrite H0 in e; try discriminate; injection e; intros; subst; auto.
(* Case 5 *)
apply IHdec; change (L.dec_context v c = in_val v0 c0) in e; inversion H; rewrite H0 in e;
try discriminate; injection e; intros; subst; auto.
(* Case 6 *)
apply IHdec; inversion H0; subst; change (L.dec_context v c = in_term t c0) in e;
rewrite H1 in e; try discriminate; injection e; intros; subst; auto.
(* Case 7 *)
constructor.
(* Case 8 *)
assert (hh:=R.dec_total (plug t c0)); destruct hh;
constructor 2 with t c0 x; auto; try apply IHdec;
rewrite <- L.compose_empty with c0; apply L.dec_plug; inversion_clear H0; auto.
Qed.

Lemma evalSamPam : forall (t : term) (v : value), eval t v -> PAM.eval t v.
Proof.
intros t v H; inversion_clear H; assert (hh := R.dec_total (pairC t nil)); destruct hh; constructor 1 with x;
try eapply decSamPam; inversion_clear H; eauto.
Qed.

Theorem evalSam : forall (t : term) (v : value), R.eval t v <-> eval t v.
Proof.
split; intro H; [ apply evalPamSam; apply PAM.evalRedPam | apply PAM.evalPamRed; apply evalSamPam ]; auto.
Qed.

Lemma dec_plug : forall c c0 t v, dec (plug t c) c0 v -> dec t (compose c c0) v.
Proof.
intros; elim (R.dec_total (plug t (compose c c0))); intros.
inversion_clear H0. apply L.dec_plug in H1; rewrite L.compose_empty in H1.
eapply decSamPam in H.
Focus 2.
apply L.dec_plug_rev; eauto.
apply decPamSam with x; auto.
apply iterPamSam; auto.
Qed.

Lemma dec_plug_rev : forall c c0 t v, dec t (compose c c0) v-> dec (plug t c) c0 v.
Proof.
intros; elim (R.dec_total (plug (plug t c) c0)); intros; inversion_clear H0; apply L.dec_plug in H1; rewrite L.compose_empty in H1.
eapply decSamPam in H.
Focus 2.
apply L.dec_plug; eauto.
apply decPamSam with x; auto.
apply iterPamSam; auto.
Qed.

End StagedAbstractMachine.

Module EvalApplyMachine (L : RED_LANG).

Module SAM := StagedAbstractMachine (L).
Module R := SAM.R.
Definition term := R.term.
Definition closure := R.closure.
Definition value := R.value.
Definition redex := R.redex.
Definition context := R.context.
Definition empty := R.empty.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.

Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.
Definition pairC := R.pairC.

Definition dec_term := R.dec_term.
Definition dec_context := R.dec_context.

Definition decomp := SAM.decomp.
Definition d_val := SAM.d_val.
Definition d_red := SAM.d_red.

Definition interm_dec := SAM.interm_dec.
Definition in_dec := SAM.in_dec.
Definition in_val := SAM.in_val.
Definition in_term:= SAM.in_term.

Inductive dec : closure -> context -> value -> Prop :=
| d_o_val: forall (t : closure) (c : context) (v : value),
             dec_term t c = in_dec (d_val v) -> dec t c v
| d_o_red: forall (t t0 : closure) (c c0 c1 : context) (r : redex) (v : value),
             dec_term t c = in_dec (d_red r c0) -> contract r c0 = Some (t0, c1) -> dec t0 c1 v -> dec t c v
| d_ctx  : forall (t : closure) (c c0 : context) (v v0 : value),
             dec_term t c = in_val v c0 -> decctx v c0 v0 -> dec t c v0
| d_many : forall (t t0 : closure) (c c0 : context) (v : value),
             dec_term t c = in_term t0 c0 -> dec t0 c0 v -> dec t c v
with decctx : value -> context -> value -> Prop :=
| dc_val : forall (v v0 : value) (c : context),
             dec_context v c = in_dec (d_val v0) -> decctx v c v0
| dc_red : forall (v v0 : value) (c c0 c1 : context) (r : redex) (t : closure),
             dec_context v c = in_dec (d_red r c0) -> contract r c0 = Some (t, c1) -> dec t c1 v0 -> decctx v c v0
| dc_ctx : forall (v v0 v1 : value) (c c0 : context),
             dec_context v c = in_val v0 c0 -> decctx v0 c0 v1 -> decctx v c v1
| dc_trm : forall (v v0 : value) (c c0 : context) (t : closure),
             dec_context v c = in_term t c0 -> dec t c0 v0 -> decctx v c v0.

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

Inductive eval : term -> value -> Prop :=
| e_intro : forall (t : term) (v : value), dec (pairC t nil) empty v -> eval t v.

Lemma decSamEam : forall (t : closure) (c : context) (v : value), SAM.dec t c v -> dec t c v.
Proof.
induction 1 using SAM.dec_Ind with
(P := fun t c v (H:SAM.dec t c v) => dec t c v)
(P0:= fun c v v' (H:SAM.decctx c v v') => decctx c v v')
(P1:= fun d v (H:SAM.iter d v) => match d with
                                 | d_val v' => decctx v empty v'
                                 | d_red r c => forall (t : closure) (c0:context), contract r c = Some (t, c0) -> dec t c0 v
                               end); simpl; intros.
(* Case 1 *)
induction d; simpl.
(* Case 1.1 *)
inversion i; subst; constructor 1; auto.
(* Case 1.2 *)
inversion i; subst; constructor 2 with t0 c0 c2 r; auto.
(* Case 2 *)
constructor 3 with c0 v; auto.
(* Case 3 *)
constructor 4 with t0 c0; auto.
(* Case 4 *)
induction d; simpl.
(* Case 4.1 *)
inversion i; subst; constructor 1; auto.
(* Case 4.2 *)
inversion_clear i; constructor 2 with c0 c2 r t; try apply IHdec; auto.
(* Case 5 *)
constructor 3 with v0 c0; auto.
(* Case 6 *)
constructor 4 with c0 t; auto.
(* Case 7 *)
constructor 1; apply L.dec_context_empty.
(* Case 8 *)
change (SAM.contract r c = Some (t0, c1)) in H0; rewrite e in H0; injection e; intros; subst; injection H0; intros; subst; auto.
Qed.

Lemma evalSamEam : forall (t : term) (v : value), SAM.eval t v -> eval t v.
Proof.
intros t v H; inversion_clear H; constructor; apply decSamEam; auto.
Qed.

Lemma decEamSam : forall (t : closure) (c : context) (v : value), dec t c v -> SAM.dec t c v.
Proof.
induction 1 using dec_Ind with
(P := fun t c v (H:dec t c v) => SAM.dec t c v)
(P0:= fun v c v' (H:decctx v c v') => SAM.decctx v c v'); intros; simpl.
constructor 1 with (d_val v); try constructor; auto.
constructor 1 with (d_red r c0); try constructor 2 with c1 t0; auto.
constructor 2 with c0 v; auto.
constructor 3 with t0 c0; auto.
constructor 1 with (d_val v0); try constructor; auto.
constructor 1 with (d_red r c0); auto; constructor 2 with c1 t; auto.
constructor 2 with v0 c0; auto.
constructor 3 with t c0; auto.
Qed.

Lemma evalEamSam : forall (t : term) (v : value), eval t v -> SAM.eval t v.
Proof.
intros t v H; inversion_clear H; constructor; apply decEamSam; auto.
Qed.

Theorem evalEam : forall (t : term) (v : value), R.eval t v <-> eval t v.
Proof.
split; intro H; assert (hh := SAM.evalSam t v); elim hh; intros;
[ apply evalSamEam; apply H0 | apply H1; apply evalEamSam ]; auto.
Qed.

Lemma dec_plug : forall c c0 t v, dec (plug t c) c0 v -> dec t (compose c c0) v.
Proof.
intros; apply decEamSam in H; apply SAM.dec_plug in H; apply decSamEam; auto.
Qed.

Lemma dec_plug_rev : forall c c0 t v, dec t (compose c c0) v-> dec (plug t c) c0 v.
Proof.
intros; apply decEamSam in H; apply SAM.dec_plug_rev in H; apply decSamEam; auto.
Qed.

End EvalApplyMachine.

Module UnfoldedEAMachine (R : RED_LANG).

Module EAM := EvalApplyMachine (R).
Module E := EAM.R.
Definition term := R.term.
Definition closure := R.closure.
Definition value := R.value.
Definition redex := R.redex.
Definition empty := R.empty.
Definition context := R.context.
Definition pairC := R.pairC.
Definition emptyC := R.emptyC.
Definition closureC := R.closureC.
Definition valueC := R.valueC.
Definition contextC := R.contextC.
Definition substC := R.substitutionC.
Definition closureC_to_closure (cl : closureC) : closure := R.closureC_to_closure cl.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.
Definition contextC_to_context (c : contextC) : context := R.contextC_to_context c.
Definition composeC (c c0 : contextC) : contextC := R.composeC c c0.
Definition valueC_to_value (v:valueC) : value := R.valueC_to_value v.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.
Coercion closureC_to_closure : closureC >-> closure.
Coercion contextC_to_context : contextC >-> context.
Coercion valueC_to_value : valueC >-> value.

Definition decomp:= EAM.decomp.
Definition d_val := EAM.d_val.
Definition d_red := EAM.d_red.

Definition interm_dec := R.interm_dec.
Definition in_dec := R.in_dec.
Definition in_val := R.in_val.
Definition in_term:= R.in_term.

Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.

Definition dec_term := R.dec_term.
Definition dec_context := R.dec_context.

Definition unf_c_red (v : valueC) (ct : contextC) (r : redex) (ct0 ct1: context) (cl : closure)
  (H : dec_context (valueC_to_value v) ct = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl, ct1)) : (term * substC * contextC)+(valueC * contextC).
Proof.
intros.
assert (hi := R.unfold_c_red _ _ _ _ _ _ H H1).
destruct hi as [p hi]; apply p.
Defined.

Lemma unf_c_red_correct : forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) ct = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl, ct1)), R.dec_by_cls cl ct1 (unf_c_red v ct r ct0 ct1 cl H H1).
Proof with auto.
intros.
unfold unf_c_red; simpl in *.
remember (R.unfold_c_red v ct r ct0 ct1 cl H H1).
destruct s as [p q]...
Qed.

Definition unf_c_cls (v : valueC) (ct : contextC) (ct0 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) ct = in_term cl ct0) : (term * substC * contextC)+(valueC * contextC).
Proof.
intros.
assert (hi := R.unfold_c_cls _ _ _ _ H).
destruct hi as [p hi]; apply p.
Defined.

Lemma unf_c_cls_correct : forall (v : valueC) (ct : contextC) (ct0 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) ct = in_term cl ct0), R.dec_by_cls cl ct0 (unf_c_cls v ct ct0 cl H).
Proof with auto.
intros.
unfold unf_c_cls; simpl in *.
remember (R.unfold_c_cls v ct cl ct0 H).
destruct s as [p q]...
Qed.

Definition unf_red (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure)
  (H : dec_term cl ct = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl0, ct1)) : (term * substC * contextC)+(valueC * contextC).
Proof.
intros.
assert (hi := R.unfold_red _ _ _ _ _ _ H H1).
destruct hi as [p hi]; apply p.
Defined.

Lemma unf_red_correct : forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure)
  (H : dec_term cl ct = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl0, ct1)), R.dec_by_cls cl0 ct1 (unf_red cl ct r ct0 ct1 cl0 H H1).
Proof with auto.
intros.
unfold unf_red; simpl in *.
remember (R.unfold_red cl ct r ct0 ct1 cl0 H H1).
destruct s as [p q]...
Qed.

Definition unf_cls (cl : closureC) (ct : contextC) (ct0 : context) (cl0 : closure)
  (H : dec_term cl ct = in_term cl0 ct0) : (term * substC * contextC)+(valueC * contextC).
Proof.
intros.
assert (hi := R.unfold_cls _ _ _ _ H).
destruct hi as [p hi]; apply p.
Defined.

Lemma unf_cls_correct : forall (cl : closureC) (ct : contextC) (ct0 : context) (cl0 : closure)
  (H : dec_term cl ct = in_term cl0 ct0), R.dec_by_cls cl0 ct0 (unf_cls cl ct ct0 cl0 H). 
Proof with auto.
intros.
unfold unf_cls in *; simpl in *.
remember (R.unfold_cls cl ct cl0 ct0 H).
destruct s as [r q]...
Qed.

Inductive dec : term -> substC -> contextC -> valueC -> Prop :=
| d_o_val : forall (t : term) (s : substC) (c : contextC) (v : valueC),
              dec_term (closureC_to_closure (pairC t s)) (c:context) = in_dec (d_val (v:value)) -> dec t s c v
| d_red_t : forall (t t0 : term) (s s0 : substC) (c c2 : contextC) (c0 c1: context) (v : valueC) (cl : closure) (r : redex)
              (H : dec_term ((pairC t s):closure) (c:context) = in_dec (d_red r c0)) (H1 : contract r c0 = Some (cl, c1)),
              unf_red (pairC t s) c r c0 c1 cl H H1 = inl _ (t0, s0, c2) -> dec t0 s0 c2 v -> dec t s c v
| d_red_v : forall (t : term) (s : substC) (c c2 : contextC) (c0 c1 : context) (v v0 : valueC) (cl : closure) (r : redex)
              (H : dec_term (pairC t s:closure) (c:context) = in_dec (d_red r c0)) (H1 : contract r c0 = Some (cl, c1)),
              unf_red (pairC t s) c r c0 c1 cl H H1 = inr _ (v0, c2) -> decctx c2 v0 v -> dec t s c v
| d_ctx   : forall (t : term) (s : substC) (c c0 : contextC) (v v0 : valueC),
              dec_term (closureC_to_closure (pairC t s)) (c:context) = in_val (v0:value) (c0:context) -> decctx c0 v0 v -> dec t s c v
| d_term_t: forall (t t0 : term) (s s0 : substC) (c c1 : contextC) (c0 : context) (cl : closure) (v : valueC)
              (H : dec_term ((pairC t s):closure) (c:context) = in_term cl (c0:context)),
              unf_cls (pairC t s) c c0 cl H = inl _ (t0, s0, c1) -> dec t0 s0 c1 v -> dec t s c v
| d_term_v: forall (t : term) (s : substC) (c c1 : contextC) (c0 : context) (cl : closure) (v v0 : valueC)
              (H : dec_term ((pairC t s):closure) (c:context) = in_term cl (c0:context)),
              unf_cls (pairC t s) c c0 cl H = inr _ (v0, c1) -> decctx c1 v0 v -> dec t s c v
with decctx : contextC -> valueC -> valueC -> Prop :=
| dc_val  : forall (c : contextC) (v v0 : valueC), dec_context (v:value) (c:context) = in_dec (d_val (v0:value)) -> decctx c v v0
| dc_red_t: forall (t : term) (s : substC) (c c2 : contextC) (c0 c1 : context) (v v0 : valueC) (cl : closure) (r : redex)
              (H : dec_context (v:value) (c:context) = in_dec (d_red r (c0:context))) (H1 : contract r c0 = Some (cl, c1)),
              unf_c_red v c r c0 c1 cl H H1 = inl _ (t, s, c2) -> dec t s c2 v0 -> decctx c v v0
| dc_red_v: forall (v v0 v1 : valueC) (c c2 : contextC) (c0 c1 : context) (cl : closure) (r : redex)
              (H : dec_context (v:value) (c:context) = in_dec (d_red r (c0:context))) (H1 : contract r c0 = Some (cl, c1)),
              unf_c_red v c r c0 c1 cl H H1 = inr _ (v0, c2) -> decctx c2 v0 v1 -> decctx c v v1
| dc_ctx  : forall (c c0 : contextC) (v v0 v1 : valueC),
              dec_context (v:value) (c:context) = in_val (v0:value) (c0:context) -> decctx c0 v0 v1 -> decctx c v v1
| dc_t_t : forall (t : term) (s : substC) (c c1 : contextC) (c0 : context) (v v0 : valueC) (cl : closure)
              (H : dec_context (v:value) (c:context) = in_term cl (c0:context)),
              unf_c_cls v c c0 cl H = inl _ (t, s, c1) -> dec t s c1 v0 -> decctx c v v0
| dc_t_v  : forall (c c1 : contextC) (c0 : context) (v v0 v1 : valueC) (cl : closure)
              (H : dec_context (v:value) (c:context) = in_term cl c0),
              unf_c_cls v c c0 cl H = inr _ (v1, c1) -> decctx c1 v1 v0 -> decctx c v v0.

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

Inductive eval : term -> valueC -> Prop :=
| e_intro : forall (t : term) (v : valueC), dec t nil emptyC v -> eval t v.

Lemma decEamUnw : forall t s v (ct:contextC), EAM.dec ((pairC t s):EAM.closure) (ct:context) (valueC_to_value v) -> dec t s ct v.
Proof with auto.
intros.
assert (((pairC t s):closure) = R.recons (t,s,emptyC))...
unfold R.recons.
change (((pairC t s):closure) = R.plug ((R.pairC t s):R.closure) (R.contextC_to_context R.emptyC)).
rewrite R.emptyC_empty; rewrite R.plug_empty...
remember H as H1; clear HeqH1.
change (EAM.dec ((pairC t s):EAM.closure) (R.contextC_to_context ct) (valueC_to_value v)) in H1.
rewrite <- R.empty_compose with (c := ct) in H1.
rewrite <- R.emptyC_empty in H1.
rewrite <- R.composeC_compose in H1.
rewrite <- R.empty_composeC with ct.
assert (ht := E.dec_total (plug (pairC t s:closure) (ct:context))); destruct ht as [d ht].
inversion_clear ht.
apply R.dec_plug in H2; rewrite R.compose_empty in H2.
remember H2; clear Heqd0; rewrite <- R.empty_composeC with ct in d0.
assert (R.dec_by_cls (pairC t s:closure) (ct:context) (inl _ (t, s, ct))); try (constructor; fail).
rewrite R.empty_composeC.
refine (EAM.dec_Ind
(fun cl c v (H:EAM.dec cl c v) => forall p, R.dec_by_cls cl c p ->
  match p with
    | inl (t, s, ct) => forall (v0 : valueC), (valueC_to_value v0) = v -> dec t s ct v0
    | inr (v0, ct) => forall (v1 : valueC), (valueC_to_value v1) = v -> decctx ct v0 v1
  end)
(fun v c v0 (H:EAM.decctx v c v0) => forall (ct:contextC) (v1 v2 : valueC), valueC_to_value v1 = v -> valueC_to_value v2 = v0 -> c = (ct:context) -> decctx ct v1 v2)
_ _ _ _ _ _ _ _ (closureC_to_closure (pairC t s)) (ct:context) (valueC_to_value v) H (inl _ (t, s, ct)) H3 v _); intros; simpl...
(* Case 1 (d_val) *)
inversion H4; intros; subst.
constructor...
change (R.dec_term (R.closureC_to_closure (R.valueC_to_closureC v1)) c0 = in_dec (d_val v2)) in e.
rewrite R.commutes in e.

rewrite R.dec_term_value in e; discriminate.
change (R.dec_term t0 c = in_dec (d_val (v0:value))) in e; rewrite H5 in e; discriminate.
(* Case 2 (d_red) *)
subst; change (R.dec_term t0 c = in_dec (d_red r c0)) in e.
inversion H5; subst...
assert (unf_red _ _ _ _ _ _ e e0 = unf_red _ _ _ _ _ _ e e0)...
destruct unf_red  in H6 at 2 .
destruct p as [[tt ss] cc].
constructor 2 with tt ss cc c0 c1 t1 r e e0...
assert (ht := unf_red_correct _ _ _ _ _ _ e e0); rewrite <- H6 in ht.
assert (ho := H4 (inl _ (tt, ss, cc))); simpl in ho.
apply ho...
destruct p as [vv cc]; intros; subst v0.
econstructor 3; eauto.
assert (ht := unf_red_correct _ _ _ _ _ _ e e0); rewrite <- H6 in ht.
assert (ho := H4 (inr _ (vv, cc))); simpl in ho.
apply ho...
assert (ht := R.dec_term_value v1 c2).
rewrite R.commutes in e.
rewrite ht in e; discriminate.
rewrite H6 in e; discriminate.
(* Case 3 (in_val) *)
change (R.dec_term t0 c = in_val v0 c0) in e.
subst; destruct p.
destruct p as [[tt ss] cc]; intros; subst v1.
inversion H5; subst.
assert (ht := R.dec_Val _ _ _ _ _ e); destruct ht as [vv [cc1 [ht ho]]]; subst.
constructor 4 with cc1 vv...
rewrite H6 in e; discriminate.
destruct p as [vv cc]; intros; subst v1.
inversion H5; subst.
assert (ht := R.dec_term_value vv cc).
rewrite R.commutes in e.
rewrite ht in e.
inversion e; subst...
rewrite H6 in e; discriminate.
(* Case 4 (in_term) *)
subst; change (R.dec_term t0 c = in_term t1 c0) in e.
inversion H5; subst.
assert (unf_cls _ _ _ _ e = unf_cls _ _ _ _ e)...
assert (ht := unf_cls_correct _ _ _ _ e).
destruct unf_cls in H6 at 2.
destruct p as [[tt ss] cc]; intros; subst v0.
econstructor 5; eauto.
rewrite <- H6 in ht.
apply (H4 (inl _ (tt, ss, cc)))...
destruct p as [vv cc]; intros; subst v0.
econstructor 6; eauto.
rewrite <- H6 in ht.
apply (H4 (inr _ (vv, cc)))...
assert (ht := R.dec_term_value v1 c1); rewrite R.commutes in e; rewrite ht in e; discriminate.
rewrite H6 in e; inversion e; subst.
apply H4...
(* Case 5 *)
subst; constructor...
(* Case 6 *)
subst; assert (unf_c_red _ _ _ _ _ _ e e0 = unf_c_red _ _ _ _ _ _ e e0)...
assert (ht := unf_c_red_correct _ _ _ _ _ _ e e0).
destruct unf_c_red in H5 at 2.
destruct p as [[tt ss] cc].
econstructor 2; eauto.
rewrite <- H5 in ht.
apply (H4 (inl _ (tt, ss, cc)))...
destruct p as [vv cc].
econstructor 3; eauto.
rewrite <- H5 in ht.
apply (H4 (inr _ (vv, cc)))...
(* Case 7 *)
subst.
assert (ho := R.dec_c_Val _ _ _ _ e); destruct ho as [ct1 [v2 [ho hp]]]; subst.
econstructor 4; eauto.
(* Case 8 *)
subst; assert (unf_c_cls _ _ _ _ e = unf_c_cls _ _ _ _ e)...
assert (ht := unf_c_cls_correct _ _ _ _ e).
destruct unf_c_cls in H5 at 2.
destruct p as [[tt ss] cc].
econstructor 5; eauto.
rewrite <- H5 in ht; subst.
apply (H4 (inl _ (tt, ss, cc)))...
destruct p as [vv cc].
econstructor 6; eauto.
rewrite <- H5 in ht; subst.
apply (H4 (inr _ (vv, cc)))...
Qed.

Lemma evalEamUnf : forall t v, EAM.eval t (valueC_to_value v) -> eval t v.
Proof with auto.
intros t v H; inversion_clear H; constructor; apply decEamUnw...
change (EAM.dec (closureC_to_closure (pairC t nil)) (R.contextC_to_context R.emptyC) (valueC_to_value v)); rewrite R.emptyC_empty...
Qed.

Lemma decUnfEam : forall t s ct v, dec t s ct v -> EAM.dec (closureC_to_closure (pairC t s)) (ct:context) (valueC_to_value v).
Proof with auto.
induction 1 using dec_Ind with
(P := fun t s ct v (H:dec t s ct v) => EAM.dec (closureC_to_closure (pairC t s)) (ct:context) (valueC_to_value v))
(P0:= fun ct v v0 (H:decctx ct v v0) => EAM.decctx (valueC_to_value v) (ct:context) (valueC_to_value v0))...
(* Case 1 *)
constructor 1...
(* Case 2 *)
assert (ht := unf_red_correct _ _ _ _ _ _ H H1).
rewrite e in ht.
econstructor 2; eauto.
assert (hr := R.dec_by_cls_folds_left _ _ _ _ _ ht).
rewrite <- R.compose_empty with c1.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c1) R.empty (v:value)).
rewrite hr.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
(* Case 3 *)
assert (ht := unf_red_correct _ _ _ _ _ _ H H1).
rewrite e in ht.
econstructor 2; eauto.
assert (hr := R.dec_by_cls_folds_right _ _ _ _ ht).
rewrite <- R.compose_empty with c1.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c1) R.empty (v:value)).
rewrite hr.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
constructor 3 with c2 v0...
rewrite R.commutes.
apply R.dec_term_value.
(* Case 4 *)
constructor 3 with (c0:context) (valueC_to_value v0)...
(* Case 5 *)
constructor 4 with cl (c0:context)...
assert (ht := unf_cls_correct _ _ _ _ H).
rewrite e in ht.
assert (hq := R.dec_by_cls_folds_left _ _ _ _ _ ht).
rewrite <- R.compose_empty with c0.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c0) R.empty (v:value)); rewrite hq.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
(* Case 6 *)
constructor 4 with cl (c0:context)...
assert (ht := unf_cls_correct _ _ _ _ H).
rewrite e in ht.
assert (hq := R.dec_by_cls_folds_right _ _ _ _ ht).
rewrite <- R.compose_empty with c0.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c0) R.empty (v:value)); rewrite hq.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
constructor 3 with c1 v0...
rewrite R.commutes.
apply R.dec_term_value.
(* Case 7 *)
constructor...
(* Case 8 *)
constructor 2 with c0 c1 r cl...
assert (ht := unf_c_red_correct _ _ _ _ _ _ H H1).
rewrite e in ht.
assert (hq := R.dec_by_cls_folds_left _ _ _ _ _ ht).
rewrite <- R.compose_empty with c1.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c1) R.empty (v0:value)); rewrite hq.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
(* Case 9 *)
constructor 2 with c0 c1 r cl...
assert (ht := unf_c_red_correct _ _ _ _ _ _ H H1).
rewrite e in ht.
assert (hq := R.dec_by_cls_folds_right _ _ _ _ ht).
rewrite <- R.compose_empty with c1.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c1) R.empty (v1:value)); rewrite hq.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
constructor 3 with c2 v0...
rewrite R.commutes.
apply R.dec_term_value.
(* Case 10 *)
constructor 3 with (v0:value) (c0:context)...
(* Case 11 *)
constructor 4 with c0 cl...
assert (ht := unf_c_cls_correct _ _ _ _ H).
rewrite e in ht.
assert (hq := R.dec_by_cls_folds_left _ _ _ _ _ ht).
rewrite <- R.compose_empty with c0.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c0) R.empty (v0:value)); rewrite hq.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
(* Case 12 *)
constructor 4 with c0 cl...
assert (ht := unf_c_cls_correct _ _ _ _ H).
rewrite e in ht.
assert (hq := R.dec_by_cls_folds_right _ _ _ _ ht).
rewrite <- R.compose_empty with c0.
apply EAM.dec_plug.
change (EAM.dec (R.plug cl c0) R.empty (v0:value)); rewrite hq.
apply EAM.dec_plug_rev; rewrite R.compose_empty...
constructor 3 with c1 v1...
rewrite R.commutes.
apply R.dec_term_value.
Qed.

Lemma evalUnfEam : forall t v, eval t v -> EAM.eval t (valueC_to_value v).
Proof with auto.
intros t v H; inversion_clear H; constructor...
change (EAM.dec (closureC_to_closure (pairC t nil)) (R.empty) (v:value)); rewrite <- R.emptyC_empty;
apply decUnfEam...
Qed.

Theorem unfolded_machine_correct : forall t (v:valueC), E.eval t (v:value) <-> eval t v.
Proof with auto.
split; intro H; assert (hh := EAM.evalEam t (v:value)); elim hh; intros;
[ apply evalEamUnf; apply H0 | apply H1; apply evalUnfEam ]...
Qed.

End UnfoldedEAMachine.

Module ProperEAMachine (R : RED_LANG).

Module UEAM := UnfoldedEAMachine (R).
Module E := UEAM.E.
Definition term := R.term.
Definition value := R.value.
Definition redex := R.redex.
Definition closure := R.closure.
Definition context := R.context.
Definition empty := R.empty.
Definition closureC := R.closureC.
Definition valueC := R.valueC.
Definition contextC := R.contextC.
Definition substC := R.substitutionC.
Definition emptyC := R.emptyC.
Definition pairC := R.pairC.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.
Definition closureC_to_closure (cl : closureC) : closure := R.closureC_to_closure cl.
Definition contextC_to_context (c : contextC) : context := R.contextC_to_context c.
Definition composeC (c c0 : contextC) : contextC := R.composeC c c0.
Definition valueC_to_value (v : valueC) : value := R.valueC_to_value v.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.
Coercion closureC_to_closure : closureC >-> closure.
Coercion contextC_to_context : contextC >-> context.
Coercion valueC_to_value : valueC >-> value.

Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.
 
Definition dec_term := R.dec_term.
Definition dec_context := R.dec_context.

Definition decomp := UEAM.decomp.
Definition d_val := UEAM.d_val.
Definition d_red := UEAM.d_red.

Definition interm_dec := R.interm_dec.
Definition in_dec := R.in_dec.
Definition in_val := R.in_val.
Definition in_term:= R.in_term.

Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> substC -> contextC -> configuration
  | c_apply : contextC -> valueC -> configuration
  | c_final : valueC -> configuration.

Definition unf_red := UEAM.unf_red.
Definition unf_cls := UEAM.unf_cls.
Definition unf_c_red := UEAM.unf_c_red.
Definition unf_c_cls := UEAM.unf_c_cls.

Inductive transition : configuration -> configuration -> Prop :=
| t_init : forall (t : term), transition (c_init t) (c_eval t nil emptyC)
| t_t_fin: forall (t : term) (s : substC) (c : contextC) (v : valueC),
             dec_term (closureC_to_closure (pairC t s)) (c:context) = in_dec (d_val (v:value)) ->
             transition (c_eval t s c) (c_final v)
| t_tr_t : forall (t t0 : term) (s s0 : substC) (c c2 : contextC) (c0 c1 : context) (r : redex) (cl : closure)
             (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_dec (d_red r (c0:context)))
             (H1 : contract r c0 = Some (cl, c1)), unf_red (pairC t s) c r c0 c1 cl H H1 = inl _ (t0, s0, c2) ->
             transition (c_eval t s c) (c_eval t0 s0 c2)
| t_tr_v : forall (t : term) (s : substC) (c c2 : contextC) (c0 c1 : context) (r : redex) (cl : closure) (v : valueC)
             (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_dec (d_red r (c0:context)))
             (H1 : contract r c0 = Some (cl, c1)), unf_red (pairC t s) c r c0 c1 cl H H1 = inr _ (v, c2) ->
             transition (c_eval t s c) (c_apply c2 v)
| t_val  : forall (t : term) (s : substC) (v : valueC) (c c0: contextC),
      	     dec_term (closureC_to_closure (pairC t s)) (c:context) = in_val (v:value) (c0:context) ->
             transition (c_eval t s c) (c_apply c0 v)
| t_rec_t: forall (t t0 : term) (s s0 : substC) (c c1: contextC) (c0 : context) (cl : closure)
      	     (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_term cl (c0:context)),
             unf_cls (pairC t s) c c0 cl H = inl _ (t0, s0, c1) -> transition (c_eval t s c) (c_eval t0 s0 c1)
| t_rec_v: forall (t : term) (s : substC) (c c1: contextC) (c0 : context) (cl : closure) (v : valueC)
      	     (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_term cl (c0:context)),
             unf_cls (pairC t s) c c0 cl H = inr _ (v, c1) -> transition (c_eval t s c) (c_apply c1 v)
| t_c_fin: forall (v v0 : valueC) (c : contextC),
      	     dec_context (v:value) (c:context) = in_dec (d_val (v0:value)) -> transition (c_apply c v) (c_final v0)
| t_cr_t : forall (v : valueC) (t : term) (s : substC) (c c2 : contextC) (c0 c1 : context) (r : redex) (cl : closure)
	     (H : dec_context (v:value) (c:context) = in_dec (d_red r (c0:context))) (H1 : contract r c0 = Some (cl, c1)),
             unf_c_red v c r c0 c1 cl H H1 = inl _ (t, s, c2) -> transition (c_apply c v) (c_eval t s c2)
| t_cr_v : forall (v : valueC) (c c2 : contextC) (c0 c1 : context) (r : redex) (cl : closure) (v0 : valueC)
	     (H : dec_context (v:value) (c:context) = in_dec (d_red r (c0:context))) (H1 : contract r c0 = Some (cl, c1)),
             unf_c_red v c r c0 c1 cl H H1 = inr _ (v0, c2) -> transition (c_apply c v) (c_apply c2 v0)
| t_ctx  : forall (v v0 : valueC) (c c0 : contextC),
             dec_context (v:value) (c:context) = in_val (v0:value) (c0:context) -> transition (c_apply c v) (c_apply c0 v0)
| t_term : forall (v : valueC) (t : term) (s : substC) (c c1 : contextC) (c0 : context) (cl : closure)
	     (H : dec_context (v:value) (c:context) = in_term cl (c0:context)),
             unf_c_cls v c c0 cl H = inl _ (t, s, c1) -> transition (c_apply c v) (c_eval t s c1)
| t_c_val: forall (v : valueC) (c c1 : contextC) (c0 : context) (cl : closure) (v0 : valueC)
	     (H : dec_context (v:value) (c:context) = in_term cl (c0:context)),
             unf_c_cls v c c0 cl H = inr _ (v0, c1) -> transition (c_apply c v) (c_apply c1 v0).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step : forall w w', transition w w' -> trans_close w w'
| multi_step : forall w w' w'', transition w w' -> trans_close w' w'' -> trans_close w w''.

Scheme trans_Ind := Induction for transition Sort Prop.
Scheme trans_close_Ind := Induction for trans_close Sort Prop.

Inductive eval : term -> valueC -> Prop :=
| e_intro : forall (t : term) (v : valueC), trans_close (c_init t) (c_final v) -> eval t v.

Lemma decEamTrans :
forall (t : term) (s : substC) (c : contextC) (v : valueC),
  UEAM.dec t s c v -> trans_close (c_eval t s c) (c_final v).
Proof with eauto.
induction 1 using UEAM.dec_Ind with
(P := fun t s c v (H:UEAM.dec t s c v) => trans_close (c_eval t s c) (c_final v))
(P0:= fun c v v' (H:UEAM.decctx c v v') => trans_close (c_apply c v) (c_final v'));
intros; simpl; try (constructor 1; constructor; auto; fail); econstructor 2; eauto;
[ econstructor 3 | econstructor 4  | constructor | econstructor 6  | econstructor 7
| econstructor 9 | econstructor 10 | constructor | econstructor 12 | econstructor 13]...
Qed.

Lemma evalEamMachine : forall (t : term) (v : valueC), UEAM.eval t v -> eval t v.
intros t v H; inversion_clear H; constructor; constructor 2 with (c_eval t nil emptyC); [constructor | apply decEamTrans]; auto.
Qed.

Lemma transDecEam : forall (t : term) (s : substC) (c : contextC) (v : valueC), trans_close (c_eval t s c) (c_final v) -> UEAM.dec t s c v.
Proof with eauto.
intros t s c v X.
refine (trans_close_ind
(fun c c0 =>
  match c, c0 with
    | c_eval t s c, c_final v => UEAM.dec t s c v
    | c_apply c v, c_final v0 => UEAM.decctx c v v0
    | _, _ => True
  end)
_ _ (c_eval t s c) (c_final v) X); intros; auto.
(* Case 1 *)
generalize H; clear H; case w; case w'; simpl; intros; try inversion t2; subst; auto;
inversion_clear H; constructor 1...
(* Case 2 *)
generalize H H0 H1; clear H H0 H1; case w; case w'; case w''; simpl; auto; intros; inversion H; subst.
econstructor 2...
econstructor 5...
econstructor 3...
econstructor 4...
econstructor 6...
inversion H0; subst; inversion H2.
econstructor 2...
econstructor 5...
econstructor 3...
econstructor 4...
econstructor 6...
inversion H0; subst; inversion H2.
Qed.

Lemma evalMachineEam : forall (t : term) (v : valueC), eval t v -> UEAM.eval t v.
Proof.
intros t v H; inversion_clear H; constructor; inversion_clear H0;
inversion H; subst; apply transDecEam; auto.
Qed.

Theorem evalMachine : forall (t : term) (v : valueC), E.eval t (v:value) <-> eval t v.
Proof.
split; intro H; assert (hh := UEAM.unfolded_machine_correct t v); elim hh; intros H0 H1;
[ apply evalEamMachine; apply H0 | apply H1; apply evalMachineEam ]; auto.
Qed.

End ProperEAMachine.

Module PushEnterMachine (R : RED_LANG).

Module UEAM := UnfoldedEAMachine (R).
Module E := UEAM.E.
Definition term := R.term.
Definition closure := R.closure.
Definition value := R.value.
Definition redex := R.redex.
Definition context := R.context.
Definition closureC := R.closureC.
Definition valueC := R.valueC.
Definition pairC := R.pairC.
Definition substC := R.substitutionC.
Definition contextC := R.contextC.
Definition emptyC := R.emptyC.
Definition empty := R.empty.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.
Definition closureC_to_closure (cl : closureC) : closure := R.closureC_to_closure cl.
Definition contextC_to_context (c : contextC) : context := R.contextC_to_context c.
Definition composeC (c c0 : contextC) : contextC := R.composeC c c0.
Definition valueC_to_value (v : valueC) : value := R.valueC_to_value v.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.
Coercion closureC_to_closure : closureC >-> closure.
Coercion contextC_to_context : contextC >-> context.
Coercion valueC_to_value : valueC >-> value.

Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.

Definition dec_term := R.dec_term.
Definition dec_context := R.dec_context.

Definition decomp := UEAM.decomp.
Definition d_val := UEAM.d_val.
Definition d_red := UEAM.d_red.

Definition interm_dec := R.interm_dec.
Definition in_dec := R.in_dec.
Definition in_val := R.in_val.
Definition in_term:= R.in_term.

Definition unf_red := UEAM.unf_red.
Definition unf_c_red := UEAM.unf_c_red.
Definition unf_cls := UEAM.unf_cls.
Definition unf_c_cls := UEAM.unf_c_cls.

Inductive dec : term -> substC -> contextC -> valueC -> Prop :=
| dec_tv : forall (t : term) (s : substC) (c : contextC) (v : valueC),
             dec_term (closureC_to_closure (pairC t s)) (c:context) = in_dec (d_val (v:value)) -> dec t s c v
| dec_tr : forall (t t0 : term) (s s0 : substC) (c c2 : contextC) (c0 c1 : context) (r : redex) (cl : closure) (v : valueC)
             (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_dec (d_red r (c0:context)))
             (H1 : contract r c0 = Some (cl, c1)), unf_red (pairC t s) c r c0 c1 cl H H1 = inl _ (t0, s0, c2) ->
             dec t0 s0 c2 v -> dec t s c v
| dec_cv : forall (t : term) (s : substC) (c c0 : contextC) (v v0 : valueC),
               dec_term (closureC_to_closure (pairC t s)) (c:context) = in_val (v:value) (c0:context) ->
               dec_context (v:value) (c0:context) = in_dec (d_val (v0:value)) -> dec t s c v0
| dec_red  : forall (t t0 : term) (s s0 : substC) (c c0 c3 : contextC) (c1 c2 : context) (v v0 : valueC) (r : redex) (cl : closure)
               (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_val (v:value) (c0:context))
               (H1 : dec_context (v:value) (c0:context) = in_dec (d_red r (c1:context))) (H2 : contract r c1 = Some (cl, c2)),
               unf_c_red v c0 r c1 c2 cl H1 H2 = inl _ (t0, s0, c3) -> dec t0 s0 c3 v0 -> dec t s c v0
| dec_cr   : forall (t t0 : term) (s s0 : substC) (c c0 c2 : contextC) (c1 : context) (cl : closure) (v v0 : valueC)
               (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_val (v:value) (c0:context))
               (H1 : dec_context (v:value) (c0:context) = in_term cl c1),
               unf_c_cls v c0 c1 cl H1 = inl _ (t0, s0, c2) -> dec t0 s0 c2 v0 -> dec t s c v0
| dec_rec  : forall (t t0 : term) (s s0 : substC) (c c1 : contextC) (c0 : context) (cl : closure) (v : valueC)
               (H : dec_term (closureC_to_closure (pairC t s)) (c:context) = in_term cl (c0:context)),
               unf_cls (pairC t s) c c0 cl H = inl _ (t0, s0, c1) -> dec t0 s0 c1 v -> dec t s c v.

Scheme dec_Ind := Induction for dec Sort Prop.

Inductive eval : term -> valueC -> Prop :=
| e_intro : forall (t : term) (v : valueC), dec t nil emptyC v -> eval t v.

Section Equivalence.

Variable dec_context_not_value :
  forall (v v0 : value) (c c0 : context), ~dec_context v c = in_val v0 c0.

Variable dec_by_cls_left_only :
  forall (cl : closure) (ct : context) (v : valueC) (ct0 : contextC), ~(R.dec_by_cls cl ct (inr _ (v, ct0))).

Lemma decEamPem : forall (t : term) (s : substC) (c : contextC) (v : valueC), UEAM.dec t s c v -> dec t s c v.
Proof with eauto.
induction 1 using UEAM.dec_Ind with
(P := fun t s c v (H:UEAM.dec t s c v) => dec t s c v)
(P0:= fun c v v0 (H:UEAM.decctx c v v0) => 
forall (d : interm_dec), dec_context (v:UEAM.value) (contextC_to_context c) = d ->
  match d with
    | in_dec (d_val v1) => forall t s, (v:UEAM.closure) = pairC t s -> v1 = (v0:UEAM.value) -> dec t s c v0
    | in_dec (d_red r c0) => forall cl c1 t s ct1 (H1 : dec_context (v:UEAM.value) (contextC_to_context c) = in_dec (d_red r c0)) (H2 : contract r c0 = Some (cl, c1)),
                    unf_c_red v c r c0 c1 cl H1 H2 = inl _ (t, s, ct1) -> dec t s ct1 v0
    | in_val _ _ => False
    | in_term cl c0 => forall t s ct1 (H1 : dec_context (v:UEAM.value) (contextC_to_context c) = in_term cl c0),
                    unf_c_cls v c c0 cl H1 = inl _ (t, s, ct1) -> dec t s ct1 v0
  end); intros; simpl.
(* Case 1 *)
constructor...
(* Case 2 *)
econstructor 2...
(* Case 3 *)
assert (ht := UEAM.unf_red_correct _ _ _ _ _ _ H H1); rewrite e in ht.
contradict (dec_by_cls_left_only _ _ _ _ ht).
(* Case 4 *)
inversion d; subst.
(* Case 4.1 *)
econstructor 3...
(* Case 4.2 *)
econstructor 4...
eapply (IHdec _ H)...
(* Case 4.3 *)
assert (ht := UEAM.unf_c_red_correct _ _ _ _ _ _ H H1); rewrite H0 in ht. 
contradict (dec_by_cls_left_only _ _ _ _ ht).
(* Case 4.4 *)
contradict (dec_context_not_value _ _ _ _ H).
(* Case 4.5 *)
econstructor 5...
eapply (IHdec _ H)...
(* Case 4.6 *)
assert (ht := UEAM.unf_c_cls_correct _ _ _ _ H); rewrite H0 in ht.
contradict (dec_by_cls_left_only _ _ _ _ ht).
(* Case 5 *)
econstructor 6...
(* Case 6 *)
assert (ht := UEAM.unf_cls_correct _ _ _ _ H); rewrite e in ht.
contradict (dec_by_cls_left_only _ _ _ _ ht).
(* Case 7 *)
change (UEAM.dec_context (v:UEAM.value) (c:UEAM.context) = d) in H; rewrite H in e; injection e;
intros; subst; simpl; econstructor 3...
cutrewrite <- (R.closureC_to_closure (pairC t s) = closureC_to_closure (pairC t s))...
rewrite <- H1; apply R.dec_term_value.
(* Case 8 *)
destruct d; simpl in *; intros; subst.
(* Case 8.1 *)
destruct d; simpl in *; intros; subst.
constructor 3 with c v...
cutrewrite <- (R.closureC_to_closure (pairC t0 s0) = closureC_to_closure (pairC t0 s0))...
rewrite <- H3; apply R.dec_term_value.
(* Case 8.2 *)
assert (ht := UEAM.unf_c_red_correct _ _ _ _ _ _ H3 H4);
unfold unf_c_red in H5; rewrite H5 in ht; clear H5.
assert (ho := UEAM.unf_c_red_correct _ _ _ _ _ _ H H1);
rewrite e in ho; clear e.
change(dec_context (v:UEAM.value) c = in_dec (d_red r c0)) in H;
change(dec_context (v:UEAM.value) c = in_dec (d_red r0 c3)) in H3; rewrite H in H3.
injection H3; intros; subst; clear H3.
unfold contract in H4; unfold UEAM.contract in H1.
rewrite H1 in H4; inversion H4; subst; clear H4.
injection (R.dec_by_cls_function _ _ _ _ ho ht);
intros; subst...
contradict (dec_context_not_value _ _ _ _ H2).
(* Case 8.3 *)
change (R.dec_context (v:R.value) (contextC_to_context c) = in_term c3 c4) in H3;
change (R.dec_context (v:R.value) (contextC_to_context c) = in_dec (d_red r c0)) in H;
clear e; rewrite H3 in H; discriminate.
(* Case 9 *)
assert (ho := UEAM.unf_c_red_correct _ _ _ _ _ _ H H1);
rewrite e in ho; clear e.
contradict (dec_by_cls_left_only _ _ _ _ ho).
(* Case 10 *)
contradict (dec_context_not_value _ _ _ _ e).
(* Case 11 *)
change (UEAM.dec_context (v:UEAM.value) (c:UEAM.context) = d) in H1; rewrite H in  H1; subst; simpl in *; intros.
assert (ht := UEAM.unf_c_cls_correct _ _ _ _ H).
assert (ho := UEAM.unf_c_cls_correct _ _ _ _ H1).
rewrite e in ht; unfold unf_c_cls in H2; rewrite H2 in ho; clear e H2.
injection (R.dec_by_cls_function _ _ _ _ ho ht); intros; subst...
(* Case 12 *)
assert (ht := UEAM.unf_c_cls_correct _ _ _ _ H); rewrite e in ht;
contradict (dec_by_cls_left_only _ _ _ _ ht).
Qed.

Lemma evalEamPem : forall (t : term) (v : valueC), UEAM.eval t v -> eval t v.
Proof.
intros t v H; inversion_clear H; constructor; apply decEamPem; auto.
Qed.
Hint Resolve evalEamPem.

Lemma decPemEam : forall (t : term) (s : substC) (c : contextC) (v : valueC), dec t s c v -> UEAM.dec t s c v.
Proof with eauto.
induction 1; intros; simpl...
constructor 1...
econstructor 2...
econstructor 4...
econstructor...
econstructor 4...
econstructor 2...
econstructor 4...
econstructor 5...
econstructor 5...
Qed.

Lemma evalPemEam : forall (t : term) (v : valueC), eval t v -> UEAM.eval t v.
Proof.
intros t v H; inversion_clear H; constructor; apply decPemEam; auto.
Qed.
Hint Resolve evalPemEam.

Theorem evalPem : forall (t : term) (v : valueC), E.eval t (v:value) <-> eval t v.
intros t v; destruct (UEAM.unfolded_machine_correct t v); split; auto.
Qed.

End Equivalence.

End PushEnterMachine.

Module ProperPEMachine (R : RED_LANG).

Module PEM := PushEnterMachine (R).
Module E := PEM.E.
Definition term := R.term.
Definition closure := R.closure.
Definition value := R.value.
Definition redex := R.redex.
Definition context := R.context.
Definition closureC := R.closureC.
Definition pairC := R.pairC.
Definition substC := R.substitutionC.
Definition contextC := R.contextC.
Definition emptyC := R.emptyC.
Definition empty := R.empty.
Definition valueC := R.valueC.
Definition value_to_closure (v : value) : closure := R.value_to_closure v.
Definition redex_to_closure (r : redex) : closure := R.redex_to_closure r.
Definition closureC_to_closure (cl : closureC) : closure := R.closureC_to_closure cl.
Definition contextC_to_context (c : contextC) : context := R.contextC_to_context c.
Definition composeC (c c0 : contextC) : contextC := R.composeC c c0.
Definition valueC_to_value (v : valueC) : value := R.valueC_to_value v.

Coercion value_to_closure : value >-> closure.
Coercion redex_to_closure : redex >-> closure.
Coercion closureC_to_closure : closureC >-> closure.
Coercion contextC_to_context : contextC >-> context.
Coercion valueC_to_value : valueC >-> value.

Definition plug := R.plug.
Definition compose := R.compose.
Definition contract := R.contract.

Definition dec_term := R.dec_term.
Definition dec_context := R.dec_context.

Definition decomp := PEM.decomp.
Definition d_val := PEM.d_val.
Definition d_red := PEM.d_red.

Definition interm_dec := R.interm_dec.
Definition in_dec := R.in_dec.
Definition in_val := R.in_val.
Definition in_term:= R.in_term.

Inductive configuration : Set :=
  | c_init  : term -> configuration 
  | c_eval  : term -> substC -> contextC -> configuration
  | c_final : valueC -> configuration.

Definition unf_red := PEM.unf_red.
Definition unf_c_red := PEM.unf_c_red.
Definition unf_cls := PEM.unf_cls.
Definition unf_c_cls := PEM.unf_c_cls.

Inductive transition : configuration -> configuration -> Prop :=
| t_init : forall (t : term), transition (c_init t) (c_eval t nil emptyC)
| t_t_val: forall (t : term) (s : substC) (c : contextC) (v : valueC),
             dec_term ((pairC t s):closure) c = in_dec (d_val (v:value)) -> transition (c_eval t s c) (c_final v)
| t_t_red: forall (t t0 : term) (s s0 : substC) (c c2 : contextC) (c0 c1 : context) (r : redex) (cl : closure)
             (H : dec_term ((pairC t s):closure) c = in_dec (d_red r c0)) (H1 : contract r c0 = Some (cl, c1)),
             unf_red (pairC t s) c r c0 c1 cl H H1 = inl _ (t0, s0, c2) -> transition (c_eval t s c) (c_eval t0 s0 c2)
| t_c_val: forall (t : term) (s : substC) (v v0 : valueC) (c c0 : contextC),
      	     dec_term ((pairC t s):closure) c = in_val (v:value) c0 -> dec_context (v:value) c0 = in_dec (d_val (v0:value)) ->
             transition (c_eval t s c) (c_final v0)
| t_red  : forall (t t0 : term) (s s0 : substC) (v : valueC) (c c0 c3 : contextC) (c1 c2 : context) (r : redex) (cl : closure)
             (H : dec_term ((pairC t s):closure) c = in_val (v:value) c0) (H1 : dec_context (v:value) c0 = in_dec (d_red r c1))
             (H2 : contract r c1 = Some (cl, c2)), unf_c_red v c0 r c1 c2 cl H1 H2 = inl _ (t0, s0, c3) ->
             transition (c_eval t s c) (c_eval t0 s0 c3)
| t_c_rec: forall (t t0 : term) (s s0 : substC) (v : valueC) (c c0 c2 : contextC) (c1 : context) (cl : closure)
             (H : dec_term ((pairC t s):closure) c = in_val (v:value) c0) (H1 : dec_context (v:value) c0 = in_term cl c1),
             unf_c_cls v c0 c1 cl H1 = inl _ (t0, s0, c2) -> transition (c_eval t s c) (c_eval t0 s0 c2)
| t_rec  : forall (t t0 : term) (s s0 : substC) (c c1 : contextC) (c0 : context) (cl : closure)
      	     (H : dec_term ((pairC t s):closure) c = in_term cl c0),
             unf_cls (pairC t s) c c0 cl H = inl _ (t0, s0, c1) -> transition (c_eval t s c) (c_eval t0 s0 c1).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step : forall w w', transition w w' -> trans_close w w'
| multi_step : forall w w' w'', transition w w' -> trans_close w' w'' -> trans_close w w''.

Scheme trans_Ind := Induction for transition Sort Prop.
Scheme trans_close_Ind := Induction for trans_close Sort Prop.

Inductive eval : term -> valueC -> Prop :=
| e_intro : forall (t : term) (v : valueC), trans_close (c_init t) (c_final v) -> eval t v.

Section Equivalence.

Variable dec_context_not_value : 
  forall (v v0 : value) (c c0 : context), ~dec_context v c = in_val v0 c0.

Variable dec_by_cls_left_only :
  forall (cl : closure) (ct : context) (v : valueC) (ct0 : contextC), ~(R.dec_by_cls cl ct (inr _ (v, ct0))).

Lemma decPemTrans : forall (t : term) (s : substC) (c : contextC) (v : valueC), PEM.dec t s c v -> trans_close (c_eval t s c) (c_final v).
Proof with eauto.
induction 1; intros; simpl...
repeat constructor...
econstructor 2...
econstructor 3...
constructor; econstructor 4...
econstructor 2...
econstructor 5...
econstructor 2...
econstructor 6...
econstructor 2...
econstructor 7...
Qed.

Lemma evalPemMachine : forall (t : term) (v : valueC), PEM.eval t v -> eval t v.
Proof.
intros t v H; inversion_clear H; constructor; constructor 2 with (c_eval t nil emptyC);
[ constructor 1 | apply decPemTrans]; auto.
Qed.
Hint Resolve evalPemMachine.

Lemma transDecPem : forall (t : term) (s : substC) (c : contextC) (v : valueC), trans_close (c_eval t s c) (c_final v) -> PEM.dec t s c v.
Proof with eauto.
intros t s c v X; refine (trans_close_ind
(fun c c0 => match c, c0 with
  | c_eval t s c, c_final v => PEM.dec t s c v
  | _, _ => True
end) _ _ (c_eval t s c) (c_final v) X); intros...
generalize H; clear H; case w; case w'; simpl; intros; try inversion t2; subst; auto; inversion_clear H; [ constructor 1 | econstructor 3 ]...
generalize H H0 H1; clear H H0 H1; case w; case w'; case w''; simpl; auto; intros; inversion H; subst...
econstructor 2...
econstructor 4...
econstructor 5...
econstructor 6...
inversion H0; subst; inversion H2.
inversion H0; subst; inversion H2.
Qed.

Lemma evalMachinePem : forall (t : term) (v : valueC), eval t v -> PEM.eval t v.
Proof.
intros t v H; constructor; inversion_clear H; inversion H0; subst; inversion H; subst;
apply transDecPem; auto.
Qed.
Hint Resolve evalMachinePem.

Theorem evalMachine : forall (t : term) (v : valueC), E.eval t (v:value) <-> eval t v.
Proof.
split; intro H; destruct (PEM.evalPem dec_context_not_value dec_by_cls_left_only t v); auto.
Qed.

End Equivalence.

End ProperPEMachine.