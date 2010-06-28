Require Import refocusing_environments_cs.
Require Import Setoid.

Module CallByValue <: RED_LANG.

Inductive term' : Set :=
| var : nat -> term'
| lam : nat -> term' -> term'
| appl : term' -> term' -> term'.
Definition term := term'.

Inductive closure' : Set :=
| pair' : term -> list closure' -> closure'
| comp  : closure' ->  closure' -> closure'.

Definition closure := closure'.
Definition substitution := list closure.
Definition pair : term -> substitution -> closure := pair'.

Inductive value' : Set :=
| v_lam : nat -> term -> substitution -> value'.
Definition value := value'.

Inductive context' : Set :=
| mt   : context'
| ap_r : value -> context' -> context'
| ap_l : closure -> context' -> context'.

Definition context := context'.
Definition empty : context := mt.

Inductive redex' : Set :=
| r_beta : value -> value -> redex'
| r_get  : nat -> substitution -> redex'
| r_app  : term -> term -> substitution -> redex'.
Definition redex := redex'.

Inductive closureC' : Set :=
| pairC' : term -> list closureC' -> closureC'.
Definition closureC := closureC'.
Definition substitutionC := list closureC.
Definition pairC : term -> substitutionC -> closureC := pairC'.

Inductive valueC' : Set :=
| v_lamC : nat -> term -> substitutionC -> valueC'.
Definition valueC := valueC'.

Inductive contextC' : Set :=
| mtC   : contextC'
| ap_rC : valueC -> contextC' -> contextC'
| ap_lC : closureC -> contextC' -> contextC'.

Definition contextC := contextC'.
Definition emptyC : contextC := mtC.

Inductive redexC' : Set :=
| r_betaC : valueC -> valueC -> redexC'.
Definition redexC := redexC'.

Definition value_to_closure (v : value) : closure :=
match v with
| v_lam n t s => pair (lam n t) s
end.
Coercion value_to_closure : value >-> closure.

Definition redex_to_closure (r : redex) : closure :=
match r with
| r_beta v v0 => comp (value_to_closure v) (value_to_closure v0)
| r_get n s => pair (var n) s
| r_app t t0 s => pair (appl t t0) s
end.
Coercion redex_to_closure : redex >-> closure.

Fixpoint closureC_to_closure (cl : closureC) : closure :=
match cl with
| pairC t s => pair t (map closureC_to_closure s)
end.
Coercion closureC_to_closure : closureC >-> closure.
Definition subC_to_sub : substitutionC -> substitution := map closureC_to_closure.
Coercion subC_to_sub : substitutionC >-> substitution.

Definition valueC_to_value (v : valueC) : value :=
match v with
| v_lamC n t s => v_lam n t (subC_to_sub s)
end.

Fixpoint contextC_to_context (ct : contextC) : context :=
match ct with
| mtC => mt
| ap_rC v ctc => ap_r (valueC_to_value v) (contextC_to_context ctc)
| ap_lC cl ct' => ap_l (cl : closure) (contextC_to_context ct')
end.
Coercion contextC_to_context : contextC >-> context.

Definition redexC_to_redex (r : redexC) : redex :=
match r with
| r_betaC v v' => r_beta (valueC_to_value v) (valueC_to_value v')
end.

Definition valueC_to_closureC (v : valueC) : closureC :=
match v with
| v_lamC n t s => pairC (lam n t) s
end.
Coercion valueC_to_closureC : valueC >-> closureC.

Fixpoint plug (cl : closure) (ct : context) {struct ct} : closure :=
match ct with
| empty => cl
| ap_r v ct0 => plug (comp cl (v:closure)) ct0
| ap_l cl0 ct0 => plug (comp cl0 cl) ct0
end.

Fixpoint compose (ct : context) (ct0 : context) {struct ct} : context :=
match ct with
| empty => ct0
| ap_r v ct' => ap_r v (compose ct' ct0)
| ap_l cl ct' => ap_l cl (compose ct' ct0)
end.

Fixpoint composeC (ct : contextC) (ct0 : contextC) {struct ct} : contextC :=
match ct with
| emptyC => ct0
| ap_rC v ct' => ap_rC v (composeC ct' ct0)
| ap_lC cl ct' => ap_lC cl (composeC ct' ct0)
end.

Lemma composeC_compose : forall c c0, contextC_to_context (composeC c c0) = compose (contextC_to_context c) (contextC_to_context c0).
Proof with auto.
induction c; intros; simpl; auto; rewrite IHc...
Qed.

Lemma commutes : forall v : valueC, closureC_to_closure (valueC_to_closureC v) = value_to_closure (valueC_to_value v).
Proof with auto.
induction v...
Qed.

Fixpoint nth_option (s : substitution) (n : nat) (c : context) {struct s} : option (closure * context) :=
match s, n with
| nil, _ => None
| h::t, 0 => Some (h, c)
| _::t, S m => nth_option t m c
end.

Fixpoint beta_plus (c:context) (n:nat) (s:substitution) (t:term) {struct c} : (closure * context) :=
    match n with
    | 0 => (pair t s, c)
    | S m => match c with
      | ap_r v ct => beta_plus ct m ((v:closure) :: s) t
      | _ => (pair (lam n t) s, c)
      end
    end.

Definition contract (r : redex) (c : context) : option (closure * context) :=
  match r with
    | r_beta (v_lam n t s) v => Some (beta_plus (ap_r v c) n s t)
    | r_get n s => nth_option s n c
    | r_app t0 t1 s => Some (comp (pair t0 s) (pair t1 s), c)
  end.

Lemma plug_compose  : forall c1 c2 r, plug r (compose c1 c2) = plug (plug r c1) c2.
Proof.
induction c1; simpl; auto.
Qed.

Lemma plug_empty    : forall c, plug c empty = c.
Proof.
auto.
Qed.

Lemma compose_empty : forall c, compose c empty = c.
Proof.
induction c; simpl; try rewrite IHc; auto.
Qed.

Lemma empty_compose : forall c, compose empty c = c.
Proof.
auto.
Qed.

Lemma empty_composeC : forall c, composeC emptyC c = c.
Proof.
auto.
Qed.

Lemma emptyC_empty  : contextC_to_context emptyC = empty.
Proof.
auto.
Qed.

Lemma decompose : forall cl:closure, (exists v:value, cl = value_to_closure v) \/ 
    (exists r:redex, exists ct:context, plug (redex_to_closure r) ct = cl).
Proof with auto.
induction cl.
destruct t.
right; exists (r_get n l); exists empty...
left; exists (v_lam n t l)...
right; exists (r_app t1 t2 l); exists empty...
right; elim IHcl2; intros; [destruct H as [v veq] | destruct H as [r [c req]]]; subst; clear IHcl2.
elim IHcl1; intros; [destruct H as [v' veq] | destruct H as [r [c req]]]; subst; clear IHcl1.
exists (r_beta v' v); exists empty; simpl...
exists r; exists (compose c (ap_r v empty)); rewrite plug_compose...
exists r; exists (compose c (ap_l cl1 empty)); rewrite plug_compose...
Qed.

Inductive decomp : Set :=
| d_val : value -> decomp
| d_red : redex -> context -> decomp.

Inductive interm_dec : Set :=
| in_dec : decomp -> interm_dec
| in_val : value -> context -> interm_dec
| in_term: closure -> context -> interm_dec.

Definition dec_term (cl : closure) (ct : context) : interm_dec :=
match cl with
| pair (lam n t) s => in_val (v_lam n t s) ct
| pair (var n) s => in_dec (d_red (r_get n s) ct)
| pair (appl t t0) s => in_dec (d_red (r_app t t0 s) ct)
| comp cl0 cl1 => in_term cl1 (ap_l cl0 ct)
end.

Definition dec_context (v : value) (ct : context) : interm_dec :=
match ct with 
| empty => in_dec (d_val v)
| ap_r v' ct0 => in_dec (d_red (r_beta v v') ct0)
| ap_l cl ct0 => in_term cl (ap_r v ct0)
end.

Lemma dec_context_empty : forall (v : value), dec_context v empty = in_dec (d_val v).
Proof.
auto.
Qed.

Lemma dec_context_not_value : forall v v0 c c0, ~dec_context v c = in_val v0 c0.
Proof.
intros; destruct c; discriminate.
Qed.
Hint Resolve dec_context_not_value : refocus.

Lemma dec_term_value : forall (v : value) (c : context), dec_term (value_to_closure v) c = in_val v c.
Proof.
intro v; case v; auto.
Qed.
Hint Resolve dec_term_value : refocus.

Lemma getC : forall l i (c : contextC) r c0, nth_option (map closureC_to_closure l) i c = Some (r, c0) ->
    {q:closureC * contextC | r = closureC_to_closure (fst q) /\ c0 = snd q}.
Proof.
induction l; induction i; simpl; intros; try discriminate.
split with (a, c).
inversion H; subst; simpl; auto.
eapply IHl; eapply H.
Qed.

Lemma closureC_ind :
forall (P : closureC' -> Prop),
  (forall (t : term) (s : list closureC'), (forall cl, In cl s -> P cl) -> P (pairC' t s)) ->
  forall cl : closureC, P cl.
Proof with eauto.
intros P hPair.
refine (fix IHc (c : closureC') : P c := _).
case c.
(* hPair *)
intros; apply hPair; induction l.
intros; inversion H.
intros.
destruct H.
rewrite <- H.
apply IHc.
fold (In cl l) in *.
apply IHl; apply H.
Qed.

Lemma closureC_to_closure_injective : forall (cl cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0.
Proof with auto.
induction cl using closureC_ind; intro cl0; case cl0; intros; try discriminate.
injection H0; intros; f_equal; subst...
generalize dependent s; induction l; destruct s; intros; try discriminate...
simpl in *; f_equal; inversion H1...
apply IHl; intros...
f_equal...
Qed.
Hint Resolve closureC_to_closure_injective : refocus.

Lemma substC_to_subst_injective : forall (s s0 : substitutionC), subC_to_sub s = subC_to_sub s0 -> s = s0.
Proof with auto with refocus.
induction s; intro s0; case s0; intros; simpl in *; try discriminate...
f_equal; inversion H...
Qed.
Hint Resolve substC_to_subst_injective : refocus.

Lemma valueC_to_value_injective : forall (v v0 : valueC), valueC_to_value v = valueC_to_value v0 -> v = v0.
Proof with auto with refocus.
intros; destruct v; destruct v0; inversion H; f_equal...
Qed.
Hint Resolve valueC_to_value_injective : refocus.

Lemma valueC_to_closureC_injective : forall (v v0 : valueC), valueC_to_closureC v = valueC_to_closureC v0 -> v = v0.
Proof with auto.
intros; destruct v; destruct v0; inversion H...
Qed.
Hint Resolve valueC_to_closureC_injective : refocus.

Lemma contextC_to_context_injective : forall (ct ct0 : contextC), contextC_to_context ct = contextC_to_context ct0 -> ct = ct0.
Proof with auto with refocus.
induction ct; intro ct0; case ct0; intros; try discriminate; simpl; inversion H; f_equal...
Qed.
Hint Resolve contextC_to_context_injective : refocus.

Lemma getB :
  forall n (ct : contextC) (s:substitutionC) r t ct', 
    beta_plus ct n (subC_to_sub s) t = (r, ct') -> 
    {p : (closureC * contextC) | (fst p:closure) = r & (snd p:context) = ct'}.
Proof with auto.
induction n; induction ct; intros; simpl in H; try discriminate.
inversion H; subst; split with (pairC t s, emptyC); simpl; f_equal; reflexivity.
inversion H; subst; split with (pairC t s, ap_rC v ct); simpl; f_equal.
inversion H; subst; split with (pairC t s, ap_lC c ct); simpl; f_equal.
inversion H; subst; split with (pairC (lam (S n) t) s, emptyC); simpl; f_equal...
apply IHn with ct ((v:closureC) :: s) t; rewrite <- commutes in H...
inversion H; subst; split with (pairC (lam (S n) t) s, ap_lC c ct); simpl; f_equal...
Qed.

Definition recons (p:term * substitutionC * contextC) : closure :=
match p with
| (t, s, c) => plug (closureC_to_closure (pairC t s)) c
end.

Inductive dec_by_cls : closure -> context -> (term * substitutionC * contextC) + (valueC * contextC) -> Prop :=
| dbc_pair : forall (t : term) (s : substitutionC) (c : contextC),
             dec_by_cls (closureC_to_closure (pairC t s)) (contextC_to_context c) (inl (valueC * contextC) (t,s,c))
| dbc_val  : forall (v : valueC) (c : contextC),
             (forall t s, (valueC_to_closureC v) <> pairC t s) ->
             dec_by_cls (closureC_to_closure (valueC_to_closureC v)) (contextC_to_context c) (inr (term * substitutionC * contextC) (v, c))
| dbc_many : forall (cl cl' : closure) (c c' : context) (p : (term * substitutionC * contextC)+(valueC * contextC)),
             dec_term cl c = in_term cl' c' -> dec_by_cls cl' c' p -> dec_by_cls cl c p.

Lemma dec_by_cls_folds_left : forall t s ct cl c, dec_by_cls cl c (inl _ (t, s, ct)) -> plug cl c = plug (closureC_to_closure (pairC t s)) (contextC_to_context ct).
Proof with auto.
induction cl; intros; inversion_clear H; try (induction t0; discriminate)...
inversion H0; subst; apply (IHcl2 _ H1).
Qed.

Lemma dec_by_cls_folds_right : forall v ct cl c, dec_by_cls cl c (inr _ (v, ct)) -> plug cl c = plug (closureC_to_closure (valueC_to_closureC v)) (contextC_to_context ct).
Proof with auto.
induction cl; intros; inversion_clear H; try (induction t; discriminate)...
inversion H0; subst; apply (IHcl2 _ H1).
Qed.

Lemma dec_by_cls_left_only :forall (cl : closure) (ct : context) (v : valueC) (ct0 : contextC), ~(dec_by_cls cl ct (inr _ (v, ct0))).
Proof with eauto.
induction cl; intros; intro.
inversion H.
destruct v; simpl in H3; apply (H3 (lam n t0) s); reflexivity.
simpl in H0; destruct t; discriminate.
inversion H; subst.
destruct v; discriminate.
injection H0; intros; subst cl' c'.
apply (IHcl2 _ _ _ H1).
Qed.
Hint Immediate dec_by_cls_left_only : refocus.

Lemma dec_by_cls_function : forall cl c p p', dec_by_cls cl c p -> dec_by_cls cl c p' -> p = p'.
Proof with eauto with refocus.
induction cl; intros; inversion H; inversion H0; subst; intros; try discriminate; try (induction t; discriminate); try (induction v; discriminate)...
repeat f_equal...
destruct v; cutrewrite (pair' t (map closureC_to_closure s) = closureC_to_closure (pairC t s)) in H5...
apply closureC_to_closure_injective in H5; contradict (H6 _ _ H5).
destruct v; cutrewrite (pair' t (map closureC_to_closure s) = closureC_to_closure (pairC t s)) in H1...
apply closureC_to_closure_injective in H1; contradict (H2 _ _ H1).
rewrite <- H5 in H1; repeat f_equal...
clear IHcl1; injection H1; intros; subst cl' c'; injection H6; intros; subst cl'0 c'0; clear H6 H1.
eapply IHcl2; eauto.
Qed.

Definition unfold_c_red :
forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl, ct1)) ->
  {p : (term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct1 p}.
Proof with auto.
intros v ct; case ct; intros; simpl in *; try discriminate.
injection H; intros; subst; clear H; generalize H0; clear H0; case v; intros;
simpl in H0; injection H0; clear H0; intros.
change (beta_plus (ap_rC v0 c:contextC) n (subC_to_sub s) t = (cl, ct1)) in H.
apply getB in H; destruct H as [[cl0 ct0] hcl hct]; simpl in *; subst.
induction cl0.
split with (inl _ (t0, l, ct0)); constructor.
Defined.

Definition unfold_red :
forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl0, ct1)) ->
  {p:(term * substitutionC * contextC)+(valueC * contextC) | dec_by_cls cl0 ct1 p}.
Proof with auto.
intro cl; case cl; intro t; case t; intros; simpl in *; try discriminate;
injection H; clear H; intros; subst.
simpl in H0; apply getC in H0; destruct H0 as [[cl2 ct2] [ecl ect]]; simpl in *; subst.
induction cl2.
split with (inl _ (t0, l0, ct2)); constructor.
simpl in H0; injection H0; clear H0; intros; subst.
split with (inl _ (t1, l, ap_lC (pairC t0 l) ct));
econstructor; simpl.
f_equal...
change (dec_by_cls (pairC t1 l) (ap_lC (pairC t0 l) ct : contextC) (inl _ (t1, l, ap_lC (pairC t0 l) ct))); constructor.
Defined.

Definition unfold_c_cls :
forall (v : valueC) (ct : contextC) (cl : closure) (ct0 : context),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_term cl ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct0 p}.
Proof with auto.
intros v ct; case ct; intros; simpl; try discriminate.
injection H; intros; subst; clear H; destruct c.
split with (inl _ (t, l, ap_rC v c0));
change (dec_by_cls (pairC t l:closureC) (ap_rC v c0:contextC) (inl _ (t, l, ap_rC v c0))); constructor.
Defined.

Definition unfold_cls :
forall (cl : closureC) (ct : contextC) (cl0 : closure) (ct0 : context),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_term cl0 ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl0 ct0 p}.
Proof with auto.
intro cl; case cl; intro t; case t; intros; simpl; discriminate.
Defined.

Lemma dec_Val :
forall t s (ct : contextC) c v,
  dec_term (closureC_to_closure (pairC t s)) (contextC_to_context ct) = in_val v c ->
  exists v0 : valueC, exists ct1 : contextC,
    (valueC_to_value v0) = v /\ c = (contextC_to_context ct1).
Proof with auto.
intro t; case t; intros; simpl in *; try discriminate.
exists (v_lamC n t0 s); exists ct; simpl; constructor;
injection H; intros; subst...
Qed.

Lemma dec_c_Val :
forall v (ct:contextC) v0 c,
  dec_context (valueC_to_value v) (contextC_to_context ct) = in_val v0 c ->
  exists ct0 : contextC, exists v1 : valueC, (valueC_to_value v1) = v0 /\ c = (contextC_to_context ct0).
Proof.
intros v ct; case ct; intros; simpl in *; discriminate.
Qed.

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

Lemma dec_redex_self : forall (r : redex) (c : context), dec (redex_to_closure r) c (d_red r c).
Proof with auto.
intro r; case r; intros; simpl; try (constructor; auto; fail).
econstructor 3.
simpl; f_equal...
case v; econstructor 2.
apply dec_term_value.
econstructor 3.
simpl; f_equal...
econstructor 2.
simpl; intros; f_equal...
constructor...
Qed.

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

(** correctness of atomic decompositions *)
Definition decomp_to_term (d : decomp) : closure :=
match d with
  | d_val v => value_to_closure v
  | d_red r c0 => plug (redex_to_closure r) c0
end.
Lemma dec_term_correct : forall cl c, match dec_term cl c with
  | in_dec d => decomp_to_term d = plug cl c
  | in_val v c0 => plug (value_to_closure v) c0 = plug cl c
  | in_term cl0 c0 => plug cl0 c0 = plug cl c
end.
Proof with auto.
intro cl; case cl; intros; simpl in *...
case t; intros; simpl...
Qed.

Lemma dec_context_correct : forall v c, match dec_context v c with
  | in_dec d => decomp_to_term d = plug (value_to_closure v) c
  | in_val v0 c0 => plug (value_to_closure v0) c0 = plug (value_to_closure v) c
  | in_term t c0 => plug t c0 = plug (value_to_closure v) c
end.
Proof with auto.
intros v ct; case ct; intros; simpl...
Qed.

Lemma dec_plug : forall c c0 cl d, dec (plug cl c) c0 d -> dec cl (compose c c0) d.
Proof with auto.
induction c; intros; simpl in *; try trivial;
assert (hh := IHc _ _ _ H); inversion hh; simpl in H0; try discriminate; subst.
injection H0; intros; subst...
destruct v; inversion H1; try discriminate; subst.
inversion H2; subst.
inversion H3; subst; try discriminate.
inversion H4; subst...
inversion H0; subst...
Qed.

Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
Proof with eauto.
induction c; intros; simpl in *; trivial;
apply IHc.
constructor 3 with (v:closure) (ap_l t (compose c c0))...
econstructor 2.
apply dec_term_value...
econstructor 3;
[simpl; f_equal | apply H]...
econstructor 3...
simpl...
Qed.

End CallByValue.

Module CBV_PEM := ProperPEMachine (CallByValue).
Module CBV_Eval := Evaluator (CallByValue).
Definition eval_CBV := CBV_Eval.eval.
Definition eval_CBV_EAM := CBV_PEM.E.eval.

Lemma eval_equiv : forall t v, eval_CBV t v <-> eval_CBV_EAM t v.
Proof with eauto.
intros; split; intros; inversion_clear H; inversion_clear H0;
econstructor; try (econstructor; eauto; fail);
clear H; induction H1; try (constructor; fail);
inversion_clear H0; econstructor; eauto; constructor...
Qed.

Module ZincMachine.

Definition term := CallByValue.term.
Definition closureC := CallByValue.closureC.
Definition substC := CallByValue.substitutionC.
Definition contextC := CallByValue.contextC.
Definition valueC := CallByValue.valueC.
Definition value := CallByValue.value.
Definition emptyC := CallByValue.emptyC.
Definition v_lamC := CallByValue.v_lamC.
Definition var := CallByValue.var.
Definition lam := CallByValue.lam.
Definition appl := CallByValue.appl.
Definition ap_rC := CallByValue.ap_rC.
Definition ap_lC := CallByValue.ap_lC.
Definition subst := CallByValue.substitution.
Definition context := CallByValue.context.
Definition closure := CallByValue.closure.
Definition pairC := CallByValue.pairC.

Definition closureC_to_closure (cl:closureC) : closure := CallByValue.closureC_to_closure cl.
Definition substC_to_subst (s : substC) : subst := CallByValue.subC_to_sub s.
Definition valueC_to_value (v : valueC) : value := CallByValue.valueC_to_value v.
Definition contextC_to_context (ct : contextC) : context := CallByValue.contextC_to_context ct.
Definition valueC_to_closureC (v : valueC) : closureC := CallByValue.valueC_to_closureC v.

Coercion closureC_to_closure : closureC >-> closure.
Coercion substC_to_subst : substC >-> subst.
Coercion valueC_to_closureC : valueC >-> closureC.
Coercion contextC_to_context : contextC >-> context.

Definition nth_option := CallByValue.nth_option.
Definition beta_plus := CallByValue.beta_plus.
Definition contract := CallByValue.contract.

Definition configuration := CBV_PEM.configuration.
Definition c_init := CBV_PEM.c_init.
Definition c_eval := CBV_PEM.c_eval.
Definition c_final := CBV_PEM.c_final.

Inductive transition : configuration -> configuration -> Prop :=
| t_init  : forall (t : term), transition (c_init t) (c_eval t nil emptyC)
| t_var   : forall (n : nat) (s s0 : substC) (c c0 : contextC) (t : term),
             nth_option (s:subst) n (c:context) = Some (closureC_to_closure (pairC t s0), c0:context) ->
             transition (c_eval (var n) s c) (c_eval t s0 c0)
| t_app   : forall (t0 t1:term) (s:substC) (c:contextC),
             transition (c_eval (appl t0 t1) s c) (c_eval t1 s (ap_lC (pairC t0 s) c))
| t_v_mt  : forall (n : nat) (t : term) (s : substC),
             transition (c_eval (lam n t) s emptyC) (c_final (v_lamC n t s))
| t_v_ap_l: forall (n : nat) (t t0 : term) (s s0 : substC) (c : contextC),
             transition (c_eval (lam n t) s (ap_lC (pairC t0 s0) c)) (c_eval t0 s0 (ap_rC (v_lamC n t s) c))
| t_v_ap_r: forall (n : nat) (t t0 : term) (s s0 : substC) (v : valueC) (ct ct0 : contextC),
             beta_plus (ap_rC v ct:CallByValue.contextC) n (s:subst) t = (closureC_to_closure (pairC t0 s0), ct0:context) ->
             transition (c_eval (lam n t) s (ap_rC v ct)) (c_eval t0 s0 ct0).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step : forall w w' : configuration, 
               transition w w' -> trans_close w w'
| mul_step : forall w w' w'' : configuration, 
               transition w w' -> trans_close w' w'' -> trans_close w w''.

Inductive eval : term -> valueC -> Prop :=
| e_k_intro : forall (t : term) (v : valueC), trans_close (c_init t) (c_final v) -> eval t v.

Definition dec_term := CallByValue.dec_term.
Definition dec_context := CallByValue.dec_context.
Definition in_dec := CallByValue.in_dec.
Definition d_red := CallByValue.d_red.
Definition redex := CallByValue.redex.
Definition dec_by_cls := CallByValue.dec_by_cls.

Lemma unf_red_correct : forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure)
  (H : dec_term (cl:closure) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl0, ct1)),
  dec_by_cls cl0 ct1 (CBV_PEM.PEM.UEAM.unf_red cl ct r ct0 ct1 cl0 H H1).
Proof with auto.
intros; unfold CBV_PEM.PEM.UEAM.unf_red; simpl in *.
remember (CallByValue.unfold_red cl ct r ct0 ct1 cl0 H H1).
destruct s as [p q]...
Qed.

Lemma unf_c_red_correct : forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl, ct1)),
  dec_by_cls cl ct1 (CBV_PEM.PEM.UEAM.unf_c_red v ct r ct0 ct1 cl H H1).
Proof with auto.
intros; unfold CBV_PEM.PEM.UEAM.unf_c_red; simpl in *.
remember (CallByValue.unfold_c_red v ct r ct0 ct1 cl H H1).
destruct s as [p q]...
Qed.

Lemma unf_c_cls_correct : forall (v : valueC) (ct : contextC) (ct0 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) (ct:context) = CallByValue.in_term cl ct0),
  dec_by_cls cl ct0 (CBV_PEM.PEM.UEAM.unf_c_cls v ct ct0 cl H).
Proof with auto.
intros; unfold CBV_PEM.PEM.UEAM.unf_c_cls; simpl in *.
remember (CallByValue.unfold_c_cls v ct cl ct0 H).
destruct s as [p q]...
Qed.

Lemma transition_unf_z : forall c0 c1, CBV_PEM.transition c0 c1 -> transition c0 c1.
Proof with eauto with refocus.
induction 1; try (induction t; discriminate); try (induction c; discriminate).
(* Case 1 (init) *)
constructor.
(* Case 2 (eval -> d_red -> eval) *)
assert (dec_by_cls cl c1 (inl (CBV_PEM.PEM.UEAM.valueC * CBV_PEM.PEM.UEAM.contextC) (t0, s0, c2))).
rewrite <- H0; apply unf_red_correct.
clear H0; destruct t; simpl in H; try discriminate.
(* Case 2.1 (r_get) *)
inversion H; subst r c0; clear H.
simpl in H1; assert (ht := CallByValue.getC _ _ _ _ _ H1).
destruct ht as [[cl2 ct2] [ht hq]]; subst.
inversion H2; subst.
apply CallByValue.contextC_to_context_injective in H; subst ct2.
change (closureC_to_closure (pairC t0 s0) = closureC_to_closure cl2) in H0.
apply CallByValue.closureC_to_closure_injective in H0; subst cl2.
constructor...
simpl in *.
induction cl2; try discriminate.
induction t; discriminate.
(* Case 2.3 (r_app) *)
inversion H; subst r c0; clear H.
simpl in *; inversion H1; rewrite <- H0 in H2; clear H0 H1.
inversion H2; subst.
inversion H; subst.
inversion H0; subst; clear H2 H.
change (CallByValue.contextC_to_context c2 = CallByValue.contextC_to_context (ap_lC (pairC t1 s0) c)) in H5;
apply CallByValue.contextC_to_context_injective in H5; subst.
apply CallByValue.substC_to_subst_injective in H4; subst.
constructor...
induction t2; discriminate.
(* apply -> final *)
destruct t; inversion H; apply CallByValue.contextC_to_context_injective in H3; subst.
destruct c0; inversion H0; apply CallByValue.valueC_to_value_injective in H3; subst.
change (valueC_to_value (v_lamC n t s) = valueC_to_value v0) in H2;
apply CallByValue.valueC_to_value_injective in H2; subst; constructor.
(* eval -> val -> red -> eval *)
assert (CallByValue.dec_by_cls cl c2 (inl (CBV_PEM.PEM.UEAM.valueC * CBV_PEM.PEM.UEAM.contextC) (t0, s0, c3))).
rewrite <- H0; apply unf_c_red_correct.
destruct t; inversion H; subst; destruct c0; inversion H1; clear H H0 H1; intros; subst.
change (valueC_to_value (v_lamC n t s) = valueC_to_value v) in H5;
apply CallByValue.valueC_to_value_injective in H5; subst; inversion H2.
change (beta_plus (contextC_to_context (ap_rC v0 c0)) n (substC_to_subst s) t = (cl, c2)) in H0.
remember H0; clear Heqe; apply CallByValue.getB in e; destruct e as [[cl' ct'] ecl ect]; subst.
destruct cl'; inversion H3; subst.
apply CallByValue.contextC_to_context_injective in H; apply CallByValue.substC_to_subst_injective in H4;
apply CallByValue.contextC_to_context_injective in H6; subst; constructor...
destruct t1; discriminate.
(* eval -> val -> eval *)
assert (CallByValue.dec_by_cls cl c1 (inl (CBV_PEM.PEM.UEAM.valueC * CBV_PEM.PEM.UEAM.contextC) (t0, s0, c2))).
rewrite <- H0; apply unf_c_cls_correct.
destruct t; inversion H; subst; destruct c0; inversion H1; clear H H0 H1; intros; subst.
change (valueC_to_value (v_lamC n t s) = valueC_to_value v) in H4;
apply CallByValue.valueC_to_value_injective in H4;
apply CallByValue.contextC_to_context_injective in H5; subst.
destruct c0; inversion H2; subst.
change (contextC_to_context c2 = contextC_to_context (ap_rC (v_lamC n t s) c3)) in H;
apply CallByValue.contextC_to_context_injective in H;
apply CallByValue.substC_to_subst_injective in H1; subst; constructor.
destruct t1; discriminate.
Qed.
Hint Resolve transition_unf_z.

Lemma trans_close_unf_z : forall c c0, CBV_PEM.trans_close c c0 -> trans_close c c0.
Proof with eauto.
induction 1; [constructor | econstructor 2]...
Qed.
Hint Resolve trans_close_unf_z.

Lemma evalUnfZinc : forall t v, CBV_PEM.eval t v -> eval t v.
Proof with auto.
intros t v H; constructor; inversion_clear H; inversion H0; inversion H; subst...
Qed.
Hint Resolve evalUnfZinc.

Lemma transition_z_unf : forall c c0, transition c c0 -> CBV_PEM.transition c c0.
Proof with eauto with refocus.
induction 1.
(* init *)
constructor.
(* var -> eval *)
assert (ha : CBV_PEM.dec_term (pairC (var n) s) (c:context) = in_dec (d_red (CallByValue.r_get n (s:subst)) (c:context)))...
constructor 3 with _ _ _ _ ha H.
unfold CBV_PEM.unf_red; unfold CBV_PEM.PEM.unf_red; unfold CBV_PEM.PEM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; subst.
repeat f_equal...
contradict peq...
destruct t; discriminate.
(* appl -> eval *)
assert (ha : CBV_PEM.dec_term (pairC (appl t0 t1) s) (c:context) = in_dec (d_red (CallByValue.r_app t0 t1 (s:subst)) (c:context)))...
assert (hb : contract (CallByValue.r_app t0 t1 (s:subst)) (c:context) = Some (CallByValue.comp (closureC_to_closure (pairC t0 s)) (closureC_to_closure (pairC t1 s)), c:context))...
constructor 3 with _ _ _ _ ha hb.
unfold CBV_PEM.unf_red; unfold CBV_PEM.PEM.unf_red; unfold CBV_PEM.PEM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
inversion H; subst; clear H.
inversion H0; subst.
apply CallByValue.substC_to_subst_injective in H2; subst.
repeat f_equal...
contradict peq...
destruct t1; discriminate.
(* lam, empty -> final *)
constructor 4 with (v_lamC n t s) emptyC...
(* lam, ap_l  -> eval *)
assert (hb : CBV_PEM.dec_context (valueC_to_value (v_lamC n t s)) (contextC_to_context (ap_lC (pairC t0 s0) c)) = CallByValue.in_term (closureC_to_closure (pairC t0 s0)) (contextC_to_context (ap_rC (v_lamC n t s) c)))...
constructor 6 with (v_lamC n t s) (ap_lC (pairC t0 s0) c) _ _ hb...
unfold CBV_PEM.unf_c_cls; unfold CBV_PEM.PEM.unf_c_cls; unfold CBV_PEM.PEM.UEAM.unf_c_cls; destruct CallByValue.unfold_c_cls as [p peq].
inversion peq; subst.
repeat f_equal...
contradict peq...
destruct t0; discriminate.
(* lam, ap_r -> eval *)
assert (ha : CBV_PEM.dec_context (CBV_PEM.valueC_to_value (v_lamC n t s)) (CBV_PEM.contextC_to_context (ap_rC v ct)) = CBV_PEM.in_dec (CBV_PEM.d_red (CallByValue.r_beta (CBV_PEM.valueC_to_value (v_lamC n t s)) (CBV_PEM.valueC_to_value v)) (CBV_PEM.contextC_to_context ct)))...
assert (hb : contract (CallByValue.r_beta (valueC_to_value (v_lamC n t s)) (valueC_to_value v)) (ct : context) = Some (closureC_to_closure (pairC t0 s0), (ct0:context))).
simpl; f_equal...
constructor 5 with (v_lamC n t s) (ap_rC v ct) _ _ _ _ ha hb...
unfold CBV_PEM.unf_c_red; unfold CBV_PEM.PEM.unf_c_red; unfold CBV_PEM.PEM.UEAM.unf_c_red; destruct CallByValue.unfold_c_red as [p peq]; clear ha.
inversion peq; subst.
repeat f_equal...
contradict peq...
destruct t0; discriminate.
Qed.
Hint Resolve transition_z_unf.

Lemma trans_close_z_unf : forall c c0, trans_close c c0 -> CBV_PEM.trans_close c c0.
Proof with eauto.
induction 1; [constructor | econstructor 2]...
Qed.
Hint Resolve trans_close_z_unf.

Lemma evalZincUnf : forall t v, eval t v -> CBV_PEM.eval t v.
Proof with auto.
intros t v H; constructor; inversion_clear H; inversion H0; inversion H; subst...
Qed.
Hint Resolve evalZincUnf.

Theorem KrivineMachineCorrect : forall t (v:valueC), eval_CBV t (valueC_to_value v) <-> eval t v.
Proof with auto with refocus.
intros; rewrite eval_equiv; rewrite CBV_PEM.evalMachine; try split...
Qed.

End ZincMachine.