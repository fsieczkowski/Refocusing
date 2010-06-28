Require Import refocusing_environments_cs.
Require Import Setoid.

Module CallByName <: RED_LANG.

Inductive term' : Set :=
| var : nat -> term'
| lam : nat -> term' -> term'
| appl : term' -> term' -> term'.
Definition term := term'.

Inductive closure' : Set :=
| pair' : term -> list closure' -> closure'
| comp  : closure' ->  closure' -> closure'
| u_lam : nat -> term -> list closure' -> list closure' -> closure'.

Inductive context' : Set :=
| mt   : context'
| ap_r : closure' -> context' -> context'.

Definition closure := closure'.
Definition substitution := list closure.
Definition pair : term -> substitution -> closure := pair'.

Definition context := context'.
Definition empty : context := mt.

Inductive value' : Set :=
| v_lam : nat -> term -> substitution -> list closure -> value'.
Definition value := value'.

Inductive redex' : Set :=
| r_beta : value -> closure -> redex'
| r_lam  : nat -> term -> substitution -> redex'
| r_get  : nat -> substitution -> redex'
| r_app  : term -> term -> substitution -> redex'.
Definition redex := redex'.

Inductive closureC' : Set :=
| pairC' : term -> list closureC' -> closureC'
| u_lamC : nat -> term -> list closureC' -> list closureC' -> closureC'.

Inductive contextC' : Set :=
| mtC   : contextC'
| ap_rC : closureC' -> contextC' -> contextC'.
Definition closureC := closureC'.
Definition substitutionC := list closureC.
Definition pairC : term -> substitutionC -> closureC := pairC'.

Definition contextC := contextC'.
Definition emptyC : contextC := mtC.

Inductive valueC' : Set :=
| v_lamC : nat -> term -> substitutionC -> list closureC -> valueC'.
Definition valueC := valueC'.

Inductive redexC' : Set :=
| r_betaC : valueC -> closureC -> redexC'.
Definition redexC := redexC'.

Fixpoint plug (cl : closure) (ct : context) {struct ct} : closure :=
match ct with
| empty => cl
| ap_r cl0 ct0 => plug (comp cl cl0) ct0
end.

Fixpoint compose (ct : context) (ct0 : context) {struct ct} : context :=
match ct with
| empty => ct0
| ap_r cl ct' => ap_r cl (compose ct' ct0)
end.

Fixpoint composeC (ct : contextC) (ct0 : contextC) {struct ct} : contextC :=
match ct with
| emptyC => ct0
| ap_rC cl ct' => ap_rC cl (composeC ct' ct0)
end.

Definition value_to_closure : value -> closure :=
fun v => match v with
| v_lam n t s c => u_lam n t s c
end.
Coercion value_to_closure : value >-> closure.

Definition redex_to_closure : redex -> closure :=
fun r => match r with
| r_beta v cl => comp (value_to_closure v) cl
| r_lam n t s => pair (lam n t) s
| r_get n s => pair (var n) s
| r_app t t0 s => pair (appl t t0) s
end.
Coercion redex_to_closure : redex >-> closure.

Fixpoint closureC_to_closure (cl : closureC) : closure :=
match cl with
| pairC t s => pair t (map closureC_to_closure s)
| u_lamC n t s l => u_lam n t (map closureC_to_closure s) (map closureC_to_closure l)
end.


Fixpoint contextC_to_context (ct : contextC) : context :=
match ct with
| mtC => mt
| ap_rC clc ctc => ap_r (closureC_to_closure clc) (contextC_to_context ctc)
end.

Coercion closureC_to_closure : closureC >-> closure.
Coercion contextC_to_context : contextC >-> context.
Definition subC_to_sub : substitutionC -> substitution := map closureC_to_closure.

Definition valueC_to_value (v : valueC) : value :=
match v with
| v_lamC n t s l => v_lam n t (subC_to_sub s) (subC_to_sub l)
end.

Definition redexC_to_redex (r : redexC) : redex :=
match r with
| r_betaC v cl => r_beta (valueC_to_value v) (closureC_to_closure cl)
end.

Definition valueC_to_closureC (v : valueC) : closureC :=
match v with
| v_lamC n t s l => u_lamC n t s l
end.
Coercion valueC_to_closureC : valueC >-> closureC.

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

Fixpoint beta_plus (c:context) (n:nat) (s:substitution) (l : list closure) (t:term) {struct c} : (closure * context) :=
    match n with
    | 0 => (pair t (app l s), c)
    | S m => match c with
      | ap_r cl ct => beta_plus ct m s (cl :: l) t
      | empty => (u_lam n t s l, c)
      end
    end.

Definition contract (r : redex) (c : context) : option (closure * context) :=
  match r with
    | r_beta (v_lam n t s l) cl => Some (beta_plus (ap_r cl c) n s l t)
    | r_lam n t s => Some (beta_plus c n s nil t)
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
case t; intros; right.
exists (r_get n l); exists empty...
exists (r_lam n t0 l); exists empty...
exists (r_app t0 t1 l); exists empty...
right; clear IHcl2; elim IHcl1; intros.
destruct H as [v H]; subst cl1.
exists (r_beta v cl2); exists empty...
destruct H as [r [ct H]]; subst cl1.
exists r; exists (compose ct (ap_r cl2 empty)).
rewrite plug_compose; simpl...
left; exists (v_lam n t l l0)...
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
| pair (lam n t) s => in_dec (d_red (r_lam n t s) ct)
| pair (var n) s => in_dec (d_red (r_get n s) ct)
| pair (appl t t0) s => in_dec (d_red (r_app t t0 s) ct)
| comp cl0 cl1 => in_term cl0 (ap_r cl1 ct)
| u_lam n t s l => in_val (v_lam n t s l) ct
end.

Definition dec_context (v : value) (ct : context) : interm_dec :=
match ct with 
| empty => in_dec (d_val v)
| ap_r cl ct0  => in_dec (d_red (r_beta v cl) ct0)
end.

Lemma dec_context_empty : forall (v : value), dec_context v empty = in_dec (d_val v).
Proof.
auto.
Qed.
Lemma dec_context_not_value : forall v v0 c c0, ~dec_context v c = in_val v0 c0.
Proof.
intros; destruct c; discriminate.
Qed.
Lemma dec_term_value : forall (v : value) (c : context), dec_term (value_to_closure v) c = in_val v c.
Proof.
intro v; case v; simpl; auto.
Qed.

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
  (forall (t : term) (s l : list closureC') (n : nat), (forall cl, In cl s -> P cl) -> (forall cl, In cl l -> P cl) -> P (u_lamC n t s l)) ->
  forall cl : closureC, P cl.
Proof with eauto.
intros P hPair hULam.
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
(* hULam *)
intros; apply hULam.
induction l; intros; inversion H.
rewrite <- H0; apply IHc.
fold (In cl l) in *.
apply IHl; apply H0.
induction l0; intros; inversion H.
rewrite <- H0; apply IHc.
fold (In cl l) in *;
apply IHl0; apply H0.
Qed.

Lemma closureC_to_closure_injective : forall (cl cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0.
Proof with auto.
induction cl using closureC_ind; intro cl0; case cl0; intros; try discriminate.
injection H0; intros; f_equal; subst...
generalize dependent s; induction l; destruct s; intros; try discriminate...
simpl in *; f_equal; inversion H1...
apply IHl; intros...
f_equal...

injection H1; intros; f_equal; subst...
generalize dependent l0; induction s; destruct l0; intros; try discriminate...
simpl in *; f_equal; inversion H3...
apply IHs; intros...
f_equal...
generalize dependent l1; induction l; destruct l1; intros; try discriminate...
simpl in *; f_equal; inversion H2...
apply IHl; intros...
f_equal...
Qed.
Hint Resolve closureC_to_closure_injective : ref.

Lemma substC_to_subst_injective : forall (s s0 : substitutionC), subC_to_sub s = subC_to_sub s0 -> s = s0.
Proof with auto with ref.
induction s; intro s0; case s0; intros; simpl in *; try discriminate...
f_equal; inversion H...
Qed.
Hint Resolve substC_to_subst_injective : ref.

Lemma valueC_to_value_injective : forall (v v0 : valueC), valueC_to_value v = valueC_to_value v0 -> v = v0.
Proof with auto with ref.
intros; destruct v; destruct v0; injection H; intros; f_equal...
Qed.
Hint Resolve valueC_to_value_injective : ref.

Lemma valueC_to_closureC_injective : forall (v v0 : valueC), valueC_to_closureC v = valueC_to_closureC v0 -> v = v0.
Proof with auto.
intros v v0; case v; case v0; intros; simpl in *; injection H; intros; subst...
Qed.
Hint Resolve valueC_to_closureC_injective : ref.

Lemma contextC_to_context_injective : forall (ct ct0 : contextC), contextC_to_context ct = contextC_to_context ct0 -> ct = ct0.
Proof with auto with ref.
induction ct; intro ct0; case ct0; intros; try discriminate; simpl; inversion H; f_equal...
Qed.
Hint Resolve contextC_to_context_injective : ref.

Lemma getB :
  forall n (ct : contextC) (s l:substitutionC) r t ct', 
    beta_plus ct n (subC_to_sub s) (subC_to_sub l) t = (r, ct') -> 
    {p : (closureC * contextC) | (fst p:closure) = r & (snd p:context) = ct'}.
Proof with auto.
induction n; induction ct; intros; simpl in H; try discriminate.
inversion H; subst; split with (pairC t (l++s), emptyC); simpl; f_equal;
[unfold subC_to_sub; apply map_app | reflexivity].
inversion H; subst; split with (pairC t (l++s), ap_rC c ct); simpl; f_equal;
unfold subC_to_sub; apply map_app.
inversion H; subst; split with (u_lamC (S n) t s l, emptyC); simpl; f_equal...
apply IHn with ct s (c :: l) t; auto.
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
inversion H0; subst; apply (IHcl1 _ H1).
Qed.

Lemma dec_by_cls_folds_right : forall v ct cl c, dec_by_cls cl c (inr _ (v, ct)) -> plug cl c = plug (closureC_to_closure (valueC_to_closureC v)) (contextC_to_context ct).
Proof with auto.
induction cl; intros; inversion_clear H; try (induction t; discriminate)...
inversion H0; subst; apply (IHcl1 _ H1).
Qed.

Lemma dec_by_cls_function : forall cl c p p', dec_by_cls cl c p -> dec_by_cls cl c p' -> p = p'.
Proof with eauto.
induction cl; intros; inversion H; inversion H0; subst; intros; try discriminate; try (induction t; discriminate); try (induction v; discriminate)...
apply contextC_to_context_injective in H5; apply substC_to_subst_injective in H7; subst...
rewrite H1 in H6; inversion H6; subst cl'0 c'0;
inversion H1; subst cl' c'; clear H1 H6; eapply IHcl1...
repeat f_equal.
rewrite <- H5 in H1.
induction v; induction v0; simpl in *; inversion H1; inversion H5; subst;
apply substC_to_subst_injective in H10; apply substC_to_subst_injective in H9; subst...
apply contextC_to_context_injective...
Qed.

Definition unfold_c_red :
forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl, ct1)) ->
  {p : (term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct1 p}.
Proof with auto.
intros v ct; case ct; intros; simpl in *; try discriminate.
injection H; intros; subst; clear H; generalize H0; clear H0; case v; intros;
simpl in H0; injection H0; clear H0; intros.
change (beta_plus (ap_rC c c0:contextC) n (subC_to_sub s) (subC_to_sub l) t = (cl, ct1)) in H.
apply getB in H; destruct H as [[cl0 ct0] hcl hct]; simpl in *; subst.
induction cl0.
split with (inl _ (t0, l0, ct0)); constructor.
split with (inr _ ((v_lamC n0 t0 l0 l1), ct0)).
change (dec_by_cls ((valueC_to_closureC (v_lamC n0 t0 l0 l1))) ct0 (inr _ (v_lamC n0 t0 l0 l1, ct0))); constructor.
intros t1 s0 eq; discriminate.
Defined.

Definition unfold_red :
forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl0, ct1)) ->
  {p:(term * substitutionC * contextC)+(valueC * contextC) | dec_by_cls cl0 ct1 p}.
Proof with auto.
intro cl; case cl; [intro t; case t | intros; simpl; discriminate]; intros; simpl in *;
injection H; clear H; intros; subst.
simpl in H0; apply getC in H0; destruct H0 as [[cl2 ct2] [ecl ect]]; simpl in *; subst.
induction cl2.
split with (inl _ (t0, l0, ct2)); constructor.
split with (inr _ ((v_lamC n0 t0 l0 l1), ct2)).
change (dec_by_cls ((valueC_to_closureC (v_lamC n0 t0 l0 l1))) ct2 (inr _ (v_lamC n0 t0 l0 l1, ct2))); constructor.
intros t1 s eq; discriminate.
simpl in H0; injection H0; clear H0; intros.
change (beta_plus ct n (subC_to_sub l) (subC_to_sub nil) t0 = (cl0, ct1)) in H;
apply getB in H; destruct H as [[cl2 ct2] ecl ect]; simpl in *; subst.
induction cl2.
split with (inl _ (t1, l0, ct2)); constructor.
split with (inr _ ((v_lamC n0 t1 l0 l1), ct2)).
change (dec_by_cls ((valueC_to_closureC (v_lamC n0 t1 l0 l1))) ct2 (inr _ (v_lamC n0 t1 l0 l1, ct2))); constructor.
intros t2 s eq; discriminate.
simpl in H0; injection H0; clear H0; intros; subst.
split with (inl _ (t0, l, ap_rC (pairC t1 l) ct));
econstructor; simpl.
f_equal...
change (dec_by_cls (pairC t0 l) (ap_rC (pairC t1 l) ct : contextC) (inl _ (t0, l, ap_rC (pairC t1 l) ct))); constructor.
Defined.

Definition unfold_c_cls :
forall (v : valueC) (ct : contextC) (cl : closure) (ct0 : context),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_term cl ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct0 p}.
Proof with auto.
intros v ct; case ct; intros; simpl; discriminate.
Defined.

Definition unfold_cls :
forall (cl : closureC) (ct : contextC) (cl0 : closure) (ct0 : context),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_term cl0 ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl0 ct0 p}.
Proof with auto.
intro cl; case cl; [intro t; case t | idtac]; intros; simpl; discriminate.
Defined.

Lemma dec_Val :
forall t s (ct : contextC) c v,
  dec_term (closureC_to_closure (pairC t s)) (contextC_to_context ct) = in_val v c ->
  exists v0 : valueC, exists ct1 : contextC,
    (valueC_to_value v0) = v /\ c = (contextC_to_context ct1).
Proof with auto.
intro t; case t; intros; simpl in *; discriminate.
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
induction c; intros; simpl in *...
assert (hh := IHc _ _ _ H).
inversion hh; simpl in H0; try discriminate.
injection H0; intros; subst...
Qed.

Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
Proof with eauto.
induction c; intros; simpl in *...
apply IHc; econstructor 3...
simpl...
Qed.

End CallByName.

Module CBN_EAM := ProperEAMachine (CallByName).
Module CBN_Eval := Evaluator (CallByName).
Definition eval_CBN := CBN_Eval.eval.
Definition eval_CBN_EAM := CBN_EAM.E.eval.

Lemma eval_equiv : forall t v, eval_CBN t v <-> eval_CBN_EAM t v.
Proof with eauto.
intros; split; intros; inversion_clear H; inversion_clear H0;
econstructor; try (econstructor; eauto; fail);
clear H; induction H1; try (constructor; fail);
inversion_clear H0; econstructor; eauto; constructor...
Qed.

Section EAMachine.

Definition term := CallByName.term.
Definition closureC := CallByName.closureC.
Definition substC := CallByName.substitutionC.
Definition contextC := CallByName.contextC.
Definition valueC := CallByName.valueC.
Definition value := CallByName.value.
Definition emptyC := CallByName.emptyC.
Definition v_lamC := CallByName.v_lamC.
Definition var := CallByName.var.
Definition lam := CallByName.lam.
Definition appl := CallByName.appl.
Definition ap_rC := CallByName.ap_rC.
Definition subst := CallByName.substitution.
Definition context := CallByName.context.
Definition closure := CallByName.closure.
Definition pairC := CallByName.pairC.

Definition closureC_to_closure (cl:closureC) : closure := CallByName.closureC_to_closure cl.
Definition substC_to_subst (s : substC) : subst := CallByName.subC_to_sub s.
Definition valueC_to_value (v : valueC) : value := CallByName.valueC_to_value v.
Definition contextC_to_context (ct : contextC) : context := CallByName.contextC_to_context ct.

Coercion closureC_to_closure : closureC >-> closure.
Coercion substC_to_subst : substC >-> subst.
Coercion valueC_to_value : valueC >-> value.
Coercion contextC_to_context : contextC >-> context.

Definition nth_option := CallByName.nth_option.
Definition beta_plus := CallByName.beta_plus.
Definition contract := CallByName.contract.

Definition configuration := CBN_EAM.configuration.
Definition c_init := CBN_EAM.c_init.
Definition c_eval := CBN_EAM.c_eval.
Definition c_apply := CBN_EAM.c_apply.
Definition c_final := CBN_EAM.c_final.

Inductive transition : configuration -> configuration -> Prop :=
| t_init : forall (t : term), transition (c_init t) (c_eval t nil emptyC)
| t_lam_u: forall (t : term) (n : nat) (s : substC) (v : valueC) (ct ct0 : contextC),
             beta_plus (ct:context) n (s:subst) nil t = (closureC_to_closure (CallByName.valueC_to_closureC v), ct0:context) ->
             transition (c_eval (lam n t) s ct) (c_apply ct0 v)
| t_lam_r: forall (t t0 : term) (n : nat) (s s0 : substC) (ct ct0 : contextC),
             beta_plus (ct : context) n (s:subst) nil t = (closureC_to_closure (pairC t0 s0), ct0:context) ->
             transition (c_eval (lam n t) s ct) (c_eval t0 s0 ct0)
| t_varP : forall (n:nat) (s s0:substC) (c c0:contextC) (t:term),
             nth_option (s:subst) n (c:context) = Some (closureC_to_closure (pairC t s0), c0:context) ->
             transition (c_eval (var n) s c) (c_eval t s0 c0)
| t_varC : forall (n:nat) (s:substC) (c c1:contextC) (v : valueC),
             nth_option (s:subst) n (c:context) = Some (closureC_to_closure (CallByName.valueC_to_closureC v), c1:context) ->
             transition (c_eval (var n) s c) (c_apply c1 v)
| t_app  : forall (t0 t1:term) (s:substC) (c:contextC),
             transition (c_eval (appl t0 t1) s c) (c_eval t0 s (ap_rC (pairC t1 s) c))
| t_mt   : forall (v : valueC), transition (c_apply emptyC v) (c_final v)
| t_ap_v : forall (n : nat) (t : term) (s l : substC) (cl : closureC) (v : valueC) (ct ct0: contextC),
             beta_plus (contextC_to_context (ap_rC cl ct)) n (s:subst) (l:subst) t = (closureC_to_closure (CallByName.valueC_to_closureC v), ct0 : context) ->
             transition (c_apply (ap_rC cl ct) (v_lamC n t s l)) (c_apply ct0 v)
| t_ap_r : forall (n : nat) (t t0 : term) (s l s0 : substC) (cl : closureC) (ct ct0: contextC),
             beta_plus (contextC_to_context (ap_rC cl ct)) n (s:subst) (l:subst) t = (closureC_to_closure (pairC t0 s0), ct0 : context) ->
             transition (c_apply (ap_rC cl ct) (v_lamC n t s l)) (c_eval t0 s0 ct0).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step : forall w w' : configuration, 
               transition w w' -> trans_close w w'
| mul_step : forall w w' w'' : configuration, 
               transition w w' -> trans_close w' w'' -> trans_close w w''.

Inductive eval : term -> valueC -> Prop :=
| e_k_intro : forall (t : term) (v : valueC), trans_close (c_init t) (c_final v) -> eval t v.

Definition dec_term := CallByName.dec_term.
Definition dec_context := CallByName.dec_context.
Definition in_dec := CallByName.in_dec.
Definition d_red := CallByName.d_red.
Definition redex := CallByName.redex.
Definition dec_by_cls := CallByName.dec_by_cls.

Lemma unf_red_correct : forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure)
  (H : dec_term (cl:closure) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl0, ct1)),
  dec_by_cls cl0 ct1 (CBN_EAM.UEAM.unf_red cl ct r ct0 ct1 cl0 H H1).
Proof with auto.
intros; unfold CBN_EAM.UEAM.unf_red; simpl in *.
remember (CallByName.unfold_red cl ct r ct0 ct1 cl0 H H1).
destruct s as [p q]...
Qed.

Lemma unf_c_red_correct : forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl, ct1)),
  dec_by_cls cl ct1 (CBN_EAM.UEAM.unf_c_red v ct r ct0 ct1 cl H H1).
Proof with auto.
intros; unfold CBN_EAM.UEAM.unf_c_red; simpl in *.
remember (CallByName.unfold_c_red v ct r ct0 ct1 cl H H1).
destruct s as [p q]...
Qed.

Lemma transition_unf_k : forall c0 c1, CBN_EAM.transition c0 c1 -> transition c0 c1.
Proof with eauto.
induction 1; try (induction t; discriminate); try (induction c; discriminate).
(* Case 1 (init) *)
constructor.
(* Case 2 (eval -> d_red -> eval) *)
assert (dec_by_cls cl c1 (inl (CBN_EAM.UEAM.valueC * CBN_EAM.UEAM.contextC) (t0, s0, c2))).
rewrite <- H0; apply unf_red_correct.
clear H0; induction t; simpl in H.
(* Case 2.1 (r_get) *)
inversion H; subst r c0; clear H.
simpl in H1; assert (ht := CallByName.getC _ _ _ _ _ H1).
destruct ht as [[cl2 ct2] [ht hq]]; subst.
inversion H2; subst.
apply CallByName.contextC_to_context_injective in H; subst ct2.
change (closureC_to_closure (pairC t0 s0) = closureC_to_closure cl2) in H0.
apply CallByName.closureC_to_closure_injective in H0; subst cl2.
constructor...
simpl in *.
induction cl2; try discriminate.
induction t; discriminate.
(* Case 2.2 (r_lam) *)
inversion H; subst r c0; clear H.
simpl in H1; inversion H1; clear H1.
change (beta_plus (contextC_to_context c) n (CallByName.subC_to_sub s) (CallByName.subC_to_sub nil) t = (cl, c1)) in H0;
assert (ht := CallByName.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ht hq]; subst.
inversion H2; subst.
apply CallByName.contextC_to_context_injective in H; subst ct2.
change (closureC_to_closure (pairC t0 s0) = closureC_to_closure cl2) in H1.
apply CallByName.closureC_to_closure_injective in H1; subst cl2.
constructor...
simpl in *.
induction cl2; try discriminate.
induction t1; discriminate.
(* Case 2.3 (r_app) *)
clear IHt1 IHt2.
inversion H; subst r c0; clear H.
simpl in *; inversion H1; rewrite <- H0 in H2; clear H0 H1.
inversion H2; subst.
inversion H; subst.
inversion H0; subst; clear H2 H.
change (CallByName.contextC_to_context c2 = CallByName.contextC_to_context (ap_rC (pairC t2 s0) c)) in H5;
apply CallByName.contextC_to_context_injective in H5; subst.
apply CallByName.substC_to_subst_injective in H4; subst.
constructor...
induction t1; discriminate.
(* Case 3 (eval -> red -> apply) *)
assert (dec_by_cls cl c1 (inr (CBN_EAM.UEAM.term * CBN_EAM.UEAM.substC * CBN_EAM.UEAM.contextC) (v, c2))).
rewrite <- H0; apply unf_red_correct.
induction t; simpl in H; try discriminate; inversion H; subst; clear H0 H.
(* Case 3.1 (r_get) *)
simpl in H1; assert (ht := CallByName.getC _ _ _ _ _ H1).
destruct ht as [[cl2 ct2] [ht hq]]; subst.
inversion H2; subst; simpl in *.
apply CallByName.contextC_to_context_injective in H0;
apply CallByName.closureC_to_closure_injective in H; subst cl2 ct2.
constructor...
induction cl2; try (induction t); discriminate.
(* Case 3.2 (r_lam) *)
simpl in H1; inversion H1; clear H1 IHt.
change (beta_plus (CallByName.contextC_to_context c) n (CallByName.subC_to_sub s) (CallByName.subC_to_sub nil) t = (cl, c1)) in H0;
assert (ht := CallByName.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ht hq]; subst.
inversion H2; subst; simpl in *.
apply CallByName.contextC_to_context_injective in H1;
apply CallByName.closureC_to_closure_injective in H; subst cl2 ct2.
constructor...
induction cl2; try (induction t0); discriminate.
(* Case 3.3 (r_app (discriminable)) *)
simpl in H1; inversion H1; subst; clear IHt1 IHt2 H1.
inversion H2; subst.
induction v; discriminate.
simpl in H; inversion H; clear H H2; subst.
inversion H0; subst; clear H0.
induction v; discriminate.
induction t1; discriminate.
(* Case 4 (final) *)
induction c; try discriminate; injection H; intros. clear H.
induction v; induction v0; simpl in *; injection H0; intros; subst.
apply CallByName.substC_to_subst_injective in H1;
apply CallByName.substC_to_subst_injective in H; subst; constructor.
(* Case 5 (apply -> red -> eval) *)
assert (CallByName.dec_by_cls cl c1 (inl (CBN_EAM.UEAM.valueC * CBN_EAM.UEAM.contextC) (t, s, c2))).
rewrite <- H0; apply unf_c_red_correct.
induction v; induction c; try discriminate; simpl in H; inversion H; subst; simpl in H1; clear H0 H IHc.
inversion H1; clear H1.
change (CallByName.beta_plus (CallByName.contextC_to_context (ap_rC c c3)) n (CallByName.subC_to_sub s0) (CallByName.subC_to_sub l) t0 = (cl, c1)) in H0.
assert (ht := CallByName.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
change (closureC_to_closure (pairC t s) = closureC_to_closure cl2) in H1;
apply CallByName.closureC_to_closure_injective in H1;
apply CallByName.contextC_to_context_injective in H; subst.
constructor...
simpl in *; induction cl2; try (induction t1); discriminate.
(* Case 6 (apply -> red -> apply) *)
assert (CallByName.dec_by_cls cl c1 (inr (CBN_EAM.UEAM.term * CBN_EAM.UEAM.substC * CBN_EAM.UEAM.contextC) (v0, c2))).
rewrite <- H0; apply unf_c_red_correct.
induction v; induction c; try discriminate; simpl in H; inversion H; subst; clear H0 H IHc.
inversion H1; clear H1; change (CallByName.beta_plus (CallByName.contextC_to_context (ap_rC c c3)) n (CallByName.subC_to_sub s) (CallByName.subC_to_sub l) t = (cl, c1)) in H0;
assert (ht := CallByName.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst.
apply CallByName.closureC_to_closure_injective in H;
apply CallByName.contextC_to_context_injective in H1; subst.
constructor...
simpl in H; induction cl2; try (induction t0); discriminate.
Qed.
Hint Resolve transition_unf_k.

Lemma trans_close_unf_k : forall c c0, CBN_EAM.trans_close c c0 -> trans_close c c0.
Proof with eauto.
induction 1; [constructor | econstructor 2]...
Qed.
Hint Resolve trans_close_unf_k.

Lemma evalUnfKrivine : forall t v, CBN_EAM.eval t v -> eval t v.
Proof with auto.
intros t v H; constructor; inversion_clear H; inversion H0; inversion H; subst...
Qed.
Hint Resolve evalUnfKrivine.

Lemma transition_k_unf : forall c c0, transition c c0 -> CBN_EAM.transition c c0.
Proof with eauto with ref.
induction 1.
(* Case 1 (init) *)
constructor.
(* Case 2 (r_lam -> apply) *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (lam n t) s) (ct:context) = in_dec (d_red (CallByName.r_lam n t (s:subst)) (ct:context)))...
assert (hb : contract (CallByName.r_lam n t (s:subst)) (ct:context) = Some (closureC_to_closure (CallByName.valueC_to_closureC v), ct0:context)).
simpl; f_equal...
constructor 4 with (ct : context) (ct0 : context) (CallByName.r_lam n t (s:subst)) _ ha hb.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByName.unfold_red as [p peq].
inversion peq; subst; try (destruct v; discriminate).
repeat f_equal...
(* Case 3 (r_lam -> eval) *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (lam n t) s) (ct:context) = in_dec (d_red (CallByName.r_lam n t (s:subst)) (ct:context)))...
assert (hb : contract (CallByName.r_lam n t (s:subst)) (ct:context) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 3 with (ct : context) (ct0 : context) (CallByName.r_lam n t (s:subst)) _ ha hb.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByName.unfold_red as [p peq].
inversion peq; subst.
repeat f_equal...
destruct v; discriminate.
destruct t0; discriminate.
(* Case 4 (r_get -> eval) *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (var n) s) (c:context) = in_dec (d_red (CallByName.r_get n (s:subst)) (c:context)))...
assert (hb : contract (CallByName.r_get n (s:subst)) (c:context) = Some (closureC_to_closure (pairC t s0), c0:context)).
simpl; f_equal...
constructor 3 with (c:context) (c0:context) (CallByName.r_get n (s:subst)) _ ha hb.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByName.unfold_red as [p peq].
inversion peq; subst.
repeat f_equal...
destruct v; discriminate.
destruct t; discriminate.
(* Case 5 (r_get -> apply) *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (var n) s) (c:context) = in_dec (d_red (CallByName.r_get n (s:subst)) (c:context)))...
assert (hb : contract (CallByName.r_get n (s:subst)) (c:context) = Some (closureC_to_closure (CallByName.valueC_to_closureC v), c1:context)).
simpl; f_equal...
constructor 4 with (c : context) (c1 : context) (CallByName.r_get n (s:subst)) _ ha hb.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByName.unfold_red as [p peq].
inversion peq; subst; try (destruct v; discriminate).
repeat f_equal...
(* Case 6 (r_app -> eval) *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (appl t0 t1) s) (c:context) = in_dec (d_red (CallByName.r_app t0 t1 (s:subst)) (c:context)))...
assert (hb : contract (CallByName.r_app t0 t1 (s:subst)) (c:context) = Some (CallByName.comp (closureC_to_closure (pairC t0 s)) (closureC_to_closure (pairC t1 s)),  c:context)).
simpl; f_equal...
constructor 3 with (c:context) (contextC_to_context c) (CallByName.r_app t0 t1 (s:subst)) _ ha hb.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByName.unfold_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
inversion H; subst.
inversion H0; subst; repeat f_equal...
apply CallByName.substC_to_subst_injective in H3; subst...
destruct v; discriminate.
destruct t0; discriminate.
(* Case 7 (final) *)
constructor...
(* Case 8 (apply -> red -> apply) *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (ap_rC cl ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByName.r_beta (valueC_to_value (v_lamC n t s l)) (closureC_to_closure cl)) (contextC_to_context ct)))...
assert (hb : contract (CallByName.r_beta (valueC_to_value(v_lamC n t s l)) (cl:closure)) (ct:context) = Some (closureC_to_closure (CallByName.valueC_to_closureC v), ct0:context)).
simpl; f_equal...
constructor 10 with _ _ (CallByName.r_beta (valueC_to_value (v_lamC n t s l)) (cl:closure)) _ ha hb...
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByName.unfold_c_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* Case 9 (apply -> red -> eval) *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (ap_rC cl ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByName.r_beta (valueC_to_value (v_lamC n t s l)) (closureC_to_closure cl)) (contextC_to_context ct)))...
assert (hb : contract (CallByName.r_beta (valueC_to_value(v_lamC n t s l)) (cl:closure)) (ct:context) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 9 with _ _ (CallByName.r_beta (valueC_to_value (v_lamC n t s l)) (cl:closure)) _ ha hb.
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByName.unfold_c_red as [p peq].
inversion peq; subst; repeat f_equal...
destruct v; discriminate.
destruct t0; discriminate.
Qed.
Hint Resolve transition_k_unf.

Lemma trans_close_k_unf : forall c c0, trans_close c c0 -> CBN_EAM.trans_close c c0.
Proof with eauto.
induction 1; [constructor | econstructor 2]...
Qed.
Hint Resolve trans_close_k_unf.

Lemma evalKrivineUnf : forall t v, eval t v -> CBN_EAM.eval t v.
Proof with auto.
intros t v H; constructor; inversion_clear H; inversion H0; inversion H; subst...
Qed.
Hint Resolve evalKrivineUnf.

Theorem EAMachineCorrect : forall t (v:valueC), eval_CBN t (valueC_to_value v) <-> eval t v.
Proof with auto.
intros; rewrite eval_equiv; rewrite CBN_EAM.evalMachine; split...
Qed.

End EAMachine.