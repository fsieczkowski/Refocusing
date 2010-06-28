Require Import refocusing_environments_cs.
Require Import Setoid.

Module CallByNameCallCC <: RED_LANG.

Inductive term' : Set :=
| var : nat -> term'
| lam : nat -> term' -> term'
| appl : term' -> term' -> term'
| C : term' -> term'.
Definition term := term'.

Inductive closure' : Set :=
| pair' : term -> list closure' -> closure'
| comp  : closure' ->  closure' -> closure'
| u_lam : nat -> term -> list closure' -> list closure' -> closure'
| C_cl  : closure' -> closure'
| C_ct  : context' -> closure'
with context' : Set :=
| mt   : context'
| ap_r : closure' -> context' -> context'
| C_ctx: context' -> context'.
Definition closure := closure'.
Definition substitution := list closure.
Definition pair : term -> substitution -> closure := pair'.

Definition context := context'.
Definition empty : context := mt.

Inductive value' : Set :=
| v_lam : nat -> term -> substitution -> list closure -> value'
| v_cc  : context -> value'.
Definition value := value'.

Inductive redex' : Set :=
| r_beta : value -> closure -> redex'
| r_vct  : value -> redex'
| r_lam  : nat -> term -> substitution -> redex'
| r_get  : nat -> substitution -> redex'
| r_app  : term -> term -> substitution -> redex'
| r_C   : term -> substitution -> redex'.
Definition redex := redex'.

Inductive closureC' : Set :=
| pairC' : term -> list closureC' -> closureC'
| u_lamC : nat -> term -> list closureC' -> list closureC' -> closureC'
| C_ctC  : contextC' -> closureC'
with contextC' : Set :=
| mtC    : contextC'
| ap_rC  : closureC' -> contextC' -> contextC'
| C_ctxC : contextC' -> contextC'.
Definition closureC := closureC'.
Definition substitutionC := list closureC.
Definition pairC : term -> substitutionC -> closureC := pairC'.

Definition contextC := contextC'.
Definition emptyC : contextC := mtC.

Inductive valueC' : Set :=
| v_lamC : nat -> term -> substitutionC -> list closureC -> valueC'
| v_ccC  : contextC -> valueC'.
Definition valueC := valueC'.

Inductive redexC' : Set :=
| r_betaC : valueC -> closureC -> redexC'
| r_vctC  : valueC -> redexC'
| r_lamC  : nat -> term -> substitutionC -> redexC'.
Definition redexC := redexC'.

Fixpoint plug (cl : closure) (ct : context) {struct ct} : closure :=
match ct with
| empty => cl
| ap_r cl0 ct0 => plug (comp cl cl0) ct0
| C_ctx ct => plug (C_cl cl) ct
end.

Fixpoint compose (ct : context) (ct0 : context) {struct ct} : context :=
match ct with
| empty => ct0
| ap_r cl ct' => ap_r cl (compose ct' ct0)
| C_ctx ct => C_ctx (compose ct ct0)
end.

Fixpoint composeC (ct : contextC) (ct0 : contextC) {struct ct} : contextC :=
match ct with
| emptyC => ct0
| ap_rC cl ct' => ap_rC cl (composeC ct' ct0)
| C_ctxC ct => C_ctxC (composeC ct ct0)
end.

Definition value_to_closure : value -> closure :=
fun v => match v with
| v_lam n t s l => u_lam n t s l
| v_cc ct => C_ct ct
end.
Coercion value_to_closure : value >-> closure.

Definition redex_to_closure : redex -> closure :=
fun r => match r with
| r_beta v cl => comp (v:closure) cl
| r_vct v => C_cl (v:closure)
| r_lam n t s => pair (lam n t) s
| r_get n s => pair (var n) s
| r_app t t0 s => pair (appl t t0) s
| r_C t s => pair (C t) s
end.
Coercion redex_to_closure : redex >-> closure.

Fixpoint closureC_to_closure (cl : closureC) : closure :=
match cl with
| pairC t s => pair t (map closureC_to_closure s)
| u_lamC n t s l => u_lam n t (map closureC_to_closure s) (map closureC_to_closure l)
| C_ctC ct => C_ct (contextC_to_context ct)
end
with contextC_to_context (ct : contextC) : context :=
match ct with
| mtC => mt
| ap_rC clc ctc => ap_r (closureC_to_closure clc) (contextC_to_context ctc)
| C_ctxC ctc => C_ctx (contextC_to_context ctc)
end.
Coercion closureC_to_closure : closureC >-> closure.
Coercion contextC_to_context : contextC >-> context.
Definition subC_to_sub : substitutionC -> substitution := map closureC_to_closure.

Definition valueC_to_value (v : valueC) : value :=
match v with
| v_lamC n t s l => v_lam n t (subC_to_sub s) (subC_to_sub l)
| v_ccC ct => v_cc ct
end.

Definition redexC_to_redex (r : redexC) : redex :=
match r with
| r_betaC v cl => r_beta (valueC_to_value v) (cl : closure)
| r_lamC n t s => r_lam n t (subC_to_sub s)
| r_vctC v => r_vct (valueC_to_value v)
end.

Definition valueC_to_closureC (v : valueC) : closureC :=
match v with
| v_lamC n t s l => u_lamC n t s l
| v_ccC ct => C_ctC ct
end.
Coercion valueC_to_closureC : valueC >-> closureC.

Lemma composeC_compose : forall c c0, contextC_to_context (composeC c c0) = compose (contextC_to_context c) (contextC_to_context c0).
Proof with auto.
induction c; intros; simpl; auto; rewrite IHc...
Qed.

Lemma closureC_ind :
forall (P : closureC' -> Prop) (P0 : contextC' -> Prop),
  (forall (t : term) (l : list closureC'), (forall t0, In t0 l -> P t0) -> P (pairC' t l)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P t0) -> (forall t0, In t0 l -> P t0) -> P (u_lamC n t s l)) ->
  (forall (ct : contextC), P0 ct -> P (C_ctC ct)) ->
  (P0 mtC) ->
  (forall (cl : closureC) (ct : contextC), P cl -> P0 ct -> P0 (ap_rC cl ct)) ->
  (forall (ct : contextC), P0 ct -> P0 (C_ctxC ct)) ->
  forall cl : closureC, P cl.
Proof with eauto.
intros P P0 hPair hULam hCC hMt hAp hCt.
refine (fix IHc (c : closureC') : P c := _ with IHct (ct : contextC') : P0 ct := _ for IHc).
(* closureC *)
case c.
(* pairC *)
intros.
apply hPair.
induction l; intros; destruct H;
[ rewrite <- H; apply IHc | apply IHl; fold (In t0 l) in H; apply H].
(* u_lamC *)
intros; apply hULam.
induction l; intros; destruct H;
[ rewrite <- H; apply IHc | apply IHl; fold (In t0 l) in H; apply H].
induction l0; intros; destruct H;
[ rewrite <- H; apply IHc | apply IHl0; fold (In t0 l0) in H; apply H].
(* ccC *)
intro c0; apply hCC; apply IHct.
(* contextC *)
case ct; intros.
(* emptyC *)
apply hMt.
(* ap_rC *)
apply hAp; [ apply IHc | apply IHct].
(* ccctC *)
apply hCt; apply IHct.
Qed.

Lemma contextC_ind :
forall (P : contextC' -> Prop) (P0 : closureC' -> Prop),
  (P mtC) ->
  (forall (cl : closureC) (ct : contextC), P0 cl -> P ct -> P (ap_rC cl ct)) ->
  (forall (ct : contextC), P ct -> P (C_ctxC ct)) ->
  (forall (t : term) (l : list closureC'), (forall t0, In t0 l -> P0 t0) -> P0 (pairC' t l)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P0 t0) -> (forall t0, In t0 l -> P0 t0) -> P0 (u_lamC n t s l)) ->
  (forall (ct : contextC), P ct -> P0 (C_ctC ct)) ->
  forall ct : contextC, P ct.
Proof with auto.
intros P P0 hMt hAp hCt hPair hULam hCC.
refine (fix IHct (ct : contextC') : P ct := _ with IHc (c : closureC') : P0 c := _ for IHct).
(* contextC *)
case ct; intros.
(* emptyC *)
apply hMt.
(* ap_rC *)
apply hAp; [apply IHc | apply IHct].
(* ccctC *)
apply hCt; apply IHct.
(* closureC *)
case c; intros.
(* pairC *)
apply hPair.
induction l; intros; destruct H;
[ rewrite <- H; apply IHc | apply IHl; fold (In t0 l) in H; apply H].
(* u_lamC *)
apply hULam.
induction l; intros; destruct H;
[ rewrite <- H; apply IHc | apply IHl; fold (In t0 l) in H; apply H].
induction l0; intros; destruct H;
[ rewrite <- H; apply IHc | apply IHl0; fold (In t0 l0) in H; apply H].
(* ccC *)
apply hCC; apply IHct.
Qed.

Lemma in_list_lemma : 
  forall l l0 : list closureC',
  (forall t1 : closureC',
    In t1 l ->
    forall cl0 : closureC,
    closureC_to_closure t1 = closureC_to_closure cl0 -> t1 = cl0) ->
  map closureC_to_closure l = map closureC_to_closure l0 -> l = l0.
Proof with auto.
intros; generalize dependent l0.
induction l; intros; destruct l0.
reflexivity.
discriminate.
discriminate.
simpl in *.
f_equal.
inversion H0.
apply H; try left...
apply IHl; intros.
apply H; try right...
inversion H0; reflexivity. 
Qed.
Hint Resolve in_list_lemma : ref.

Lemma closureC_to_closure_injective : forall (cl cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0.
Proof with auto with ref.
induction cl using closureC_ind with
(P0:= fun ct => forall ct0 : contextC, contextC_to_context ct = contextC_to_context ct0 -> ct = ct0);
intros; try destruct cl0; try destruct ct0; try discriminate;
[inversion H0 | inversion H1 | inversion H | idtac | inversion H | inversion H]; f_equal...
Qed.
Hint Resolve closureC_to_closure_injective : ref.

Lemma contextC_to_context_injective : forall (ct ct0 : contextC), contextC_to_context ct = contextC_to_context ct0 -> ct = ct0.
Proof with auto with ref.
induction ct using contextC_ind with
(P0 := fun cl => forall (cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0);
intros; try destruct cl0; try destruct ct0; try discriminate;
[idtac | inversion H | inversion H | inversion H0 | inversion H1 | inversion H]; f_equal...
Qed.
Hint Resolve contextC_to_context_injective : ref.

Lemma substC_to_subst_injective : forall (s s0 : substitutionC), subC_to_sub s = subC_to_sub s0 -> s = s0.
Proof with auto with ref.
induction s; intro s0; case s0; intros; try discriminate; inversion H; f_equal...
Qed.
Hint Resolve substC_to_subst_injective : ref.

Lemma valueC_to_value_injective : forall (v v0 : valueC), valueC_to_value v = valueC_to_value v0 -> v = v0.
Proof with auto with ref.
induction v; induction v0; intros; try discriminate; inversion H; f_equal...
Qed.
Hint Resolve valueC_to_value_injective : ref.

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
  | 0 => (pair t (l ++ s), c)
  | S m => match c with
    | ap_r cl ct => beta_plus ct m s (cl :: l) t
    | C_ctx ct => beta_plus ct m s (C_ct ct :: l) t
    | _ => (u_lam n t s l, c)
    end
  end.

Definition contract (r : redex) (ct : context) : option (closure * context) :=
  match r with
    | r_beta (v_lam n t s l) cl => Some (beta_plus (ap_r cl ct) n s l t)
    | r_beta (v_cc ct0) cl => Some (cl, ct0)
    | r_lam n t s => Some (beta_plus ct n s nil t)
    | r_vct (v_lam n t s l) => Some (beta_plus (C_ctx ct) n s l t)
    | r_vct (v_cc ct0) => Some (comp (C_ct ct0) (C_ct ct), ct)
    | r_get n s => nth_option s n ct
    | r_app t0 t1 s => Some (comp (pair t0 s) (pair t1 s), ct)
    | r_C t s => Some (C_cl (pair t s), ct)
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
    (exists r:redex, exists c:context, plug (redex_to_closure r) c = cl).
Proof with auto.
induction cl; intros.
(* pair *)
case t; intros; right.
exists (r_get n l); exists empty...
exists (r_lam n t0 l); exists empty...
exists (r_app t0 t1 l); exists empty...
exists (r_C t0 l); exists empty...
(* comp *)
inversion_clear IHcl1; right.
destruct H as [v H]; exists (r_beta v cl2); exists empty; subst...
destruct H as [r [c H]]; exists r; exists (compose c (ap_r cl2 empty)); rewrite plug_compose; subst...
(* u_lam *)
left; exists (v_lam n t l l0)...
(* C_cl *)
elim IHcl; intros; right; clear IHcl.
destruct H as [v H]; exists (r_vct v); exists empty; subst...
destruct H as [r [c H]]; exists r; exists (compose c (C_ctx empty)); rewrite plug_compose; subst...
(* C_ct *)
left; exists (v_cc c)...
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
| pair (C t) s => in_dec (d_red (r_C t s) ct)
| u_lam n t s l => in_val (v_lam n t s l) ct
| comp cl0 cl1 => in_term cl0 (ap_r cl1 ct)
| C_cl cl => in_term cl (C_ctx ct)
| C_ct ct' => in_val (v_cc ct') ct
end.

Definition dec_context (v : value) (ct : context) : interm_dec :=
match ct with 
| empty => in_dec (d_val v)
| ap_r cl ct' => in_dec (d_red (r_beta v cl) ct')
| C_ctx ct' => in_dec (d_red (r_vct v) ct')
end.

Lemma dec_context_empty : forall (v : value), dec_context v empty = in_dec (d_val v).
Proof.
auto.
Qed.
Lemma dec_context_left_only : forall v (c:contextC), exists d, dec_context v c = in_dec d.
Proof with auto.
intros v c; case c; intros.
exists (d_val v)...
exists (d_red (r_beta v (c0:closureC)) (c1:contextC))...
exists (d_red (r_vct v) (c0:contextC))...
Qed.
Lemma dec_term_value : forall (v : value) (c : context), dec_term (value_to_closure v) c = in_val v c.
Proof.
intro v; case v; simpl; auto.
Qed.
Hint Resolve dec_term_value : ref.

Lemma getC : forall l i (c : contextC) r c0, nth_option (map closureC_to_closure l) i c = Some (r, c0) ->
    {q:closureC * contextC | r = closureC_to_closure (fst q) /\ c0 = snd q}.
Proof.
induction l; induction i; simpl; intros; try discriminate.
split with (a, c).
inversion H; subst; simpl; auto.
eapply IHl; eapply H.
Qed.

Lemma getB :
  forall n (ct : contextC) (s l:substitutionC) r t ct', 
    beta_plus ct n (subC_to_sub s) (subC_to_sub l) t = (r, ct') -> 
    {p : (closureC * contextC) | (fst p:closure) = r & (snd p:context) = ct'}.
Proof with eauto.
induction n; induction ct; intros; simpl in H; try discriminate.
inversion H; subst; split with (pairC t (l++s), emptyC); simpl; f_equal; auto;
unfold subC_to_sub; apply map_app.
inversion H; subst; split with (pairC t (l++s), ap_rC c ct); simpl; f_equal;
unfold subC_to_sub; apply map_app.
inversion H; subst; split with (pairC t (l++s), C_ctxC ct); simpl; f_equal;
unfold subC_to_sub; apply map_app.
inversion H; subst; split with (u_lamC (S n) t s l, emptyC); simpl; f_equal...
eapply IHn with _ _ (c :: l) _...
apply IHn with ct s (C_ctC ct :: l) t; simpl...
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

Lemma dec_by_cls_folds_left : forall t s ct cl c, dec_by_cls cl c (inl _ (t, s, ct)) -> plug cl c = plug (pairC t s:closureC) ct.
Proof with auto.
induction cl; intros; inversion_clear H; try (induction t0; discriminate)...
inversion H0; subst; apply (IHcl1 _ H1).
inversion H0; subst; apply (IHcl _ H1).
simpl in H0; discriminate.
Qed.

Lemma dec_by_cls_folds_right : forall v ct cl c, dec_by_cls cl c (inr _ (v, ct)) -> plug cl c = plug (v:closure) ct.
Proof with auto.
induction cl; intros; inversion_clear H; try (induction t; discriminate)...
inversion H0; subst; apply (IHcl1 _ H1).
inversion H0; subst; apply (IHcl _ H1).
simpl in H0; discriminate.
Qed.

Lemma valueC_to_closureC_injective : forall (v v0 : valueC), valueC_to_closureC v = valueC_to_closureC v0 -> v = v0.
Proof with auto.
destruct v; destruct v0; intros; simpl in H; try discriminate; injection H; intros; subst...
Qed.
Hint Resolve valueC_to_closureC_injective : ref.

Lemma dec_by_cls_function : forall cl c p p', dec_by_cls cl c p -> dec_by_cls cl c p' -> p = p'.
Proof with eauto with ref.
induction cl; intros; inversion H; inversion H0; subst; intros; try discriminate; try (destruct t; discriminate); try (destruct v; discriminate)...
repeat f_equal...
injection H1; intros; subst cl' c'; injection H6; intros; subst cl'0 c'0; clear H1 H6; eapply IHcl1...
rewrite <- H5 in H1; repeat f_equal...
injection H1; injection H6; intros; subst cl' c' cl'0 c'0; eapply IHcl...
rewrite <- H5 in H1; repeat f_equal...
Qed.

Definition un_cls_help (cl : closureC) (ct : contextC) : {p : (term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct p}.
Proof with auto.
destruct cl; intros.
split with (inl _ (t, l, ct)); constructor.
constructor 1 with (inr _ (v_lamC n t l l0, ct));
change (dec_by_cls (valueC_to_closureC (v_lamC n t l l0)) ct (inr _ (v_lamC n t l l0, ct))); constructor.
intros t0 s eq; discriminate.
constructor 1 with (inr _ ((v_ccC c), ct));
change (dec_by_cls (valueC_to_closureC (v_ccC c)) ct (inr _ (v_ccC c, ct))); constructor.
intros t s eq; discriminate.
Defined.

Definition unfold_c_red (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) ct = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl, ct1)) :
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct1 p}.
Proof with auto.
intros v ct; case ct; intros; simpl in *; try discriminate;
injection H; intros; subst; clear H;
induction v; injection H1; intros; subst; clear H1.
change (beta_plus (contextC_to_context (ap_rC c c0)) n (subC_to_sub s) (subC_to_sub l) t = (cl, ct1)) in H;
apply getB in H; destruct H as [[cl2 ct2] hf ht]; subst; apply un_cls_help.
apply un_cls_help.
change (beta_plus (contextC_to_context (C_ctxC c)) n (subC_to_sub s) (subC_to_sub l) t = (cl, ct1)) in H;
apply getB in H; destruct H as [[cl2 ct2] hf ht]; subst; apply un_cls_help.
split with (inr _ (v_ccC c0, ap_rC (C_ctC c) c)); econstructor 3; simpl...
change (dec_by_cls (valueC_to_closureC (v_ccC c0)) (contextC_to_context (ap_rC (C_ctC c) c)) (inr _ (v_ccC c0, (ap_rC (C_ctC c) c)))); constructor.
intros t s eq; discriminate.
Defined.

Definition unfold_c_cls (v : valueC) (ct : contextC) (cl : closure) (ct0 : context)
  (H : dec_context (valueC_to_value v) ct = in_term cl ct0) : {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct0 p}.
Proof with auto.
intros v ct; case ct; intros; simpl in *; discriminate.
Defined.

Definition unfold_cls :
forall (cl : closureC) (ct : contextC) (cl0 : closure) (ct0 : context),
  (dec_term cl ct = in_term cl0 ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl0 ct0 p}.
Proof with auto.
intro cl; case cl; intro t; case t; intros; discriminate.
Defined.

Definition unfold_red (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure)
  (H : dec_term cl ct = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl0, ct1)) :
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl0 ct1 p}.
Proof with auto.
intro cl; case cl; intro t; case t; intros; simpl in *; try discriminate;
injection H; intros; subst; clear H.
simpl in H1; apply getC in H1; destruct H1 as [[cl2 ct2] [e1 e2]]; simpl in *; subst.
apply un_cls_help.
injection H1; intros; subst; clear H1.
change (beta_plus ct n (subC_to_sub l) (subC_to_sub nil) t0 = (cl0, ct1)) in H; apply getB in H;
destruct H as [[cl2 ct2] H H0]; subst; simpl; apply un_cls_help.
injection H1; intros; subst; clear H1.
constructor 1 with (inl _ (t0, l, ap_rC (pairC t1 l) ct)); econstructor; simpl; eauto.
change (dec_by_cls (pairC t0 l:closureC) (ap_rC (pairC t1 l) ct:contextC) (inl _ (t0, l, ap_rC (pairC t1 l) ct))); constructor.
injection H1; intros; subst; clear H1.
constructor 1 with (inl _ (t0, l, C_ctxC ct)); econstructor; simpl; eauto.
change (dec_by_cls (pairC t0 l:closureC) (C_ctxC ct:contextC) (inl _ (t0, l, C_ctxC ct))); constructor.
Defined.

Lemma dec_Val :
forall t s (ct : contextC) c v,
  dec_term (closureC_to_closure (pairC t s)) ct = in_val v c ->
  exists v0 : valueC, exists ct1 : contextC,
    (valueC_to_value v0) = v /\ c = ct1.
Proof with auto.
intros; induction t; discriminate.
Qed.

Lemma dec_c_Val :
forall v (ct : contextC) v0 c,
  dec_context (valueC_to_value v) (ct : context) = in_val v0 c ->
  exists ct0 : contextC, exists v1 : valueC, (valueC_to_value v1) = v0 /\ c = ct0.
Proof with auto.
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

Scheme dec_Ind := Induction for dec Sort Prop
with decctx_Ind := Induction for decctx Sort Prop.

Definition decomp_to_term (d : decomp) : closure :=
match d with
  | d_val v => value_to_closure v
  | d_red r c0 => plug (redex_to_closure r) c0
end.

Lemma dec_term_correct : forall t c, match dec_term t c with
  | in_dec d => decomp_to_term d = plug t c
  | in_val v c0 => plug (value_to_closure v) c0 = plug t c
  | in_term t0 c0 => plug t0 c0 = plug t c
end.
Proof.
induction t; try induction t; simpl; auto.
Qed.

Lemma dec_context_correct : forall v c, match dec_context v c with
  | in_dec d => decomp_to_term d = plug (value_to_closure v) c
  | in_val v0 c0 => plug (value_to_closure v0) c0 = plug (value_to_closure v) c
  | in_term t c0 => plug t c0 = plug (value_to_closure v) c
end.
Proof.
induction c; simpl; auto.
Qed.

Lemma dec_plug : forall c c0 t d, dec (plug t c) c0 d -> dec t (compose c c0) d.
Proof with auto.
induction c; intros; simpl...
apply IHc in H; inversion H; inversion H0; subst...
apply IHc in H; inversion H; subst; try discriminate.
injection H0; intros; subst...
Qed.

Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
Proof.
induction c; simpl; intros; auto.
apply IHc; econstructor 3; simpl; eauto.
apply IHc; econstructor 3; simpl; eauto.
Qed.

Lemma dec_redex_self : forall (r:redex) c, dec r c (d_red r c).
Proof with eauto.
induction r; simpl; intros; try (constructor; simpl; auto; fail);
econstructor 3; simpl; try reflexivity;
econstructor 2; try eapply dec_term_value; constructor...
Qed.

End CallByNameCallCC.

Module CBN_EAM := ProperEAMachine (CallByNameCallCC).
Module CBN_Eval := Evaluator (CallByNameCallCC).
Definition eval_CBN := CBN_Eval.eval.
Definition eval_CBN_EAM := CBN_EAM.E.eval.

Lemma eval_equiv : forall t v, eval_CBN t v <-> eval_CBN_EAM t v.
Proof with eauto.
intros; split; intros; inversion_clear H; inversion_clear H0;
econstructor; try (econstructor; eauto; fail);
clear H; induction H1; try (constructor; fail);
inversion_clear H0; econstructor; eauto; constructor...
Qed.

Module KrivineMachineWCallCC.

Definition term := CallByNameCallCC.term.
Definition closureC := CallByNameCallCC.closureC.
Definition substC := CallByNameCallCC.substitutionC.
Definition contextC := CallByNameCallCC.contextC.
Definition valueC := CallByNameCallCC.valueC.
Definition value := CallByNameCallCC.value.
Definition emptyC := CallByNameCallCC.emptyC.
Definition v_lamC := CallByNameCallCC.v_lamC.
Definition v_ccC := CallByNameCallCC.v_ccC.
Definition var := CallByNameCallCC.var.
Definition lam := CallByNameCallCC.lam.
Definition appl := CallByNameCallCC.appl.
Definition C := CallByNameCallCC.C.
Definition ap_rC := CallByNameCallCC.ap_rC.
Definition C_ctxC := CallByNameCallCC.C_ctxC.

Definition subst := CallByNameCallCC.substitution.
Definition context := CallByNameCallCC.context.
Definition closure := CallByNameCallCC.closure.
Definition pairC := CallByNameCallCC.pairC.
Definition u_lamC := CallByNameCallCC.u_lamC.
Definition C_ctC := CallByNameCallCC.C_ctC.

Definition closureC_to_closure (cl:closureC) : closure := CallByNameCallCC.closureC_to_closure cl.
Definition substC_to_subst (s : substC) : subst := CallByNameCallCC.subC_to_sub s.
Definition valueC_to_value (v : valueC) : value := CallByNameCallCC.valueC_to_value v.
Definition contextC_to_context (ct : contextC) : context := CallByNameCallCC.contextC_to_context ct.

Coercion closureC_to_closure : closureC >-> closure.
Coercion substC_to_subst : substC >-> subst.
Coercion valueC_to_value : valueC >-> value.
Coercion contextC_to_context : contextC >-> context.

Definition nth_option := CallByNameCallCC.nth_option.
Definition beta_plus := CallByNameCallCC.beta_plus.
Definition contract := CallByNameCallCC.contract.

Definition configuration := CBN_EAM.configuration.
Definition c_init := CBN_EAM.c_init.
Definition c_eval := CBN_EAM.c_eval.
Definition c_apply := CBN_EAM.c_apply.
Definition c_final := CBN_EAM.c_final.

Definition dec_term := CallByNameCallCC.dec_term.
Definition dec_context := CallByNameCallCC.dec_context.
Definition in_dec := CallByNameCallCC.in_dec.
Definition d_red := CallByNameCallCC.d_red.
Definition redex := CallByNameCallCC.redex.
Definition dec_by_cls := CallByNameCallCC.dec_by_cls.

Lemma unf_red_correct : forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure)
  (H : dec_term (cl:closure) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl0, ct1)),
  dec_by_cls cl0 ct1 (CBN_EAM.UEAM.unf_red cl ct r ct0 ct1 cl0 H H1).
Proof with auto.
intros; unfold CBN_EAM.UEAM.unf_red; simpl in *.
remember (CallByNameCallCC.unfold_red cl ct r ct0 ct1 cl0 H H1).
destruct s as [p q]...
Qed.

Lemma unf_c_red_correct : forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl, ct1)),
  dec_by_cls cl ct1 (CBN_EAM.UEAM.unf_c_red v ct r ct0 ct1 cl H H1).
Proof with auto.
intros; unfold CBN_EAM.UEAM.unf_c_red; simpl in *.
remember (CallByNameCallCC.unfold_c_red v ct r ct0 ct1 cl H H1).
destruct s as [p q]...
Qed.

Inductive transition : configuration -> configuration -> Prop :=
| t_init : forall (t : term), transition (c_init t) (c_eval t nil emptyC)
| t_lamC : forall (t : term) (n : nat) (s : substC) (ct ct0 : contextC) (v : valueC),
             beta_plus (ct:context) n (s:subst) nil t = (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v), ct0:context) ->
             transition (c_eval (lam n t) s ct) (c_apply ct0 v)
| t_lamP: forall (t t0 : term) (n : nat) (s s0 : substC) (ct ct0 : contextC),
             beta_plus (ct : context) n (s:subst) nil t = (closureC_to_closure (pairC t0 s0), ct0:context) ->
             transition (c_eval (lam n t) s ct) (c_eval t0 s0 ct0)
| t_varP : forall (n:nat) (s s0:substC) (c c0:contextC) (t:term),
             nth_option (s:subst) n (c:context) = Some (closureC_to_closure (pairC t s0), c0:context) ->
             transition (c_eval (var n) s c) (c_eval t s0 c0)
| t_varC : forall (n:nat) (s:substC) (c c1:contextC) (v : valueC),
             nth_option (s:subst) n (c:context) = Some (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v), c1:context) ->
             transition (c_eval (var n) s c) (c_apply c1 v)
| t_app  : forall (t0 t1:term) (s:substC) (c:contextC),
             transition (c_eval (appl t0 t1) s c) (c_eval t0 s (ap_rC (pairC t1 s) c))
| t_kt   : forall (t : term) (s:substC) (c:contextC),
             transition (c_eval (C t) s c) (c_eval t s (C_ctxC c))
| t_mt   : forall (v:valueC), transition (c_apply emptyC v) (c_final v)
| t_betaP: forall (t : term) (n : nat) (s l : substC) (ct ct0 : contextC) (v : valueC),
             ct <> emptyC -> beta_plus (ct:context) n (s:subst) (l:subst) t = (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v), ct0:context) ->
             transition (c_apply ct (v_lamC n t s l)) (c_apply ct0 v)
| t_betaC: forall (n:nat) (t t0:term) (s l s0:substC) (ct ct0:contextC),
             ct <> emptyC -> beta_plus (ct:context) n (s:subst) (l:subst) t = (closureC_to_closure (pairC t0 s0), ct0:context) ->
             transition (c_apply ct (v_lamC n t s l)) (c_eval t0 s0 ct0)
| t_apCP : forall (t:term) (s:substC) (ct ct0:contextC),
             transition (c_apply (ap_rC (pairC t s) ct) (v_ccC ct0)) (c_eval t s ct0)
| t_apCC : forall (ct ct0 : contextC) (v : valueC),
             transition (c_apply (ap_rC (CallByNameCallCC.valueC_to_closureC v) ct) (v_ccC ct0)) (c_apply ct0 v)
| t_apCV : forall (ct ct0 : contextC),
             transition (c_apply (C_ctxC ct) (v_ccC ct0)) (c_apply (ap_rC (C_ctC ct) ct) (v_ccC ct0)).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step : forall w w' : configuration, 
               transition w w' -> trans_close w w'
| mul_step : forall w w' w'' : configuration, 
               transition w w' -> trans_close w' w'' -> trans_close w w''.

Inductive eval : term -> valueC -> Prop :=
| e_k_intro : forall (t : term) (v : valueC), trans_close (c_init t) (c_final v) -> eval t v.

Lemma transition_unf_k : forall c0 c1, CBN_EAM.transition c0 c1 -> transition c0 c1.
Proof with eauto.
induction 1; try (induction t; discriminate); try (induction c; discriminate).
(* init *)
constructor.
(* eval -> red -> eval *)
assert (dec_by_cls cl c1 (inl (CBN_EAM.UEAM.valueC * CBN_EAM.UEAM.contextC) (t0, s0, c2)));
[rewrite <- H0; apply unf_red_correct | clear H0];
induction t; simpl in H.
(* var *)
inversion H; subst r c0; clear H.
simpl in H1; assert (ht := CallByNameCallCC.getC _ _ _ _ _ H1).
destruct ht as [[cl2 ct2] [ht hq]]; subst.
inversion H2; subst.
apply CallByNameCallCC.contextC_to_context_injective in H; subst ct2.
change (closureC_to_closure (pairC t0 s0) = closureC_to_closure cl2) in H0.
apply CallByNameCallCC.closureC_to_closure_injective in H0; subst cl2.
constructor...
simpl in *.
induction cl2; try discriminate.
induction t; discriminate.
(* lam *)
inversion H; subst r c0; clear H.
simpl in H1; inversion H1; clear H1.
change (beta_plus (contextC_to_context c) n (CallByNameCallCC.subC_to_sub s) (CallByNameCallCC.subC_to_sub nil) t = (cl, c1)) in H0;
assert (ht := CallByNameCallCC.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ht hq]; subst.
inversion H2; subst.
apply CallByNameCallCC.contextC_to_context_injective in H; subst ct2.
change (closureC_to_closure (pairC t0 s0) = closureC_to_closure cl2) in H1.
apply CallByNameCallCC.closureC_to_closure_injective in H1; subst cl2.
constructor...
simpl in *.
induction cl2; try discriminate.
induction t1; discriminate.
(* appl *)
inversion H; subst r c0; clear H IHt1 IHt2.
simpl in *; inversion H1; rewrite <- H0 in H2; clear H0 H1.
inversion H2; subst.
inversion H; subst.
inversion H0; subst; clear H2 H.
change (CallByNameCallCC.contextC_to_context c2 = CallByNameCallCC.contextC_to_context (ap_rC (pairC t2 s0) c)) in H5;
apply CallByNameCallCC.contextC_to_context_injective in H5; subst.
apply CallByNameCallCC.substC_to_subst_injective in H4; subst.
constructor...
induction t1; discriminate.
(* C *)
inversion H; subst; clear H IHt; simpl in H1.
inversion H1; subst; clear H1; simpl in H2.
inversion H2; subst; clear H2.
inversion H; subst; clear H.
inversion H0; subst.
change (CallByNameCallCC.contextC_to_context c2 = CallByNameCallCC.contextC_to_context (C_ctxC c)) in H;
apply CallByNameCallCC.contextC_to_context_injective in H;
apply CallByNameCallCC.substC_to_subst_injective in H2; subst.
constructor...
induction t; discriminate.
(* eval -> red -> apply *)
assert (dec_by_cls cl c1 (inr (CBN_EAM.UEAM.term * CBN_EAM.UEAM.substC * CBN_EAM.UEAM.contextC) (v, c2))).
rewrite <- H0; apply unf_red_correct.
induction t; simpl in H; inversion H; subst; clear H0 H.
(* var *)
simpl in H1; assert (ht := CallByNameCallCC.getC _ _ _ _ _ H1).
destruct ht as [[cl2 ct2] [ht hq]]; subst.
inversion H2; subst; simpl in *.
apply CallByNameCallCC.contextC_to_context_injective in H0;
apply CallByNameCallCC.closureC_to_closure_injective in H; subst cl2 ct2.
constructor...
induction cl2; try (induction t); discriminate.
(* lam *)
simpl in H1; inversion H1; clear H1 IHt.
change (beta_plus (CallByNameCallCC.contextC_to_context c) n (CallByNameCallCC.subC_to_sub s) (CallByNameCallCC.subC_to_sub nil) t = (cl, c1)) in H0;
assert (ht := CallByNameCallCC.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ht hq]; subst.
inversion H2; subst; simpl in *.
apply CallByNameCallCC.contextC_to_context_injective in H1;
apply CallByNameCallCC.closureC_to_closure_injective in H; subst cl2 ct2.
constructor...
induction cl2; try (induction t0); discriminate.
(* appl *)
simpl in H1; inversion H1; subst; clear IHt1 IHt2 H1.
inversion H2; subst.
induction v; discriminate.
simpl in H; inversion H; clear H H2; subst.
inversion H0; subst; clear H0.
induction v; discriminate.
induction t1; discriminate.
(* C *)
inversion H1; subst; clear H1 IHt.
inversion H2; subst; clear H2.
induction v; discriminate.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
induction v; discriminate.
induction t; discriminate.
(* final *)
induction c; inversion H; apply CallByNameCallCC.valueC_to_value_injective in H1; subst; constructor.
(* apply -> red -> eval *)
assert (CallByNameCallCC.dec_by_cls cl c1 (inl (CBN_EAM.UEAM.valueC * CBN_EAM.UEAM.contextC) (t, s, c2)));
[rewrite <- H0; apply unf_c_red_correct | induction c; try discriminate; clear H0 IHc].
(* ap_rC *)
inversion H; subst r c0; clear H.
induction v; inversion H1; clear H1.
(* - v_lamC *)
change (CallByNameCallCC.beta_plus (CallByNameCallCC.contextC_to_context (ap_rC c c3)) n (CallByNameCallCC.subC_to_sub s0) (CallByNameCallCC.subC_to_sub l) t0 = (cl, c1)) in H0.
assert (ht := CallByNameCallCC.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByNameCallCC.contextC_to_context_injective in H;
change (closureC_to_closure (pairC t s) = closureC_to_closure cl2) in H1;
apply CallByNameCallCC.closureC_to_closure_injective in H1; subst; constructor...
simpl; intro; discriminate.
simpl in H0; induction cl2; try induction t1; discriminate.
(* - v_c_ctC *)
subst; inversion H2; subst; clear H2.
change (closureC_to_closure (pairC t s) = (c:closureC)) in H0;
apply CallByNameCallCC.closureC_to_closure_injective in H0;
apply CallByNameCallCC.contextC_to_context_injective in H; subst.
constructor.
induction c; try induction t0; discriminate.
(* C_ctxC *)
inversion H; subst r c0; clear H.
induction v; inversion H1; subst; clear H1.
(* - v_lamC *)
change (CallByNameCallCC.beta_plus (CallByNameCallCC.contextC_to_context (C_ctxC c)) n (CallByNameCallCC.subC_to_sub s0) (CallByNameCallCC.subC_to_sub l) t0 = (cl, c1)) in H0.
assert (ht := CallByNameCallCC.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByNameCallCC.contextC_to_context_injective in H;
change (closureC_to_closure (pairC t s) = closureC_to_closure cl2) in H1;
apply CallByNameCallCC.closureC_to_closure_injective in H1; subst; constructor...
simpl; intro; discriminate.
simpl in H; induction cl2; try induction t1; discriminate.
(* - v_c_ctC *)
inversion H2; subst; clear H2.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
discriminate.
(* apply -> red -> apply *)
assert (CallByNameCallCC.dec_by_cls cl c1 (inr (CBN_EAM.UEAM.term * CBN_EAM.UEAM.substC * CBN_EAM.UEAM.contextC) (v0, c2))).
rewrite <- H0; apply unf_c_red_correct.
induction c; clear H0; inversion H; subst; induction v; inversion H1; subst; clear H1 H IHc.
(* ap_rC *)
(* - v_lamC *)
change (CallByNameCallCC.beta_plus (CallByNameCallCC.contextC_to_context (ap_rC c c3)) n (CallByNameCallCC.subC_to_sub s) (CallByNameCallCC.subC_to_sub l) t = (cl, c1)) in H3.
assert (ht := CallByNameCallCC.getB _ _ _ _ _ _ _ H3); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByNameCallCC.contextC_to_context_injective in H0;
apply CallByNameCallCC.closureC_to_closure_injective in H; subst; constructor...
simpl; intro; discriminate.
simpl in H; induction cl2; try induction t0; discriminate.
(* - v_c_ctC *)
subst; inversion H2; subst; clear H2.
apply CallByNameCallCC.closureC_to_closure_injective in H;
apply CallByNameCallCC.contextC_to_context_injective in H0; subst; constructor.
induction c; try induction t; discriminate.
(* C_ctxC *)
(* - v_lamC *)
change (CallByNameCallCC.beta_plus (CallByNameCallCC.contextC_to_context (C_ctxC c)) n (CallByNameCallCC.subC_to_sub s) (CallByNameCallCC.subC_to_sub l) t = (cl, c1)) in H3.
assert (ht := CallByNameCallCC.getB _ _ _ _ _ _ _ H3); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByNameCallCC.contextC_to_context_injective in H0;
apply CallByNameCallCC.closureC_to_closure_injective in H; subst; constructor...
intro; discriminate.
simpl in H; induction cl2; try induction t0; discriminate.
(* - v_c_ctC *)
inversion H2; subst; clear H2.
induction v0; discriminate.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
change (contextC_to_context c2 = contextC_to_context (ap_rC (CallByNameCallCC.C_ctC c) c)) in H1;
apply CallByNameCallCC.contextC_to_context_injective in H1;
change (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v0) = closureC_to_closure (CallByNameCallCC.valueC_to_closureC (v_ccC c0))) in H;
apply CallByNameCallCC.closureC_to_closure_injective in H; apply CallByNameCallCC.valueC_to_closureC_injective in H; subst; constructor.
discriminate.
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
(* init *)
constructor.
(* lam -> apply *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (lam n t) s) (ct:context) = in_dec (d_red (CallByNameCallCC.r_lam n t (s:subst)) (ct:context)))...
assert (hb : contract (CallByNameCallCC.r_lam n t (s:subst)) (ct:context) = Some (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v), ct0:context)).
simpl; f_equal...
constructor 4 with (ct : context) (ct0 : context) (CallByNameCallCC.r_lam n t (s:subst)) _ ha hb.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByNameCallCC.unfold_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* lam -> eval *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (lam n t) s) (ct:context) = in_dec (d_red (CallByNameCallCC.r_lam n t (s:subst)) (ct:context)))...
assert (hb : contract (CallByNameCallCC.r_lam n t (s:subst)) (ct:context) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 3 with (ct : context) (ct0 : context) (CallByNameCallCC.r_lam n t (s:subst)) _ ha hb.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByNameCallCC.unfold_red as [p peq].
inversion peq; subst; repeat f_equal...
destruct v; discriminate.
destruct t0; discriminate.
(* var -> eval *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (var n) s) (c:context) = in_dec (d_red (CallByNameCallCC.r_get n (s:subst)) (c:context)))...
constructor 3 with (c:context) (c0:context) (CallByNameCallCC.r_get n (s:subst)) _ ha H...
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByNameCallCC.unfold_red as [p peq].
inversion peq; subst; [ repeat f_equal | destruct v; discriminate | destruct t; discriminate]...
(* var -> apply *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (var n) s) (c:context) = in_dec (d_red (CallByNameCallCC.r_get n (s:subst)) (c:context)))...
constructor 4 with (c : context) (c1 : context) (CallByNameCallCC.r_get n (s:subst)) _ ha H.
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByNameCallCC.unfold_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* appl -> eval *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (appl t0 t1) s) (c:context) = in_dec (d_red (CallByNameCallCC.r_app t0 t1 (s:subst)) (c:context)))...
assert (hb : contract (CallByNameCallCC.r_app t0 t1 (s:subst)) (c:context) = Some (CallByNameCallCC.comp (closureC_to_closure (pairC t0 s)) (closureC_to_closure (pairC t1 s)),  c:context)).
simpl; f_equal...
constructor 3 with (c:context) (contextC_to_context c) (CallByNameCallCC.r_app t0 t1 (s:subst)) _ ha hb...
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByNameCallCC.unfold_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
injection H; intros; subst; inversion H0; subst; [repeat f_equal | destruct v; discriminate | destruct t0; discriminate]...
apply CallByNameCallCC.substC_to_subst_injective in H3; subst...
(* C -> eval *)
assert (ha : CBN_EAM.UEAM.dec_term (pairC (C t) s) (c:context) = in_dec (d_red (CallByNameCallCC.r_C t (s:subst)) (c:context)))...
assert (hb : contract (CallByNameCallCC.r_C t (s:subst)) (c:context) = Some (CallByNameCallCC.C_cl (closureC_to_closure (pairC t s)),  c:context)).
simpl; f_equal...
constructor 3 with (c:context) (contextC_to_context c) (CallByNameCallCC.r_C t (s:subst)) _ ha hb...
unfold CBN_EAM.unf_red; unfold CBN_EAM.UEAM.unf_red; destruct CallByNameCallCC.unfold_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
injection H; intros; subst; inversion H0; subst; [repeat f_equal | destruct v; discriminate | destruct t; discriminate]...
(* final *)
constructor...
(* v_lamC -> apply *)
induction ct; try (elim H; reflexivity; fail); clear IHct H.
(* ap_rC *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (ap_rC c ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByNameCallCC.r_beta (valueC_to_value (v_lamC n t s l)) (closureC_to_closure c)) (contextC_to_context ct)))...
assert (hb : contract (CallByNameCallCC.r_beta (valueC_to_value(v_lamC n t s l)) (closureC_to_closure c)) (contextC_to_context ct) = Some (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v), ct0:context)).
simpl; f_equal...
constructor 10 with _ _ (CallByNameCallCC.r_beta (valueC_to_value (v_lamC n t s l)) (closureC_to_closure c)) _ ha hb.
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByNameCallCC.unfold_c_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* C_ctxC *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (C_ctxC ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByNameCallCC.r_vct (valueC_to_value (v_lamC n t s l))) (contextC_to_context ct)))...
assert (hb : contract (CallByNameCallCC.r_vct (valueC_to_value(v_lamC n t s l))) (contextC_to_context ct) = Some (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v), ct0:context)).
simpl; f_equal...
constructor 10 with _ _ (CallByNameCallCC.r_vct (valueC_to_value (v_lamC n t s l))) _ ha hb.
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByNameCallCC.unfold_c_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* v_lamC -> eval *)
induction ct; try (elim H; reflexivity; fail); clear H IHct.
(* ap_rC *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (ap_rC c ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByNameCallCC.r_beta (valueC_to_value (v_lamC n t s l)) (closureC_to_closure c)) (contextC_to_context ct)))...
assert (hb : contract (CallByNameCallCC.r_beta (valueC_to_value(v_lamC n t s l)) (closureC_to_closure c)) (contextC_to_context ct) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 9 with _ _ (CallByNameCallCC.r_beta (valueC_to_value (v_lamC n t s l)) (closureC_to_closure c)) _ ha hb.
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByNameCallCC.unfold_c_red as [p peq].
inversion peq; subst; [repeat f_equal | destruct v; discriminate | destruct t0; discriminate]...
(* C_ctxC *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (C_ctxC ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByNameCallCC.r_vct (valueC_to_value (v_lamC n t s l))) (contextC_to_context ct)))...
assert (hb : contract (CallByNameCallCC.r_vct (valueC_to_value(v_lamC n t s l))) (contextC_to_context ct) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 9 with _ _ (CallByNameCallCC.r_vct (valueC_to_value (v_lamC n t s l))) _ ha hb.
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByNameCallCC.unfold_c_red as [p peq].
inversion peq; subst; [repeat f_equal | destruct v; discriminate | destruct t0; discriminate]...
(* v_ccC ap_rC -> eval *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_ccC ct0)) (contextC_to_context (ap_rC (pairC t s) ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByNameCallCC.r_beta (valueC_to_value (v_ccC ct0)) (closureC_to_closure (pairC t s))) (contextC_to_context ct)))...
assert (hb : contract (CallByNameCallCC.r_beta (valueC_to_value(v_ccC ct0)) (closureC_to_closure (pairC t s))) (ct:context) = Some (closureC_to_closure (pairC t s), ct0:context)).
simpl; f_equal.
constructor 9 with (ct:context) _ (CallByNameCallCC.r_beta (valueC_to_value (v_ccC ct0)) (closureC_to_closure (pairC t s))) _ ha hb.
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByNameCallCC.unfold_c_red as [p peq].
inversion peq; subst; [repeat f_equal | destruct v; discriminate | destruct t; discriminate]...
(* v_ccC ap_rC -> apply *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_ccC ct0)) (contextC_to_context (ap_rC (CallByNameCallCC.valueC_to_closureC v)  ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByNameCallCC.r_beta (valueC_to_value (v_ccC ct0)) (CallByNameCallCC.valueC_to_closureC v)) (contextC_to_context ct)))...
assert (hb : contract (CallByNameCallCC.r_beta (valueC_to_value(v_ccC ct0)) (CallByNameCallCC.valueC_to_closureC v)) (ct:context) = Some (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v), ct0:context)).
simpl; repeat f_equal...
constructor 10 with (ct:context) _ (CallByNameCallCC.r_beta (valueC_to_value (v_ccC ct0)) (CallByNameCallCC.valueC_to_closureC v)) (closureC_to_closure (CallByNameCallCC.valueC_to_closureC v)) ha hb...
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByNameCallCC.unfold_c_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* v_ccC C_ctxC -> apply *)
assert (ha : CBN_EAM.UEAM.dec_context (valueC_to_value (v_ccC ct0)) (contextC_to_context (C_ctxC ct)) = CBN_EAM.UEAM.in_dec (CBN_EAM.UEAM.d_red (CallByNameCallCC.r_vct (valueC_to_value (v_ccC ct0))) (contextC_to_context ct)))...
assert (hb : contract (CallByNameCallCC.r_vct (valueC_to_value(v_ccC ct0))) (ct:context) = Some (CallByNameCallCC.comp (closureC_to_closure (CallByNameCallCC.C_ctC ct0)) (closureC_to_closure (CallByNameCallCC.C_ctC ct)), ct:context)).
simpl; repeat f_equal...
constructor 10 with (ct:context) _ (CallByNameCallCC.r_vct (valueC_to_value (v_ccC ct0))) (CallByNameCallCC.comp (closureC_to_closure (CallByNameCallCC.C_ctC ct0)) (closureC_to_closure (CallByNameCallCC.C_ctC ct))) ha hb.
unfold CBN_EAM.unf_c_red; unfold CBN_EAM.UEAM.unf_c_red; destruct CallByNameCallCC.unfold_c_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
injection H; intros; subst; inversion H0; subst; [repeat f_equal | discriminate]...
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

Theorem KrivineMachineCorrect : forall t (v:valueC), eval_CBN t (valueC_to_value v) <-> eval t v.
Proof with auto.
intros; rewrite eval_equiv; rewrite CBN_EAM.evalMachine; split...
Qed.

End KrivineMachineWCallCC.