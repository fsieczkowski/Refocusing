Require Import refocusing_environments_cs.
Require Import Setoid.

Module CallByValue <: RED_LANG.

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
with value' : Set :=
| v_lam : nat -> term -> list closure' -> list closure' -> value'
| v_c_ct: context' -> value'
with context' : Set :=
| mt    : context'
| ap_l  : closure' -> context' -> context'
| ap_r  : value' -> context' -> context'
| C_ctx : context' -> context'.
Definition closure := closure'.
Definition value := value'.
Definition substitution := list closure.
Definition pair : term -> substitution -> closure := pair'.

Definition context := context'.
Definition empty : context := mt.

Inductive redex' : Set :=
| r_beta : value -> value -> redex'
| r_vct  : value -> redex'
| r_lam  : nat -> term -> substitution -> redex'
| r_get  : nat -> substitution -> redex'
| r_app  : term -> term -> substitution -> redex'
| r_C    : term -> substitution -> redex'.
Definition redex := redex'.

Inductive closureC' : Set :=
| pairC' : term -> list closureC' -> closureC'
| C_ctC  : contextC' -> closureC'
| u_lamC : nat -> term -> list closureC' -> list closureC' -> closureC'
with valueC' : Set :=
| v_lamC : nat -> term -> list closureC' -> list closureC' -> valueC'
| v_c_ctC: contextC' -> valueC'
with contextC' : Set :=
| mtC    : contextC'
| ap_rC  : valueC' -> contextC' -> contextC'
| ap_lC  : closureC' -> contextC' -> contextC'
| C_ctxC : contextC' -> contextC'.
Definition closureC := closureC'.
Definition substitutionC := list closureC.
Definition pairC : term -> substitutionC -> closureC := pairC'.

Definition contextC := contextC'.
Definition emptyC : contextC := mtC.

Definition valueC := valueC'.

Inductive redexC' : Set :=
| r_betaC : valueC -> valueC -> redexC'
| r_vctC : valueC -> redexC'
| r_lamC : nat -> term -> substitutionC -> redexC'.
Definition redexC := redexC'.

Definition value_to_closure : value -> closure :=
fun v => match v with
| v_lam n t s l => u_lam n t s l
| v_c_ct ct => C_ct ct
end.
Coercion value_to_closure : value >-> closure.

Definition redex_to_closure : redex -> closure :=
fun r => match r with
| r_beta v v0 => comp (v:closure) (v0:closure)
| r_vct v => C_cl (v:closure)
| r_lam n t s => pair (lam n t) s
| r_get n s => pair (var n) s
| r_app t t0 s => pair (appl t t0) s
| r_C t s => pair (C t) s
end.
Coercion redex_to_closure : redex >-> closure.

Fixpoint plug (cl : closure) (ct : context) {struct ct} : closure :=
match ct with
| empty => cl
| ap_r v ct0 => plug (comp cl (value_to_closure v)) ct0
| ap_l cl0 ct0 => plug (comp cl0 cl) ct0
| C_ctx ct => plug (C_cl cl) ct
end.

Fixpoint compose (ct : context) (ct0 : context) {struct ct} : context :=
match ct with
| empty => ct0
| ap_r v ct' => ap_r v (compose ct' ct0)
| ap_l cl0 ct1 => ap_l cl0 (compose ct1 ct0)
| C_ctx ct => C_ctx (compose ct ct0)
end.

Fixpoint composeC (ct : contextC) (ct0 : contextC) {struct ct} : contextC :=
match ct with
| emptyC => ct0
| ap_rC v ct' => ap_rC v (composeC ct' ct0)
| ap_lC cl ct' => ap_lC cl (composeC ct' ct0)
| C_ctxC ct => C_ctxC (composeC ct ct0)
end.

Fixpoint closureC_to_closure (cl : closureC) : closure :=
match cl with
| pairC t s => pair t (map closureC_to_closure s)
| u_lamC n t s l => u_lam n t (map closureC_to_closure s) (map closureC_to_closure l)
| C_ctC ct => C_ct (contextC_to_context ct)
end with contextC_to_context (ct : contextC) : context :=
match ct with
| emptyC => empty
| ap_rC v ct' => ap_r (valueC_to_value v) (contextC_to_context ct')
| ap_lC cl ct' => ap_l (closureC_to_closure cl) (contextC_to_context ct')
| C_ctxC ct => C_ctx (contextC_to_context ct)
end with valueC_to_value (v : valueC) : value :=
match v with
| v_lamC n t s l => v_lam n t (map closureC_to_closure s) (map closureC_to_closure l)
| v_c_ctC ct => v_c_ct (contextC_to_context ct)
end.
Definition subC_to_sub : substitutionC -> substitution :=
map closureC_to_closure.

Definition redexC_to_redex (r : redexC) : redex :=
match r with
| r_betaC v0 v1 => r_beta (valueC_to_value v0) (valueC_to_value v1)
| r_vctC v => r_vct (valueC_to_value v)
| r_lamC n t s => r_lam n t (subC_to_sub s)
end.

Definition valueC_to_closureC (v : valueC) : closureC :=
match v with
| v_lamC n t s c => u_lamC n t s c
| v_c_ctC ct => C_ctC ct
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

Fixpoint beta_plus (c:context) (n:nat) (s:substitution) (l : list closure) (t:term) {struct c} : (closure * context) :=
    match n with
    | 0 => (pair t (app l s), c)
    | S m => match c with
      | ap_r cl ct => beta_plus ct m s ((value_to_closure cl) :: l) t
      | C_ctx ct' => beta_plus ct' m s ((C_ct ct') :: l) t
      | _ => (u_lam n t s l, c)
      end
    end.

Definition contract (r : redex) (c : context) : option (closure * context) :=
  match r with
    | r_beta (v_lam n t s l) v => Some (beta_plus (ap_r v c) n s l t)
    | r_beta (v_c_ct ct) v => Some ((value_to_closure v), ct)
    | r_vct (v_lam n t s l) => Some (beta_plus (C_ctx c) n s l t)
    | r_vct (v_c_ct ct') => Some (comp (C_ct ct') (C_ct c), c)
    | r_lam n t s => Some (beta_plus c n s nil t)
    | r_get n s => nth_option s n c
    | r_app t0 t1 s => Some (comp (pair t0 s) (pair t1 s), c)
    | r_C t s => Some (C_cl (pair t s), c)
  end.

Lemma closureC_ind :
forall (P : closureC' -> Prop) (P0 : valueC' -> Prop) (P1 : contextC' -> Prop),
  (forall (t : term) (l : list closureC'), (forall t0, In t0 l -> P t0) -> P (pairC' t l)) ->
  (forall (ct : contextC), P1 ct -> P (C_ctC ct)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P t0) -> (forall t0, In t0 l -> P t0) -> P (u_lamC n t s l)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P t0) -> (forall t0, In t0 l -> P t0) -> P0 (v_lamC n t s l)) ->
  (forall (ct : contextC), P1 ct -> P0 (v_c_ctC ct)) ->
  (P1 mtC) ->
  (forall (v : valueC) (ct : contextC), P0 v -> P1 ct -> P1 (ap_rC v ct)) ->
  (forall (cl : closureC) (ct : contextC), P cl -> P1 ct -> P1 (ap_lC cl ct)) ->
  (forall (ct : contextC), P1 ct -> P1 (C_ctxC ct)) ->
  forall cl : closureC, P cl.
Proof with eauto.
intros P P0 P1 hPair hCC hULam hVLam hVCC hMt hApR hApL hCt.
refine (fix IHc (c : closureC') : P c := _
        with IHv (v : valueC') : P0 v := _
        with IHct (ct : contextC') : P1 ct := _ for IHc).
(* closureC *)
case c; intros.
(* pairC *)
apply hPair; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
(* C_ctC *)
apply hCC.
apply IHct.
(* u_lamC *)
apply hULam; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
induction l0.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl0.
fold (In t0 l0) in *.
apply H.
(* valueC *)
case v; intros.
(* v_lamC *)
apply hVLam; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
induction l0.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl0.
fold (In t0 l0) in *.
apply H.
(* v_c_ctC *)
apply hVCC; intros; apply IHct.
(* contextC *)
case ct; intros.
(* emptyC *)
apply hMt.
(* ap_rC *)
apply hApR; [ apply IHv | apply IHct].
(* ap_lC *)
apply hApL; [apply IHc | apply IHct].
(* C_ctxC *)
apply hCt; apply IHct.
Qed.

Lemma valueC_ind :
forall (P : closureC' -> Prop) (P0 : valueC' -> Prop) (P1 : contextC' -> Prop),
  (forall (t : term) (l : list closureC'), (forall t0, In t0 l -> P t0) -> P (pairC' t l)) ->
  (forall (ct : contextC), P1 ct -> P (C_ctC ct)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P t0) -> (forall t0, In t0 l -> P t0) -> P (u_lamC n t s l)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P t0) -> (forall t0, In t0 l -> P t0) -> P0 (v_lamC n t s l)) ->
  (forall (ct : contextC), P1 ct -> P0 (v_c_ctC ct)) ->
  (P1 mtC) ->
  (forall (v : valueC) (ct : contextC), P0 v -> P1 ct -> P1 (ap_rC v ct)) ->
  (forall (cl : closureC) (ct : contextC), P cl -> P1 ct -> P1 (ap_lC cl ct)) ->
  (forall (ct : contextC), P1 ct -> P1 (C_ctxC ct)) ->
  forall v : valueC, P0 v.
Proof with eauto.
intros P P0 P1 hPair hCC hULam hVLam hVCC hMt hApR hApL hCt.
refine (fix IHv (v : valueC') : P0 v := _
        with IHc (c : closureC') : P c := _
        with IHct (ct : contextC') : P1 ct := _ for IHv).
(* valueC *)
case v; intros.
(* v_lamC *)
apply hVLam; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
induction l0.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl0.
fold (In t0 l0) in *.
apply H.
(* v_c_ctC *)
apply hVCC; intros; apply IHct.
(* closureC *)
case c; intros.
(* pairC *)
apply hPair; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
(* C_ctC *)
apply hCC.
apply IHct.
(* u_lamC *)
apply hULam; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
induction l0.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl0.
fold (In t0 l0) in *.
apply H.
(* contextC *)
case ct; intros.
(* emptyC *)
apply hMt.
(* ap_rC *)
apply hApR; [ apply IHv | apply IHct].
(* ap_lC *)
apply hApL; [apply IHc | apply IHct].
(* C_ctxC *)
apply hCt; apply IHct.
Qed.

Lemma contextC_ind :
forall (P : closureC' -> Prop) (P0 : valueC' -> Prop) (P1 : contextC' -> Prop),
  (forall (t : term) (l : list closureC'), (forall t0, In t0 l -> P t0) -> P (pairC' t l)) ->
  (forall (ct : contextC), P1 ct -> P (C_ctC ct)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P t0) -> (forall t0, In t0 l -> P t0) -> P (u_lamC n t s l)) ->
  (forall (n : nat) (t : term) (s l : list closureC'), (forall t0, In t0 s -> P t0) -> (forall t0, In t0 l -> P t0) -> P0 (v_lamC n t s l)) ->
  (forall (ct : contextC), P1 ct -> P0 (v_c_ctC ct)) ->
  (P1 mtC) ->
  (forall (v : valueC) (ct : contextC), P0 v -> P1 ct -> P1 (ap_rC v ct)) ->
  (forall (cl : closureC) (ct : contextC), P cl -> P1 ct -> P1 (ap_lC cl ct)) ->
  (forall (ct : contextC), P1 ct -> P1 (C_ctxC ct)) ->
  forall ct : contextC, P1 ct.
Proof with eauto.
intros P P0 P1 hPair hCC hULam hVLam hVCC hMt hApR hApL hCt.
refine (fix IHct (ct : contextC') : P1 ct := _
        with IHc (c : closureC') : P c := _
        with IHv (v : valueC') : P0 v := _ for IHct).
(* contextC *)
case ct; intros.
(* emptyC *)
apply hMt.
(* ap_rC *)
apply hApR; [ apply IHv | apply IHct].
(* ap_lC *)
apply hApL; [apply IHc | apply IHct].
(* C_ctxC *)
apply hCt; apply IHct.
(* closureC *)
case c; intros.
(* pairC *)
apply hPair; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
(* C_ctC *)
apply hCC.
apply IHct.
(* u_lamC *)
apply hULam; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
induction l0.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl0.
fold (In t0 l0) in *.
apply H.
(* valueC *)
case v; intros.
(* v_lamC *)
apply hVLam; intros.
induction l.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl.
fold (In t0 l) in *.
apply H.
induction l0.
inversion H.
destruct H.
rewrite <- H.
apply IHc.
apply IHl0.
fold (In t0 l0) in *.
apply H.
(* v_c_ctC *)
apply hVCC; intros; apply IHct.
Qed.

Lemma in_list_lemma : 
  forall l l0 : list closureC',
  (forall t1 : closureC',
    In t1 l ->
    forall cl0 : closureC,
    closureC_to_closure t1 = closureC_to_closure cl0 -> t1 = cl0) ->
  map closureC_to_closure l = map closureC_to_closure l0 -> l = l0.
Proof with auto.
intros.
generalize dependent l0.
induction l.
destruct l0.
intros; trivial.
simpl in *.
intros.
discriminate.
intros.
destruct l0.
simpl in *.
discriminate.
simpl in *.
f_equal.
inversion H0.
apply H.
left; trivial.
apply H2.
apply IHl; intros.
apply H.
right; apply H1.
apply H2.
inversion H0; reflexivity. 
Qed.
Hint Resolve in_list_lemma : ref.

Lemma closureC_to_closure_injective : forall (cl cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0.
Proof with auto with ref.
induction cl using closureC_ind with
(P0 := fun v => forall v0, valueC_to_value v = valueC_to_value v0 -> v = v0)
(P1 := fun ct => forall ct0, contextC_to_context ct = contextC_to_context ct0 -> ct = ct0); intros;
try (destruct cl0); try (destruct v0); try (destruct ct0); try discriminate;
[inversion H0 | inversion H | inversion H1 | inversion H1 | inversion H |
idtac | inversion H | inversion H | inversion H]; f_equal...
Qed.
Hint Resolve closureC_to_closure_injective : ref.

Lemma contextC_to_context_injective : forall (ct ct0 : contextC), contextC_to_context ct = contextC_to_context ct0 -> ct = ct0.
Proof with auto with ref.
induction ct using contextC_ind with
(P := fun (cl : closureC) => forall (cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0)
(P0:= fun (v : valueC) => forall (v0 : valueC), valueC_to_value v = valueC_to_value v0 -> v = v0); intros;
try (destruct cl0); try (destruct v0); try (destruct ct0); try discriminate;
[ inversion H0 | inversion H | inversion H1 | inversion H1 | inversion H
| idtac | inversion H | inversion H | inversion H]; f_equal...
Qed.
Hint Resolve contextC_to_context_injective : ref.

Lemma valueC_to_value_injective : forall (v v0 : valueC), valueC_to_value v = valueC_to_value v0 -> v = v0.
Proof with auto with ref.
induction v using valueC_ind with
(P := fun cl => forall (cl0 : closureC), closureC_to_closure cl = closureC_to_closure cl0 -> cl = cl0)
(P1:= fun ct => forall (ct0 : contextC), contextC_to_context ct = contextC_to_context ct0 -> ct = ct0); intros;
try (destruct cl0); try (destruct v0); try (destruct ct0); try discriminate;
[ inversion H0 | inversion H | inversion H1 | inversion H1 | inversion H
| idtac | inversion H | inversion H | inversion H]; f_equal...
Qed.
Hint Resolve valueC_to_value_injective : ref.

Lemma plug_compose : forall c1 c2 r, plug r (compose c1 c2) = plug (plug r c1) c2.
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
induction cl; intros.
(* pair *)
right; case t; intros.
exists (r_get n l); exists empty...
exists (r_lam n t0 l); exists empty...
exists (r_app t0 t1 l); exists empty...
exists (r_C t0 l); exists empty...
(* comp *)
elim IHcl2; intros; right.
destruct H as [v2 H]; elim IHcl1; intros; clear IHcl2 IHcl1; subst.
destruct H0 as [v1 H0]; subst.
exists (r_beta v1 v2); exists empty...
destruct H0 as [r [ct H]]; exists r; exists (compose ct (ap_r v2 empty))...
rewrite plug_compose; rewrite H...
destruct H as [r [ct H]]; exists r; exists (compose ct (ap_l cl1 empty)).
rewrite plug_compose; rewrite H...
(* u_lam *)
left; exists (v_lam n t l l0)...
(* C_cl *)
right; elim IHcl; intros.
destruct H as [v H]; subst; exists (r_vct v); exists empty...
destruct H as [r [ct H]]; exists r; exists (compose ct (C_ctx empty)).
rewrite plug_compose; rewrite H...
(* C_ct *)
left; exists (v_c_ct c)...
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
| comp cl0 cl1 => in_term cl1 (ap_l cl0 ct)
| u_lam n t s l => in_val (v_lam n t s l) ct
| C_cl cl => in_term cl (C_ctx ct)
| C_ct ct' => in_val (v_c_ct ct') ct
end.

Definition dec_context (v : value) (ct : context) : interm_dec :=
match ct with 
| empty => in_dec (d_val v)
| ap_r v' ct0  => in_dec (d_red (r_beta v v') ct0)
| ap_l cl ct0 => in_term cl (ap_r v ct0)
| C_ctx ct => in_dec (d_red (r_vct v) ct)
end.

Lemma dec_context_empty : forall (v : value), dec_context v empty = in_dec (d_val v).
Proof.
auto.
Qed.

Lemma dec_term_value : forall (v : value) (c : context), dec_term (value_to_closure v) c = in_val v c.
Proof.
intro v; case v; simpl; auto.
Qed.
Hint Resolve dec_term_value : ref.

Coercion contextC_to_context : contextC >-> context.
Coercion closureC_to_closure : closureC >-> closure.
Coercion valueC_to_value : valueC >-> value.

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
Proof with auto.
induction n; induction ct; intros; simpl in H; try discriminate.
inversion H; subst; split with (pairC t (l++s), emptyC); simpl; f_equal;
[unfold subC_to_sub; apply map_app | reflexivity].
inversion H; subst; split with (pairC t (l++s), ap_rC v ct); simpl; f_equal;
unfold subC_to_sub; apply map_app.
inversion H; subst; split with (pairC t (l++s), ap_lC c ct); simpl; f_equal;
unfold subC_to_sub; apply map_app.
inversion H; subst; split with (pairC t (l++s), C_ctxC ct); simpl; f_equal;
unfold subC_to_sub; apply map_app.
inversion H; subst; split with (u_lamC (S n) t s l, emptyC); simpl; f_equal...
apply IHn with ct s ((valueC_to_closureC v) :: l) t; simpl.
rewrite commutes...
inversion H; subst; split with (u_lamC (S n) t s l, ap_lC c ct); simpl; f_equal...
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

Lemma dec_by_cls_folds_left : forall t s ct cl c, dec_by_cls cl c (inl _ (t, s, ct)) -> plug cl c = plug (closureC_to_closure (pairC t s)) (contextC_to_context ct).
Proof with auto.
induction cl; intros; inversion_clear H; try (induction t0; discriminate)...
inversion H0; subst; apply (IHcl2 _ H1).
inversion H0; subst; apply (IHcl _ H1).
discriminate.
Qed.

Lemma dec_by_cls_folds_right : forall v ct cl c, dec_by_cls cl c (inr _ (v, ct)) -> plug cl c = plug (closureC_to_closure (valueC_to_closureC v)) (contextC_to_context ct).
Proof with auto.
induction cl; intros; inversion_clear H; try (induction t; discriminate)...
inversion H0; subst; apply (IHcl2 _ H1).
inversion H0; subst; apply (IHcl _ H1).
discriminate.
Qed.

Lemma substC_to_subst_injective : forall (s s0 : substitutionC), subC_to_sub s = subC_to_sub s0 -> s = s0.
Proof with auto with ref.
induction s; intro s0; case s0; intros; simpl in *; try discriminate; inversion H; f_equal...
Qed.
Hint Resolve substC_to_subst_injective : ref.

Lemma valueC_to_closureC_injective : forall (v v0 : valueC), valueC_to_closureC v = valueC_to_closureC v0 -> v = v0.
Proof with auto.
intros v v0; case v; case v0; intros; simpl in *; try discriminate; injection H; intros; subst...
Qed.
Hint Resolve valueC_to_closureC_injective : ref.

Lemma dec_by_cls_function : forall cl c p p', dec_by_cls cl c p -> dec_by_cls cl c p' -> p = p'.
Proof with eauto with ref.
induction cl; intros; inversion H; inversion H0; subst; intros; try discriminate; try (induction t; discriminate); try (induction v; discriminate)...
repeat f_equal...
rewrite H1 in H6; inversion H6; subst cl'0 c'0; inversion H1; subst cl' c'; clear H1 H6; eapply IHcl2...
repeat f_equal; rewrite <- H1 in H5...
rewrite H1 in H6; inversion H6; subst cl'0 c'0; clear H6; inversion H1; subst cl' c'; eapply IHcl...
repeat f_equal; rewrite <- H5 in H1...
Qed.

Definition unfold_c_red :
forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl, ct1)) ->
  {p : (term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct1 p}.
Proof with auto.
intros v ct; case ct; intros; simpl in *; try discriminate.
injection H; intros; subst; clear H; generalize H0; clear H0; case v; intros;
simpl in H0; injection H0; clear H0; intros.
change (beta_plus (ap_rC v0 c:contextC) n (subC_to_sub l) (subC_to_sub l0) t = (cl, ct1)) in H.
apply getB in H; destruct H as [[cl0 ct0] hcl hct]; simpl in *; subst.
induction cl0.
split with (inl _ (t0, l1, ct0)); constructor.
split with (inr _ ((v_c_ctC c0), ct0)).
change (dec_by_cls (valueC_to_closureC (v_c_ctC c0)) ct0 (inr _ (v_c_ctC c0, ct0))); constructor.
intros t0 s eq; discriminate.
split with (inr _ ((v_lamC n0 t0 l1 l2), ct0)).
change (dec_by_cls ((valueC_to_closureC (v_lamC n0 t0 l1 l2))) ct0 (inr _ (v_lamC n0 t0 l1 l2, ct0))); constructor.
intros t1 s eq; discriminate.

subst; split with (inr _ (v0, c0)).
rewrite <- commutes; constructor.
intros t s eq; destruct v0; discriminate.

injection H; intros; subst; clear H.
generalize H0; clear H0; case v; intros; inversion H0.
change (beta_plus (C_ctxC c:contextC) n (subC_to_sub l) (subC_to_sub l0) t = (cl, ct1)) in H1.
apply getB in H1; destruct H1 as [[cl0 ct0] hcl hct]; simpl in *; subst; clear H0.
induction cl0.
split with (inl _ (t0, l1, ct0)); constructor.
split with (inr _ ((v_c_ctC c0), ct0)).
change (dec_by_cls (valueC_to_closureC (v_c_ctC c0)) ct0 (inr _ (v_c_ctC c0, ct0))); constructor.
intros t0 s eq; discriminate.
split with (inr _ ((v_lamC n0 t0 l1 l2), ct0)).
change (dec_by_cls ((valueC_to_closureC (v_lamC n0 t0 l1 l2))) ct0 (inr _ (v_lamC n0 t0 l1 l2, ct0))); constructor.
intros t1 s eq; discriminate.
subst; clear H0.
split with (inr _ (v_c_ctC c, ap_lC (C_ctC c0) c)); econstructor 3; simpl...
change (dec_by_cls (valueC_to_closureC (v_c_ctC c)) (ap_lC (C_ctC c0) c : contextC) (inr _ (v_c_ctC c, ap_lC (C_ctC c0) c))); constructor.
intros t s eq; discriminate.
Defined.

Definition unfold_red :
forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_dec (d_red r ct0)) -> (contract r ct0 = Some (cl0, ct1)) ->
  {p:(term * substitutionC * contextC)+(valueC * contextC) | dec_by_cls cl0 ct1 p}.
Proof with auto.
intro cl; case cl; try (intros; discriminate); intro t; case t; intros; simpl in *;
injection H; clear H; intros; subst.
(* r_get *)
simpl in H0; apply getC in H0; destruct H0 as [[cl2 ct2] [ecl ect]]; simpl in *; subst.
induction cl2.
split with (inl _ (t0, l0, ct2)); constructor.
split with (inr _ ((v_c_ctC c), ct2)).
change (dec_by_cls (valueC_to_closureC (v_c_ctC c)) ct2 (inr _ (v_c_ctC c, ct2))); constructor.
intros t0 s eq; discriminate.
split with (inr _ ((v_lamC n0 t0 l0 l1), ct2)).
change (dec_by_cls ((valueC_to_closureC (v_lamC n0 t0 l0 l1))) ct2 (inr _ (v_lamC n0 t0 l0 l1, ct2))); constructor.
intros t1 s eq; discriminate.
(* r_lam *)
simpl in H0; injection H0; clear H0; intros.
change (beta_plus ct n (subC_to_sub l) (subC_to_sub nil) t0 = (cl0, ct1)) in H;
apply getB in H; destruct H as [[cl2 ct2] ecl ect]; simpl in *; subst.
induction cl2.
split with (inl _ (t1, l0, ct2)); constructor.
split with (inr _ ((v_c_ctC c), ct2)).
change (dec_by_cls (valueC_to_closureC (v_c_ctC c)) ct2 (inr _ (v_c_ctC c, ct2))); constructor.
intros t1 s eq; discriminate.
split with (inr _ ((v_lamC n0 t1 l0 l1), ct2)).
change (dec_by_cls ((valueC_to_closureC (v_lamC n0 t1 l0 l1))) ct2 (inr _ (v_lamC n0 t1 l0 l1, ct2))); constructor.
intros t2 s eq; discriminate.
(* r_app *)
simpl in H0; injection H0; clear H0; intros; subst.
split with (inl _ (t1, l, ap_lC (pairC t0 l) ct));
econstructor; simpl.
f_equal...
change (dec_by_cls (pairC t1 l) (ap_lC (pairC t0 l) ct : contextC) (inl _ (t1, l, ap_lC (pairC t0 l) ct))); constructor.
(* r_C *)
simpl in H0; injection H0; clear H0; intros; subst.
split with (inl _ (t0, l, C_ctxC ct)); econstructor 3; simpl...
change (dec_by_cls (pairC t0 l) (C_ctxC ct : contextC) (inl _ (t0, l, C_ctxC ct))); constructor.
Defined.

Definition unfold_c_cls :
forall (v : valueC) (ct : contextC) (cl : closure) (ct0 : context),
  (dec_context (valueC_to_value v) (contextC_to_context ct) = in_term cl ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl ct0 p}.
Proof with auto.
intros v ct; case ct; intros; simpl; try discriminate.
injection H; clear H; intros; subst.
induction c.
split with (inl _ (t, l, ap_rC v c0)).
change (dec_by_cls (pairC t l) (ap_rC v c0 : contextC) (inl _ (t, l, ap_rC v c0))); constructor.
split with (inr _ (v_c_ctC c, ap_rC v c0)).
change (dec_by_cls (valueC_to_closureC (v_c_ctC c)) (ap_rC v c0 : contextC) (inr _ (v_c_ctC c, ap_rC v c0))); constructor.
intros t s eq; discriminate.
split with (inr _ (v_lamC n t l l0, ap_rC v c0)).
change (dec_by_cls (valueC_to_closureC (v_lamC n t l l0)) (ap_rC v c0 : contextC) (inr _ (v_lamC n t l l0, ap_rC v c0))); constructor.
intros t0 s eq; discriminate.
Defined.

Definition unfold_cls :
forall (cl : closureC) (ct : contextC) (cl0 : closure) (ct0 : context),
  (dec_term (closureC_to_closure cl) (contextC_to_context ct) = in_term cl0 ct0) ->
  {p:(term * substitutionC * contextC) + (valueC * contextC) | dec_by_cls cl0 ct0 p}.
Proof with auto.
intro cl; case cl; try (intro t; case t); intros; simpl; discriminate.
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
Proof with eauto with ref.
intro r; case r; intros; simpl; try (constructor; auto; fail).
econstructor 3; simpl...
econstructor 2...
econstructor 3; simpl...
econstructor 2...
econstructor...
econstructor 3; simpl...
econstructor 2...
econstructor...
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
induction c; intros; simpl in *; auto;
assert (hh := IHc _ _ _ H); inversion hh; simpl in H0; try discriminate;
injection H0; intros; subst...
inversion H1; rewrite dec_term_value in H2; inversion H2; subst.
inversion H3; inversion H4; subst...
Qed.

Lemma dec_plug_rev : forall c c0 t d, dec t (compose c c0) d -> dec (plug t c) c0 d.
Proof with eauto.
induction c; intros; simpl in *...
apply IHc; econstructor 3; simpl...
apply IHc; econstructor 3; simpl...
econstructor 2; [eapply dec_term_value | econstructor 3]; simpl...
apply IHc; econstructor 3; simpl...
Qed.

End CallByValue.

Module CBV_EAM := ProperEAMachine (CallByValue).
Module CBV_Eval := Evaluator (CallByValue).
Definition eval_CBV := CBV_Eval.eval.
Definition eval_CBV_EAM := CBV_EAM.E.eval.

Lemma eval_equiv : forall t v, eval_CBV t v <-> eval_CBV_EAM t v.
Proof with eauto.
intros; split; intros; inversion_clear H; inversion_clear H0;
econstructor; try (econstructor; eauto; fail);
clear H; induction H1; try (constructor; fail);
inversion_clear H0; econstructor; eauto; constructor...
Qed.

Module EAMachine.

Definition term := CallByValue.term.
Definition closureC := CallByValue.closureC.
Definition substC := CallByValue.substitutionC.
Definition contextC := CallByValue.contextC.
Definition valueC := CallByValue.valueC.
Definition value := CallByValue.value.
Definition emptyC := CallByValue.emptyC.
Definition v_lamC := CallByValue.v_lamC.
Definition v_c_ctC := CallByValue.v_c_ctC.
Definition var := CallByValue.var.
Definition lam := CallByValue.lam.
Definition appl := CallByValue.appl.
Definition C := CallByValue.C.
Definition ap_rC := CallByValue.ap_rC.
Definition ap_lC := CallByValue.ap_lC.
Definition C_ctxC := CallByValue.C_ctxC.
Definition subst := CallByValue.substitution.
Definition context := CallByValue.context.
Definition closure := CallByValue.closure.
Definition pairC := CallByValue.pairC.

Definition closureC_to_closure (cl:closureC) : closure := CallByValue.closureC_to_closure cl.
Definition substC_to_subst (s : substC) : subst := CallByValue.subC_to_sub s.
Definition valueC_to_value (v : valueC) : value := CallByValue.valueC_to_value v.
Definition contextC_to_context (ct : contextC) : context := CallByValue.contextC_to_context ct.

Coercion closureC_to_closure : closureC >-> closure.
Coercion substC_to_subst : substC >-> subst.
Coercion valueC_to_value : valueC >-> value.
Coercion contextC_to_context : contextC >-> context.

Definition nth_option := CallByValue.nth_option.
Definition beta_plus := CallByValue.beta_plus.
Definition contract := CallByValue.contract.

Definition configuration := CBV_EAM.configuration.
Definition c_init := CBV_EAM.c_init.
Definition c_eval := CBV_EAM.c_eval.
Definition c_apply := CBV_EAM.c_apply.
Definition c_final := CBV_EAM.c_final.

Definition dec_term := CallByValue.dec_term.
Definition dec_context := CallByValue.dec_context.
Definition in_dec := CallByValue.in_dec.
Definition d_red := CallByValue.d_red.
Definition redex := CallByValue.redex.
Definition dec_by_cls := CallByValue.dec_by_cls.

Lemma unf_red_correct : forall (cl : closureC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl0 : closure)
  (H : dec_term (cl:closure) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl0, ct1)),
  dec_by_cls cl0 ct1 (CBV_EAM.UEAM.unf_red cl ct r ct0 ct1 cl0 H H1).
Proof with auto.
intros; unfold CBV_EAM.UEAM.unf_red; simpl in *.
remember (CallByValue.unfold_red cl ct r ct0 ct1 cl0 H H1).
destruct s as [p q]...
Qed.

Lemma unf_c_red_correct : forall (v : valueC) (ct : contextC) (r : redex) (ct0 ct1 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) (ct:context) = in_dec (d_red r ct0)) (H1 : contract r ct0 = Some (cl, ct1)),
  dec_by_cls cl ct1 (CBV_EAM.UEAM.unf_c_red v ct r ct0 ct1 cl H H1).
Proof with auto.
intros; unfold CBV_EAM.UEAM.unf_c_red; simpl in *.
remember (CallByValue.unfold_c_red v ct r ct0 ct1 cl H H1).
destruct s as [p q]...
Qed.

Lemma unf_c_cls_correct : forall (v : valueC) (ct : contextC) (ct0 : context) (cl : closure)
  (H : dec_context (valueC_to_value v) (ct:context) = CallByValue.in_term cl ct0), CallByValue.dec_by_cls cl ct0 (CBV_EAM.UEAM.unf_c_cls v ct ct0 cl H).
Proof with auto.
intros; unfold CBV_EAM.UEAM.unf_c_cls; simpl in *.
remember (CallByValue.unfold_c_cls v ct cl ct0 H).
destruct s as [p q]...
Qed.

Inductive transition : configuration -> configuration -> Prop :=
| t_init : forall (t : term), transition (c_init t) (c_eval t nil emptyC)
| t_lam_u: forall (t : term) (n : nat) (s : substC) (v : valueC) (ct ct0 : contextC),
             beta_plus (ct:context) n (s:subst) nil t = (closureC_to_closure (CallByValue.valueC_to_closureC v), ct0:context) ->
             transition (c_eval (lam n t) s ct) (c_apply ct0 v)
| t_lam_r: forall (t t0 : term) (n : nat) (s s0 : substC) (ct ct0 : contextC),
             beta_plus (ct : context) n (s:subst) nil t = (closureC_to_closure (pairC t0 s0), ct0:context) ->
             transition (c_eval (lam n t) s ct) (c_eval t0 s0 ct0)
| t_varP : forall (n:nat) (s s0:substC) (c c0:contextC) (t:term),
             nth_option (s:subst) n (c:context) = Some (closureC_to_closure (pairC t s0), c0:context) ->
             transition (c_eval (var n) s c) (c_eval t s0 c0)
| t_varC : forall (n:nat) (s:substC) (c c1:contextC) (v : valueC),
             nth_option (s:subst) n (c:context) = Some (closureC_to_closure (CallByValue.valueC_to_closureC v), c1:context) ->
             transition (c_eval (var n) s c) (c_apply c1 v)
| t_app  : forall (t0 t1:term) (s:substC) (c:contextC),
             transition (c_eval (appl t0 t1) s c) (c_eval t1 s (ap_lC (pairC t0 s) c))
| t_C    : forall (t : term) (s : substC) (c : contextC),
             transition (c_eval (C t) s c) (c_eval t s (C_ctxC c))
| t_mt     : forall (v : valueC), transition (c_apply emptyC v) (c_final v)
| t_ap_r_v : forall (n : nat) (t : term) (s l : substC) (v v0 : valueC) (ct ct0: contextC),
               beta_plus (contextC_to_context (ap_rC v ct)) n (s:subst) (l:subst) t = (closureC_to_closure (CallByValue.valueC_to_closureC v0), ct0 : context) ->
               transition (c_apply (ap_rC v ct) (v_lamC n t s l)) (c_apply ct0 v0)
| t_ap_r_r : forall (n : nat) (t t0 : term) (s l s0 : substC) (v : valueC) (ct ct0: contextC),
               beta_plus (contextC_to_context (ap_rC v ct)) n (s:subst) (l:subst) t = (closureC_to_closure (pairC t0 s0), ct0 : context) ->
               transition (c_apply (ap_rC v ct) (v_lamC n t s l)) (c_eval t0 s0 ct0)
| t_ap_r_c : forall (v : valueC) (ct ct0 : contextC),
               transition (c_apply (ap_rC v ct) (v_c_ctC ct0)) (c_apply ct0 v)
| t_ap_l_v : forall (v v0 : valueC) (ct : contextC),
               transition (c_apply (ap_lC (CallByValue.valueC_to_closureC v) ct) v0) (c_apply (ap_rC v0 ct) v)
| t_ap_l_r : forall (t : term) (s : substC) (ct : contextC) (v : valueC),
               transition (c_apply (ap_lC (pairC t s) ct) v) (c_eval t s (ap_rC v ct))
| t_C_ct_v : forall (n : nat) (t : term) (s l : substC) (ct ct0 : contextC) (v : valueC),
               beta_plus (contextC_to_context (C_ctxC ct)) n (s:subst) (l:subst) t = (closureC_to_closure (CallByValue.valueC_to_closureC v), ct0 : context) ->
               transition (c_apply (C_ctxC ct) (v_lamC n t s l)) (c_apply ct0 v)
| t_C_ct_r : forall (n : nat) (t t0 : term) (s l s0 : substC) (ct ct0 : contextC),
               beta_plus (contextC_to_context (C_ctxC ct)) n (s:subst) (l:subst) t = (closureC_to_closure (pairC t0 s0), ct0 : context) ->
               transition (c_apply (C_ctxC ct) (v_lamC n t s l)) (c_eval t0 s0 ct0)
| t_C_ct_c : forall (ct ct0 : contextC),
               transition (c_apply (C_ctxC ct) (v_c_ctC ct0)) (c_apply (ap_lC (CallByValue.valueC_to_closureC (v_c_ctC ct0)) ct) (v_c_ctC ct)).

Inductive trans_close : configuration -> configuration -> Prop :=
| one_step : forall w w' : configuration, 
               transition w w' -> trans_close w w'
| mul_step : forall w w' w'' : configuration, 
               transition w w' -> trans_close w' w'' -> trans_close w w''.

Inductive eval : term -> valueC -> Prop :=
| e_intro : forall (t : term) (v : valueC), trans_close (c_init t) (c_final v) -> eval t v.

Lemma transition_unf_z : forall c0 c1, CBV_EAM.transition c0 c1 -> transition c0 c1.
Proof with eauto.
induction 1; try (induction t; discriminate); try (induction c; discriminate).
(* init *)
constructor.
(* eval -> redex -> eval *)
assert (dec_by_cls cl c1 (inl (CBV_EAM.UEAM.valueC * CBV_EAM.UEAM.contextC) (t0, s0, c2))).
rewrite <- H0; apply unf_red_correct.
clear H0; induction t; simpl in H.
(* var *)
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
(* lam *)
inversion H; subst r c0; clear H.
simpl in H1; inversion H1; clear H1.
change (beta_plus (contextC_to_context c) n (CallByValue.subC_to_sub s) (CallByValue.subC_to_sub nil) t = (cl, c1)) in H0;
assert (ht := CallByValue.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ht hq]; subst.
inversion H2; subst.
apply CallByValue.contextC_to_context_injective in H; subst ct2.
change (closureC_to_closure (pairC t0 s0) = closureC_to_closure cl2) in H1.
apply CallByValue.closureC_to_closure_injective in H1; subst cl2.
constructor...
simpl in *.
induction cl2; try discriminate.
induction t1; discriminate.
(* appl *)
clear IHt1 IHt2.
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
(* C *)
inversion H; subst r c0; clear H.
inversion H1; subst; clear H1 IHt.
inversion H2; subst; clear H2.
inversion H; subst cl' c'; clear H.
inversion H0; subst.
change (contextC_to_context c2 = contextC_to_context (C_ctxC c)) in H;
apply CallByValue.contextC_to_context_injective in H;
apply CallByValue.substC_to_subst_injective in H2; subst c2 s0; constructor.
induction t; discriminate.
(* eval -> red -> apply *)
assert (dec_by_cls cl c1 (inr (CBV_EAM.UEAM.term * CBV_EAM.UEAM.substC * CBV_EAM.UEAM.contextC) (v, c2))).
rewrite <- H0; apply unf_red_correct.
induction t; simpl in H; try discriminate; inversion H; subst; clear H0 H.
(* var *)
simpl in H1; assert (ht := CallByValue.getC _ _ _ _ _ H1).
destruct ht as [[cl2 ct2] [ht hq]]; subst.
inversion H2; subst; simpl in *.
apply CallByValue.contextC_to_context_injective in H0;
apply CallByValue.closureC_to_closure_injective in H; subst cl2 ct2.
constructor...
induction cl2; try (induction t); discriminate.
(* lam *)
simpl in H1; inversion H1; clear H1 IHt.
change (beta_plus (CallByValue.contextC_to_context c) n (CallByValue.subC_to_sub s) (CallByValue.subC_to_sub nil) t = (cl, c1)) in H0;
assert (ht := CallByValue.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ht hq]; subst.
inversion H2; subst; simpl in *.
apply CallByValue.contextC_to_context_injective in H1;
apply CallByValue.closureC_to_closure_injective in H; subst cl2 ct2.
constructor...
induction cl2; try (induction t0); discriminate.
(* appl *)
simpl in H1; inversion H1; subst; clear IHt1 IHt2 H1.
inversion H2; subst.
induction v; discriminate.
simpl in H; inversion H; clear H H2; subst.
inversion H0; subst; clear H0.
induction v; discriminate.
induction t2; discriminate.
(* C *)
inversion H1; subst; clear H1 IHt.
inversion H2; subst; clear H2.
induction v; discriminate.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
induction v; discriminate.
induction t; discriminate.
(* final *)
induction c; try discriminate; rewrite CallByValue.dec_context_empty in H; inversion H; subst.
apply CallByValue.valueC_to_value_injective in H1; subst; constructor.
(* apply -> red -> eval *)
assert (CallByValue.dec_by_cls cl c1 (inl (CBV_EAM.UEAM.valueC * CBV_EAM.UEAM.contextC) (t, s, c2))).
rewrite <- H0; apply unf_c_red_correct.
induction c; try discriminate; clear H0 IHc.
(* ap_rC *)
inversion H; subst r c0; clear H.
induction v; inversion H1; clear H1.
(* - v_lamC *)
change (CallByValue.beta_plus (CallByValue.contextC_to_context (ap_rC v0 c)) n (CallByValue.subC_to_sub l) (CallByValue.subC_to_sub l0) t0 = (cl, c1)) in H0.
assert (ht := CallByValue.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByValue.contextC_to_context_injective in H;
change (closureC_to_closure (pairC t s) = closureC_to_closure cl2) in H1;
apply CallByValue.closureC_to_closure_injective in H1; subst; constructor...
simpl in H; induction cl2; try induction t1; discriminate.
(* - v_c_ctC *)
subst; inversion H2; subst; clear H2.
induction v0; discriminate.
rewrite CallByValue.dec_term_value in H; discriminate.
(* C_ctxC *)
inversion H; subst r c0; clear H.
induction v; inversion H1; subst; clear H1.
(* - v_lamC *)
change (CallByValue.beta_plus (CallByValue.contextC_to_context (C_ctxC c)) n (CallByValue.subC_to_sub l) (CallByValue.subC_to_sub l0) t0 = (cl, c1)) in H0.
assert (ht := CallByValue.getB _ _ _ _ _ _ _ H0); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByValue.contextC_to_context_injective in H;
change (closureC_to_closure (pairC t s) = closureC_to_closure cl2) in H1;
apply CallByValue.closureC_to_closure_injective in H1; subst; constructor...
simpl in H; induction cl2; try induction t1; discriminate.
(* - v_c_ctC *)
inversion H2; subst; clear H2.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
discriminate.
(* apply -> red -> apply *)
assert (CallByValue.dec_by_cls cl c1 (inr (CBV_EAM.UEAM.term * CBV_EAM.UEAM.substC * CBV_EAM.UEAM.contextC) (v0, c2))).
rewrite <- H0; apply unf_c_red_correct.
induction c; clear H0; inversion H; subst; induction v; inversion H1; subst; clear H1 H IHc.
(* ap_rC *)
(* - v_lamC *)
change (CallByValue.beta_plus (CallByValue.contextC_to_context (ap_rC v1 c)) n (CallByValue.subC_to_sub l) (CallByValue.subC_to_sub l0) t = (cl, c1)) in H3.
assert (ht := CallByValue.getB _ _ _ _ _ _ _ H3); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByValue.contextC_to_context_injective in H0;
apply CallByValue.closureC_to_closure_injective in H; subst; constructor...
simpl in H; induction cl2; try induction t0; discriminate.
(* - v_c_ctC *)
subst; inversion H2; subst; clear H2.
rewrite <- CallByValue.commutes in H; apply CallByValue.closureC_to_closure_injective in H;
apply CallByValue.valueC_to_closureC_injective in H; apply CallByValue.contextC_to_context_injective in H0;
subst; constructor.
rewrite CallByValue.dec_term_value in H; discriminate.
(* C_ctxC *)
(* - v_lamC *)
change (CallByValue.beta_plus (CallByValue.contextC_to_context (C_ctxC c)) n (CallByValue.subC_to_sub l) (CallByValue.subC_to_sub l0) t = (cl, c1)) in H3.
assert (ht := CallByValue.getB _ _ _ _ _ _ _ H3); destruct ht as [[cl2 ct2] ecl ect]; subst.
inversion H2; subst; clear H2.
apply CallByValue.contextC_to_context_injective in H0;
apply CallByValue.closureC_to_closure_injective in H; subst; constructor...
simpl in H; induction cl2; try induction t0; discriminate.
(* - v_c_ctC *)
inversion H2; subst; clear H2.
induction v0; discriminate.
inversion H; subst; clear H.
inversion H0; subst; clear H0.
change (contextC_to_context c2 = contextC_to_context (ap_lC (CallByValue.C_ctC c0) c)) in H1;
apply CallByValue.contextC_to_context_injective in H1;
change (closureC_to_closure (CallByValue.valueC_to_closureC v0) = closureC_to_closure (CallByValue.valueC_to_closureC (v_c_ctC c))) in H;
apply CallByValue.closureC_to_closure_injective in H; apply CallByValue.valueC_to_closureC_injective in H; subst; constructor.
discriminate.
(* apply -> eval *)
assert (CallByValue.dec_by_cls cl c0 (inl (CBV_EAM.UEAM.valueC * CBV_EAM.UEAM.contextC) (t, s, c1))).
rewrite <- H0; apply unf_c_cls_correct.
induction c; try discriminate; inversion H; subst; clear H H0 IHc.
inversion H1; subst; clear H1.
change (contextC_to_context c1 = contextC_to_context (ap_rC v c2)) in H; apply CallByValue.contextC_to_context_injective in H;
change (closureC_to_closure (pairC t s) = closureC_to_closure c) in H0; apply CallByValue.closureC_to_closure_injective in H0;
subst; constructor.
induction c; try induction t0; discriminate.
(* apply -> apply *)
assert (CallByValue.dec_by_cls cl c0 (inr (CBV_EAM.UEAM.term * CBV_EAM.UEAM.substC * CBV_EAM.UEAM.contextC) (v0, c1))).
rewrite <- H0; apply unf_c_cls_correct.
induction c; try discriminate; inversion H; subst; clear H IHc H0.
inversion H1; subst; clear H1.
change (contextC_to_context c1 = contextC_to_context (ap_rC v c2)) in H0; apply CallByValue.contextC_to_context_injective in H0;
apply CallByValue.closureC_to_closure_injective in H; subst; constructor.
induction c; try induction t; discriminate.
Qed.
Hint Resolve transition_unf_z.

Lemma trans_close_unf_z : forall c c0, CBV_EAM.trans_close c c0 -> trans_close c c0.
Proof with eauto.
induction 1; [constructor | econstructor 2]...
Qed.
Hint Resolve trans_close_unf_z.

Lemma evalUnfZinc : forall t v, CBV_EAM.eval t v -> eval t v.
Proof with auto.
intros t v H; constructor; inversion_clear H; inversion H0; inversion H; subst...
Qed.
Hint Resolve evalUnfZinc.

Lemma transition_z_unf : forall c c0, transition c c0 -> CBV_EAM.transition c c0.
Proof with eauto with ref.
induction 1.
(* init *)
constructor.
(* lam -> apply *)
assert (ha : CBV_EAM.UEAM.dec_term (pairC (lam n t) s) (ct:context) = in_dec (d_red (CallByValue.r_lam n t (s:subst)) (ct:context)))...
assert (hb : contract (CallByValue.r_lam n t (s:subst)) (ct:context) = Some (closureC_to_closure (CallByValue.valueC_to_closureC v), ct0:context)).
simpl; f_equal...
constructor 4 with (ct : context) (ct0 : context) (CallByValue.r_lam n t (s:subst)) _ ha hb...
unfold CBV_EAM.unf_red; unfold CBV_EAM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* lam -> eval *)
assert (ha : CBV_EAM.UEAM.dec_term (pairC (lam n t) s) (ct:context) = in_dec (d_red (CallByValue.r_lam n t (s:subst)) (ct:context)))...
assert (hb : contract (CallByValue.r_lam n t (s:subst)) (ct:context) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 3 with (ct : context) (ct0 : context) (CallByValue.r_lam n t (s:subst)) _ ha hb...
unfold CBV_EAM.unf_red; unfold CBV_EAM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; subst; [repeat f_equal | destruct v; discriminate | destruct t0; discriminate]...
(* var -> eval *)
assert (ha : CBV_EAM.UEAM.dec_term (pairC (var n) s) (c:context) = in_dec (d_red (CallByValue.r_get n (s:subst)) (c:context)))...
constructor 3 with (c:context) (c0:context) (CallByValue.r_get n (s:subst)) _ ha H.
unfold CBV_EAM.unf_red; unfold CBV_EAM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; subst; [repeat f_equal | destruct v; discriminate | destruct t; discriminate]...
(* var -> apply *)
assert (ha : CBV_EAM.UEAM.dec_term (pairC (var n) s) (c:context) = in_dec (d_red (CallByValue.r_get n (s:subst)) (c:context)))...
constructor 4 with (c : context) (c1 : context) (CallByValue.r_get n (s:subst)) _ ha H...
unfold CBV_EAM.unf_red; unfold CBV_EAM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; try (destruct v; discriminate); repeat f_equal...
(* appl -> eval *)
assert (ha : CBV_EAM.UEAM.dec_term (pairC (appl t0 t1) s) (c:context) = in_dec (d_red (CallByValue.r_app t0 t1 (s:subst)) (c:context)))...
assert (hb : contract (CallByValue.r_app t0 t1 (s:subst)) (c:context) = Some (CallByValue.comp (closureC_to_closure (pairC t0 s)) (closureC_to_closure (pairC t1 s)),  c:context)).
simpl; f_equal...
constructor 3 with (c:context) (contextC_to_context c) (CallByValue.r_app t0 t1 (s:subst)) _ ha hb...
unfold CBV_EAM.unf_red; unfold CBV_EAM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
injection H; intros; subst; inversion H0; subst; [ repeat f_equal | destruct v; discriminate | destruct t1; discriminate]...
apply CallByValue.substC_to_subst_injective in H3; subst...
(* C -> eval *)
assert (ha : CBV_EAM.UEAM.dec_term (pairC (C t) s) (c:context) = in_dec (d_red (CallByValue.r_C t (s:subst)) (c:context)))...
assert (hb : contract (CallByValue.r_C t (s:subst)) (c:context) = Some (CallByValue.C_cl (closureC_to_closure (pairC t s)),  c:context)).
simpl; f_equal...
constructor 3 with (c:context) (contextC_to_context c) (CallByValue.r_C t (s:subst)) _ ha hb.
unfold CBV_EAM.unf_red; unfold CBV_EAM.UEAM.unf_red; destruct CallByValue.unfold_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
injection H; intros; subst; inversion H0; subst; [repeat f_equal | destruct v; discriminate | destruct t; discriminate]...
(* final *)
constructor...
(* ap_rC v_lamC -> apply *)
assert (ha : CBV_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (ap_rC v ct)) = CBV_EAM.UEAM.in_dec (CBV_EAM.UEAM.d_red (CallByValue.r_beta (valueC_to_value (v_lamC n t s l)) (CallByValue.valueC_to_value v)) (contextC_to_context ct)))...
assert (hb : contract (CallByValue.r_beta (valueC_to_value(v_lamC n t s l)) (v:value)) (ct:context) = Some (closureC_to_closure (CallByValue.valueC_to_closureC v0), ct0:context)).
simpl; f_equal...
constructor 10 with _ _ (CallByValue.r_beta (valueC_to_value (v_lamC n t s l)) (v:value)) _ ha hb...
unfold CBV_EAM.unf_c_red; unfold CBV_EAM.UEAM.unf_c_red; destruct CallByValue.unfold_c_red as [p peq].
inversion peq; subst; try (destruct v0; discriminate); repeat f_equal...
(* ap_rC v_lamC -> eval *)
assert (ha : CBV_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (ap_rC v ct)) = CBV_EAM.UEAM.in_dec (CBV_EAM.UEAM.d_red (CallByValue.r_beta (valueC_to_value (v_lamC n t s l)) (valueC_to_value v)) (contextC_to_context ct)))...
assert (hb : contract (CallByValue.r_beta (valueC_to_value(v_lamC n t s l)) (v:value)) (ct:context) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 9 with _ _ (CallByValue.r_beta (valueC_to_value (v_lamC n t s l)) (v:value)) _ ha hb.
unfold CBV_EAM.unf_c_red; unfold CBV_EAM.UEAM.unf_c_red; destruct CallByValue.unfold_c_red as [p peq].
inversion peq; subst; [repeat f_equal | destruct v0; discriminate | destruct t0; discriminate]...
(* ap_rC v_c_ctC -> apply *)
assert (ha : CBV_EAM.UEAM.dec_context (valueC_to_value (v_c_ctC ct0)) (contextC_to_context (ap_rC v ct)) = CBV_EAM.UEAM.in_dec (CBV_EAM.UEAM.d_red (CallByValue.r_beta (valueC_to_value (v_c_ctC ct0)) (valueC_to_value v)) (contextC_to_context ct)))...
assert (hb : contract (CallByValue.r_beta (valueC_to_value(v_c_ctC ct0)) (v:value)) (ct:context) = Some (closureC_to_closure (CallByValue.valueC_to_closureC v), ct0:context)).
simpl; repeat f_equal; change (CallByValue.value_to_closure (CallByValue.valueC_to_value v) = CallByValue.closureC_to_closure (CallByValue.valueC_to_closureC v)); rewrite CallByValue.commutes...
constructor 10 with (ct:context) _ (CallByValue.r_beta (valueC_to_value (v_c_ctC ct0)) (v:value)) (closureC_to_closure (CallByValue.valueC_to_closureC v)) ha hb...
unfold CBV_EAM.unf_c_red; unfold CBV_EAM.UEAM.unf_c_red; destruct CallByValue.unfold_c_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* ap_lC -> apply *)
assert (ha : CBV_EAM.UEAM.dec_context (v0:value) (contextC_to_context (ap_lC (CallByValue.valueC_to_closureC v) ct)) = CBV_EAM.UEAM.in_term (closureC_to_closure (CallByValue.valueC_to_closureC v)) (contextC_to_context (ap_rC v0 ct)))...
constructor 13 with (contextC_to_context (ap_rC v0 ct)) (closureC_to_closure (CallByValue.valueC_to_closureC v)) ha...
unfold CBV_EAM.unf_c_cls; unfold CBV_EAM.UEAM.unf_c_cls; destruct CallByValue.unfold_c_cls as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* ap_lC -> eval *)
assert (ha : CBV_EAM.UEAM.dec_context (v:value) (contextC_to_context (ap_lC (pairC t s) ct)) = CBV_EAM.UEAM.in_term (closureC_to_closure (pairC t s)) (contextC_to_context (ap_rC v ct)))...
constructor 12 with (contextC_to_context (ap_rC v ct)) (closureC_to_closure (pairC t s)) ha...
unfold CBV_EAM.unf_c_cls; unfold CBV_EAM.UEAM.unf_c_cls; destruct CallByValue.unfold_c_cls as [p peq].
inversion peq; subst; [repeat f_equal | destruct v0; discriminate | destruct t; discriminate]...
(* C_ctxC v_lamC -> apply *)
assert (ha : CBV_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (C_ctxC ct)) = CBV_EAM.UEAM.in_dec (CBV_EAM.UEAM.d_red (CallByValue.r_vct (valueC_to_value (v_lamC n t s l))) (contextC_to_context ct)))...
assert (hb : contract (CallByValue.r_vct (valueC_to_value(v_lamC n t s l))) (ct:context) = Some (closureC_to_closure (CallByValue.valueC_to_closureC v), ct0:context)).
simpl; f_equal...
constructor 10 with _ _ (CallByValue.r_vct (valueC_to_value (v_lamC n t s l))) _ ha hb...
unfold CBV_EAM.unf_c_red; unfold CBV_EAM.UEAM.unf_c_red; destruct CallByValue.unfold_c_red as [p peq].
inversion peq; subst; try (destruct v; discriminate); repeat f_equal...
(* C_ctxC v_lamC -> eval *)
assert (ha : CBV_EAM.UEAM.dec_context (valueC_to_value (v_lamC n t s l)) (contextC_to_context (C_ctxC ct)) = CBV_EAM.UEAM.in_dec (CBV_EAM.UEAM.d_red (CallByValue.r_vct (valueC_to_value (v_lamC n t s l))) (contextC_to_context ct)))...
assert (hb : contract (CallByValue.r_vct (valueC_to_value(v_lamC n t s l))) (ct:context) = Some (closureC_to_closure (pairC t0 s0), ct0:context)).
simpl; f_equal...
constructor 9 with _ _ (CallByValue.r_vct (valueC_to_value (v_lamC n t s l))) _ ha hb.
unfold CBV_EAM.unf_c_red; unfold CBV_EAM.UEAM.unf_c_red; destruct CallByValue.unfold_c_red as [p peq].
inversion peq; subst; [repeat f_equal | destruct v; discriminate | destruct t0; discriminate]...
(* C_ctxC v_c_ctC -> apply *)
assert (ha : CBV_EAM.UEAM.dec_context (valueC_to_value (v_c_ctC ct0)) (contextC_to_context (C_ctxC ct)) = CBV_EAM.UEAM.in_dec (CBV_EAM.UEAM.d_red (CallByValue.r_vct (valueC_to_value (v_c_ctC ct0))) (contextC_to_context ct)))...
assert (hb : contract (CallByValue.r_vct (valueC_to_value(v_c_ctC ct0))) (ct:context) = Some (CallByValue.comp (closureC_to_closure (CallByValue.C_ctC ct0)) (closureC_to_closure (CallByValue.C_ctC ct)), ct:context)).
simpl; repeat f_equal...
constructor 10 with (ct:context) _ (CallByValue.r_vct (valueC_to_value (v_c_ctC ct0))) (CallByValue.comp (closureC_to_closure (CallByValue.C_ctC ct0)) (closureC_to_closure (CallByValue.C_ctC ct))) ha hb.
unfold CBV_EAM.unf_c_red; unfold CBV_EAM.UEAM.unf_c_red; destruct CallByValue.unfold_c_red as [p peq].
inversion peq; subst.
destruct v; discriminate.
injection H; intros; subst; inversion H0; subst; [repeat f_equal | discriminate]...
Qed.
Hint Resolve transition_z_unf.

Lemma trans_close_z_unf : forall c c0, trans_close c c0 -> CBV_EAM.trans_close c c0.
Proof with eauto.
induction 1; [constructor | econstructor 2]...
Qed.
Hint Resolve trans_close_z_unf.

Lemma evalZincUnf : forall t v, eval t v -> CBV_EAM.eval t v.
Proof with auto.
intros t v H; constructor; inversion_clear H; inversion H0; inversion H; subst...
Qed.
Hint Resolve evalZincUnf.

Theorem EAMachineCorrect : forall t (v:valueC), eval_CBV t (valueC_to_value v) <-> eval t v.
Proof with auto.
intros; rewrite eval_equiv; rewrite CBV_EAM.evalMachine; split...
Qed.

End EAMachine.