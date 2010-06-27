Require Export Wellfounded.Transitive_Closure.
Require Export Relations.
Require Export Relation_Operators.
Require Export List.
Require Import Setoid.

Ltac isda := intros; simpl in *; try discriminate; auto.

Section tcl.

Variable A : Type.
Variable R : relation A.

Notation trans_clos := (clos_trans A R).
Notation trans_clos_l := (clos_trans_1n A R).
Notation trans_clos_r := (clos_trans_n1 A R).

Lemma exl : forall x y, trans_clos x y -> R x y \/ exists z, R x z /\ trans_clos z y.
Proof with auto.
  induction 1.
  left...
  right; clear IHclos_trans2; destruct IHclos_trans1 as [H1 | [u [H1 H2]]].
  exists y...
  exists u; split; [ assumption | econstructor 2; eauto].
Qed.

Lemma exr : forall x y, trans_clos x y -> R x y \/ exists z, R z y /\ trans_clos x z.
Proof with auto.
  induction 1.
  left...
  right; clear IHclos_trans1; destruct IHclos_trans2 as [H1 | [u [H1 H2]]].
  exists y...
  exists u; split; [ assumption | econstructor 2; eauto].
Qed.

Lemma tcl_l_h : forall x y z, trans_clos x y -> trans_clos_l y z -> trans_clos_l x z.
Proof with eauto.
  induction 1; intros...
  econstructor 2...
Qed.

Lemma tcl_l : forall x y, trans_clos x y <-> trans_clos_l x y.
Proof with eauto.
  split; induction 1; intros...
  constructor...
  eapply tcl_l_h...
  constructor...
  econstructor 2...
  constructor...
Qed.

Lemma tcl_r_h : forall x y z, trans_clos y z -> trans_clos_r x y -> trans_clos_r x z.
Proof with eauto.
  induction 1; intros...
  econstructor 2...
Qed.

Lemma tcl_r : forall x y, trans_clos x y <-> trans_clos_r x y.
Proof with eauto.
  split; induction 1; intros.
  constructor...
  eapply tcl_r_h...
  constructor...
  econstructor 2...
  constructor...
Qed.

Lemma Acc_tcl_l : forall x, Acc trans_clos x -> Acc trans_clos_l x.
Proof with auto.
  induction 1.
  constructor; intros.
  apply H0; rewrite tcl_l...
Qed.

Theorem wf_clos_trans_l : well_founded R -> well_founded trans_clos_l.
Proof with auto.
  intros H a; apply Acc_tcl_l; apply wf_clos_trans...
Qed.

Lemma Acc_tcl_r : forall x, Acc trans_clos x -> Acc trans_clos_r x.
Proof with auto.
  induction 1.
  constructor; intros.
  apply H0; rewrite tcl_r...
Qed.

Theorem wf_clos_trans_r : well_founded R -> well_founded trans_clos_r.
Proof with auto.
  intros H a; apply Acc_tcl_r; apply wf_clos_trans...
Qed.

End tcl.

Definition opt_to_list {T} (o : option T) : list T :=
  match o with
  | None => nil
  | Some x => x :: nil
  end.

Section map_injective.

  Variables A B : Set.
  Variable f : A -> B.
  Hypothesis f_injective : forall a a0 : A, f a = f a0 -> a = a0.

  Lemma map_injective : forall l l0, map f l = map f l0 -> l = l0.
  Proof.
    induction l; destruct l0; intro H; inversion H; f_equal; auto.
  Qed.

End map_injective.

Section streams.

  Variable A : Set.

  CoInductive stream :=
  | s_nil : stream
  | s_cons : A -> stream -> stream.

  CoInductive bisim_stream : stream -> stream -> Prop :=
  | b_nil : bisim_stream s_nil s_nil
  | b_cons : forall (x : A) (s0 s1 : stream), bisim_stream s0 s1 -> bisim_stream (s_cons x s0) (s_cons x s1).

End streams.

Implicit Arguments s_nil [A].
Implicit Arguments s_cons [A].
Implicit Arguments bisim_stream [A].
Implicit Arguments b_nil [A].
Implicit Arguments b_cons [A x s0 s1].
