Require Import Coq.Lists.List.
Import ListNotations.
Require Import Tactics.

Require Import Omega.

Set Implicit Arguments.

Section subseq.
  Variable A : Type.
  Fixpoint subseq (xs ys : list A) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => match ys with
               | [] => False
               | y :: ys' => subseq xs ys' \/ (x = y /\ subseq xs' ys')
               end
  end.

  Lemma subseq_In :
    forall xs ys x,
      subseq xs ys ->
      In x xs ->
      In x ys.
  Proof.
    intros. generalize dependent xs.
    induction ys; simpl; intros; break_match; intuition; subst; simpl in *;
      intuition (subst; eauto with * ).
  Qed.

  Lemma subseq_NoDup :
    forall xs ys,
      NoDup ys ->
      subseq xs ys ->
      NoDup xs.
  Proof.
    intros. generalize dependent xs.
    induction ys; simpl; intros; break_match; intuition; subst.
    - constructor.
    - apply IHys; auto. invc H; auto.
    - invc H. constructor; auto.
      intuition. eauto using subseq_In.
  Qed.
End subseq.

Section remove_all.
  Variable A : Type.
  Hypothesis (A_eq_dec : forall x y : A, {x = y} + {x <> y}).

  Fixpoint remove_all xs ys : list A :=
    match xs with
    | [] => ys
    | x :: xs' => remove A_eq_dec x (remove_all xs' ys)
    end.

  Lemma in_remove_elim_weak : forall y x ys, In y (remove A_eq_dec x ys) -> In y ys.
  Proof.
    induction ys; simpl; intuition.
    break_if.
    - subst. intuition.
    - simpl in *. intuition.
  Qed.

  Lemma in_remove_elim : forall y x ys, In y (remove A_eq_dec x ys) -> x <> y /\ In y ys.
  Proof.
    split.
    - intro Hx. subst. eapply remove_In; eauto.
    - eauto using in_remove_elim_weak.
  Qed.

  Lemma in_remove_intro : forall y x ys, x <> y -> In y ys -> In y (remove A_eq_dec x ys).
  Proof.
    induction ys; simpl; intuition; break_if; simpl; intuition.
    congruence.
  Qed.

  Lemma in_remove_all_elim_weak : forall y xs ys,
      In y (remove_all xs ys) -> In y ys.
  Proof.
    induction xs; simpl; intuition eauto using in_remove_elim_weak.
  Qed.

  Lemma in_remove_all_elim_strong : forall y xs ys,
      In y (remove_all xs ys) -> In y ys /\ ~ In y xs.
  Proof.
    induction xs; simpl; intuition.
    - find_apply_lem_hyp in_remove_elim_weak. firstorder.
    - subst. eapply remove_In; eauto.
    - find_apply_lem_hyp in_remove_elim_weak. firstorder.
  Qed.

  Lemma in_remove_all_intro :
    forall y xs ys,
      ~ In y xs ->
      In y ys ->
      In y (remove_all xs ys).
  Proof.
    induction xs; simpl; intuition auto using in_remove_intro.
  Qed.
End remove_all.


Section disjoint.
  Variable A : Type.

  Fixpoint disjoint (xs ys : list A) : Prop :=
    match xs with
    | [] => True
    | x :: xs' => (~ In x ys) /\ disjoint xs' ys
    end.

  Hypothesis (A_eq_dec : forall x y : A, {x = y} + {x <> y}).

  Fixpoint disjoint_dec  xs ys : bool :=
    match xs with
    | [] => true
    | x :: xs' => if in_dec A_eq_dec x ys then false else disjoint_dec xs' ys
    end.

  Lemma disjoint_dec_sound :
    forall xs ys,
      disjoint_dec xs ys = true ->
      disjoint xs ys.
  Proof.
    induction xs; simpl; intuition; break_if; try congruence; auto.
  Qed.

  Lemma disjoint_dec_complete :
    forall xs ys,
      disjoint xs ys ->
      disjoint_dec xs ys = true.
  Proof.
    induction xs; simpl; intuition; break_if; try congruence; auto.
  Qed.

  Lemma disjoint_nil_r_intro : forall xs, disjoint xs [].
  Proof.
    induction xs; simpl; auto.
  Qed.

  Lemma disjoint_cons_r_intro :
    forall xs y ys,
      ~ In y xs ->
      disjoint xs ys ->
      disjoint xs (y :: ys).
  Proof.
    induction xs; simpl; intuition.
  Qed.

  Lemma disjoint_sym : forall xs ys, disjoint xs ys -> disjoint ys xs.
  Proof.
    induction xs; simpl; intros; intuition.
    - auto using disjoint_nil_r_intro.
    - apply disjoint_cons_r_intro; intuition.
  Qed.

  Lemma disjoint_cons_r_elim :
    forall xs y ys,
      disjoint xs (y :: ys) ->
      disjoint xs ys /\ (In y xs -> False).
  Proof.
    intros. apply disjoint_sym in H. simpl in *. intuition auto using disjoint_sym.
  Qed.

  Lemma disjoint_contradiction :
    forall x xs ys,
      In x xs ->
      In x ys ->
      disjoint xs ys ->
      False.
  Proof.
    induction xs; simpl; intuition eauto.
    subst. auto.
  Qed.

  Lemma disjoint_intro :
    forall xs ys,
      (forall x y, In x xs -> In y ys -> x <> y) ->
      disjoint xs ys.
  Proof.
    induction xs; simpl; intuition eauto.
  Qed.

  Lemma disjoint_proper_l : forall xs xs' ys,
      disjoint xs' ys ->
      (forall x, In x xs -> In x xs') ->
      disjoint xs ys.
  Proof.
    induction xs; simpl; intuition eauto using disjoint_contradiction.
  Qed.

  Lemma disjoint_app_elim : forall xs ys zs, disjoint (xs ++ ys) zs ->
                                       disjoint xs zs /\ disjoint ys zs.
  Proof.
    induction xs; simpl; firstorder.
  Qed.

  Lemma disjoint_app_intro : forall (xs ys zs : list A),
      disjoint xs zs ->
      disjoint ys zs ->
      disjoint (xs ++ ys) zs.
  Proof.
    induction xs; simpl; firstorder.
  Qed.

  Lemma disjoint_remove_elim :
    forall x ys zs,
      disjoint (remove A_eq_dec x zs) ys ->
      ~ In x ys ->
      disjoint zs ys.
  Proof.
    induction zs; simpl; intuition.
    - break_match; simpl in *; intuition. congruence.
    - break_match; simpl in *; intuition.
  Qed.

  Lemma disjoint_remove_all_elim :
    forall xs ys zs,
      disjoint xs ys ->
      disjoint (remove_all A_eq_dec xs zs) ys ->
      disjoint zs ys.
  Proof.
    induction xs; simpl; intuition.
    apply disjoint_remove_elim in H0; intuition.
  Qed.
End disjoint.

Module list_rel.
  Section list_rel.
    Variable A B : Type.
    Variable R : A -> B -> Prop.
    Inductive t : list A -> list B -> Prop :=
    | nil : t [] []
    | cons : forall x y xs ys, R x y -> t xs ys -> t (x :: xs) (y :: ys).
    Hint Constructors t.
  End list_rel.
  Hint Constructors t.

  Section same.
    Variable A : Type.
    Variable R : A -> A -> Prop.

    Lemma refl_intro : (forall x, R x x) -> forall xs, t R xs xs.
    Proof.
      induction xs; auto.
    Qed.

    Lemma refl_intro_strong : forall xs, (forall x, In x xs -> R x x) -> t R xs xs.
    Proof.
      induction xs; intros; auto with *.
    Qed.

    Lemma sym_intro : (forall x y, R x y -> R y x) -> forall xs ys, t R xs ys -> t R ys xs.
    Proof.
      intro H. induction 1; auto.
    Qed.

    Lemma sym_intro_strong :
      forall xs ys,
        t (fun x y => R x y -> R y x) xs ys -> t R xs ys -> t R ys xs.
    Proof.
      intro H. induction 1; auto.
      inversion 1; subst. auto.
    Qed.

    Lemma trans_intro_strong :
      forall xs ys,
        t (fun x y => R x y -> forall z, R y z -> R x z) xs ys ->
        t R xs ys ->
        forall zs, t R ys zs -> t R xs zs.
    Proof.
      intro H. induction 1; auto.
      inversion 1; subst. intros. invc H2. auto.
    Qed.
  End same.

  Fixpoint dec {A : Type} (R_dec : A -> A -> bool) xs ys : bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => R_dec x y && dec R_dec xs' ys'
    | _, _ => false
    end.

  Lemma dec_sound :
    forall A (R : A -> A -> Prop) (R_dec : A -> A -> bool) xs ys,
      (forall x y, R_dec x y = true -> R x y) ->
      dec R_dec xs ys = true ->
      t R xs ys.
  Proof.
    induction xs; simpl; intros; break_match; auto; try congruence;
      try find_apply_lem_hyp Bool.andb_true_iff; intuition.
  Qed.

  Lemma dec_complete :
    forall A (R : A -> A -> Prop) (R_dec : A -> A -> bool) xs ys,
      (forall x y, R x y -> R_dec x y = true) ->
      t R xs ys ->
      dec R_dec xs ys = true.
  Proof.
    induction xs; simpl; intros; break_match; auto; solve_by_inversion.
  Qed.
End list_rel.


Fixpoint sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

Lemma in_sum : forall n l, In n l -> n <= sum l.
Proof.
  induction l; simpl; intuition.
Qed.

Section dedup.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Fixpoint dedup (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => let tail := dedup xs in
                 if in_dec A_eq_dec x xs then
                   tail
                 else
                   x :: tail
    end.

  Lemma dedup_In : forall (x : A) xs,
      In x xs ->
      In x (dedup xs).
  Proof.
    induction xs; simpl; intuition; break_if; subst; intuition.
  Qed.

  Lemma dedup_app : forall (xs ys : list A),
      disjoint xs ys ->
      dedup (xs ++ ys) = dedup xs ++ dedup ys.
  Proof.
    induction xs; simpl; intuition; repeat break_match; intuition.
    - exfalso. apply in_app_or in i; intuition.
    - exfalso. apply n. apply in_or_app. auto.
    - simpl. auto using f_equal.
  Qed.

  Lemma in_dedup_was_in :
    forall xs (x : A),
      In x (dedup xs) ->
      In x xs.
  Proof.
    induction xs; intros.
    - simpl in *; intuition.
    - simpl in *. break_if; simpl in *; intuition.
  Qed.

  Lemma NoDup_dedup :
    forall (xs : list A),
      NoDup (dedup xs).
  Proof.
    induction xs.
    - simpl. constructor.
    - simpl. break_if; auto.
      constructor; auto.
      intro.
      apply n.
      eapply in_dedup_was_in; eauto.
  Qed.

  Lemma remove_preserve :
    forall (x y : A) xs,
      x <> y ->
      In y xs ->
      In y (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - intuition.
    - simpl in *.
      concludes.
      intuition; break_if; subst; try congruence; intuition.
  Qed.

  Lemma remove_dedup_comm : forall (x : A) xs,
      remove A_eq_dec x (dedup xs) =
      dedup (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - auto.
    - simpl. repeat (break_match; simpl); auto.
      + exfalso. apply n0. apply remove_preserve; auto.
      + exfalso. apply n. eapply in_remove_elim_weak; eauto.
      + f_equal. auto.
  Qed.

  Lemma remove_not_in : forall (x : A) xs,
      ~ In x xs ->
      remove A_eq_dec x xs = xs.
  Proof.
    intros. induction xs.
    - intuition.
    - simpl. break_match.
      + exfalso. apply H.
        subst. intuition.
      + f_equal. apply IHxs.
        intro Hin.
        apply H. simpl. intuition.
  Qed.

  Lemma dedup_NoDup_id : forall (xs : list A),
      NoDup xs -> dedup xs = xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl. invc H. concludes. rewrite IHxs.
      break_if; congruence.
  Qed.

  Lemma dedup_not_in_cons :
    forall x xs,
      (~ In x xs) ->
      x :: dedup xs = dedup (x :: xs).
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. intuition. repeat break_match; intuition.
  Qed.
End dedup.
