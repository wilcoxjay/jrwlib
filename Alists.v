Require Import EQsig ANYsig.
Require Import Tactics.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Module Type ALIST.
  Declare Module Key : EQ.
  Parameter t : Type -> Type.
  Parameter empty : forall V, t V.
  Parameter get : forall V, t V -> Key.t -> option V.
  Parameter set : forall V, t V -> Key.t -> V -> t V.
  (* Parameter del : forall V, t V -> Key.t -> t V. *)

  Axiom get_empty : forall V k, get (empty V) k = None.
  Axiom get_set : forall V a k1 k2 (v1 : V),
      get (set a k1 v1) k2 =
      if Key.eq_dec k1 k2 then Some v1 else get a k2.
End ALIST.

Module Type MONO_ALIST.
  Declare Module Key : EQ.
  Declare Module Value : ANY.

  Parameter t :  Type.
  Parameter empty : t.
  Parameter get : t -> Key.t -> option Value.t.
  Parameter set : t -> Key.t -> Value.t -> t.

  Axiom get_empty : forall k, get empty k = None.
  Axiom get_set : forall a k1 k2 (v1 : Value.t),
      get (set a k1 v1) k2 =
      if Key.eq_dec k1 k2 then Some v1 else get a k2.
End MONO_ALIST.

Module SpecializeAlist(A : ALIST)(V : ANY) <: MONO_ALIST.
  Module Key := A.Key.
  Module Value := V.

  Definition t := A.t Value.t.
  Definition empty := A.empty Value.t.
  Definition get := @A.get Value.t.
  Definition set := @A.set Value.t.
  Definition get_empty := @A.get_empty Value.t.
  Definition get_set := @A.get_set Value.t.
End SpecializeAlist.

Module Type ALIST_UTIL.
  Include ALIST.

  Parameter equiv : forall V, t V -> t V -> Prop.
  Axiom equiv_get : forall V (a1 a2 : t V) k, equiv a1 a2 -> get a1 k = get a2 k.
  Axiom equiv_refl : forall V (a : t V), equiv a a.
  Axiom equiv_sym : forall V (a1 a2 : t V), equiv a1 a2 -> equiv a2 a1.
  Axiom equiv_trans : forall V (a1 a2 a3 : t V), equiv a1 a2 -> equiv a2 a3 -> equiv a1 a3.

  Axiom set_preserves_equiv : forall V (a1 a2 : t V) k v, equiv a1 a2 ->
                                                     equiv (set a1 k v) (set a2 k v).

  Axiom set_swap_neq : forall V (a : t V) k1 k2 v1 v2,
      k1 <> k2 ->
      equiv (set (set a k1 v1) k2 v2) (set (set a k2 v2) k1 v1) .

End ALIST_UTIL.

Module Alist_Util (A : ALIST) <: ALIST_UTIL.
  Include A.

  Section util.
    Variable V : Type.
    Definition equiv (a1 a2 : t V) : Prop :=
      forall k, get a1 k = get a2 k.

    Lemma equiv_get : forall a1 a2 k, equiv a1 a2 -> get a1 k = get a2 k.
    Proof. auto. Qed.

    Lemma equiv_refl : forall a1, equiv a1 a1.
    Proof. unfold equiv. auto. Qed.

    Lemma equiv_sym : forall a1 a2, equiv a1 a2 -> equiv a2 a1.
    Proof. unfold equiv. auto. Qed.

    Lemma equiv_trans : forall a1 a2 a3, equiv a1 a2 -> equiv a2 a3 -> equiv a1 a3.
    Proof. unfold equiv. intros a1 a2 a3 H12 H23 k. now rewrite H12, H23. Qed.

    Lemma set_preserves_equiv : forall a1 a2 k v, equiv a1 a2 ->
                                             equiv (set a1 k v) (set a2 k v).
    Proof.
      unfold equiv.
      intros.
      rewrite !A.get_set.
      break_if; auto.
    Qed.

    Lemma set_swap_neq : forall a k1 k2 v1 v2,
      k1 <> k2 ->
      equiv (set (set a k1 v1) k2 v2) (set (set a k2 v2) k1 v1) .
    Proof.
      unfold equiv.
      intros.
      rewrite !A.get_set.
      repeat break_match; try congruence.
    Qed.
  End util.
End Alist_Util.

Module Type MONO_ALIST_UTIL.
  Include MONO_ALIST.

  Parameter equiv : t -> t -> Prop.
  Axiom equiv_get : forall (a1 a2 : t) k, equiv a1 a2 -> get a1 k = get a2 k.
  Axiom equiv_refl : forall (a : t), equiv a a.
  Axiom equiv_sym : forall (a1 a2 : t), equiv a1 a2 -> equiv a2 a1.
  Axiom equiv_trans : forall (a1 a2 a3 : t), equiv a1 a2 -> equiv a2 a3 -> equiv a1 a3.

  Axiom set_preserves_equiv : forall a1 a2 k v, equiv a1 a2 ->
                                             equiv (set a1 k v) (set a2 k v).

  Axiom set_swap_neq : forall a k1 k2 v1 v2,
      k1 <> k2 ->
      equiv (set (set a k1 v1) k2 v2) (set (set a k2 v2) k1 v1) .
End MONO_ALIST_UTIL.

Module SpecializeAlistUtil(A : ALIST_UTIL)(V : ANY) <: MONO_ALIST_UTIL.
  Module S := SpecializeAlist(A)(V).
  Include S.

  Definition equiv := @A.equiv Value.t.
  Definition equiv_get := @A.equiv_get Value.t.
  Definition equiv_refl := @A.equiv_refl Value.t.
  Definition equiv_sym := @A.equiv_sym Value.t.
  Definition equiv_trans := @A.equiv_trans Value.t.

  Definition set_preserves_equiv := @A.set_preserves_equiv Value.t.
  Definition set_swap_neq := @A.set_swap_neq Value.t.
End SpecializeAlistUtil.

Module Alist(K : EQ) : ALIST with Definition Key.t := K.t.
  Module Key := K.
  Section alist.
    Variable V : Type.
    Definition t := list (Key.t * V).
    Definition empty : t := [].
    Fixpoint get (a : t) (k : Key.t) : option V :=
      match a with
      | [] => None
      | (k',v') :: xs => if Key.eq_dec k k' then Some v' else get xs k
      end.
    Definition set (a : t) (k : Key.t) (v : V) : t := (k, v) :: a.

    Lemma get_empty : forall k, get empty k = None.
    Proof. auto. Qed.

    Lemma get_set : forall a k1 k2 (v1 : V),
      get (set a k1 v1) k2 =
      if Key.eq_dec k1 k2 then Some v1 else get a k2.
    Proof.
      unfold get, set; intuition; repeat break_match; congruence.
    Qed.
  End alist.
End Alist.
