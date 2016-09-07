(* -*- coding: utf-8 -*- *)

Require Import Coq.Program.Basics.

Module Typeclasses.

Local Open Scope program_scope.

Class Functor f := {
  fmap {A B} : (A -> B) -> f A -> f B;
  functor_hom : forall {A B C} (g : B -> C) (h : A -> B) x,
    fmap (g ∘ h) x = (fmap g ∘ fmap h) x;
  functor_id : forall A x, @fmap A A id x = id x
}.

Reserved Notation "a <*> b" (at level 40).

Class Applicative f:= {
  applic_is_functor :> Functor f;
  pure : forall {A}, A -> f A;
  comb : forall {A B}, f (A -> B) -> f A -> f B;
  applic_id : forall {A} (x : f A), comb (pure id) x = x;
  applic_hom : forall {A B} (f : A -> B) x,
    comb (pure f) (pure x) = pure (f x);
  applic_inter : forall {A B} (u : f (A -> B)) y,
    comb u (pure y) = comb (pure (fun f => f y)) u;
  applic_comp : forall {A B C} (u : f (B -> C)) (v : f (A -> B)) w,
    comb u (comb v w) = comb (comb (comb (pure compose) u) v) w
}.

Class Alternative f := {
  altern_is_applic :> Applicative f;
  altern_empty : forall {A}, f A;
  altern_or    : forall {A}, f A -> f A -> f A;
  altern_left_empty : forall {A} x,
    @altern_or A altern_empty x = x;
  altern_right_empty : forall {A} x,
    @altern_or A x altern_empty = x;
  altern_assoc : forall {A} x y z,
    @altern_or A (altern_or x y) z = altern_or x (altern_or y z)
}.

Instance option_Functor : Functor option := {
  fmap A B f m := match m with | None => None | Some m' => Some (f m') end
}.
Proof.
  destruct x; auto.
  destruct x; auto.
Defined.

Instance option_Applicative : Applicative option := {
  pure A x := Some x;
  comb A B f x := match f with | None => None | Some f' => fmap f' x end
}.
Proof.
  destruct x; auto.
  auto.
  auto.
  destruct w; destruct v; destruct u; auto.
Defined.

Instance option_Alternative : Alternative option := {
  altern_empty A := None;
  altern_or A l r := match l with None => r | Some x => Some x end
}.
Proof.
  auto.
  destruct x; auto.
  destruct x; auto.
Defined.

Local Close Scope program_scope.

End Typeclasses.

