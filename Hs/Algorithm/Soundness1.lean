
import Hs.HsTerm
import Hs.Algorithm
import Hs.Monad

import SystemFD.Term
import Batteries.Lean.Except

theorem compile_kind_sound (k : HsTerm) :
  ⊢ Γ ->
  c = □ ->
  compile_kind Γ c k = .ok k' ->
  Γ ⊢ k' : □ := by
intro wf e1 j;
induction c, k using compile_kind.induct generalizing k' <;> simp at *
case _ => cases j; constructor; assumption
case _ k1 k2 ih1 ih2 =>
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w1 j =>
  cases j; case _ h1 j =>
  rw[Except.bind_eq_ok] at j;
  cases j; case _ w2 j =>
  cases j; case _ h2 j =>
  cases j;
  simp_all;
  constructor; assumption; assumption
