import SystemFD.Substitution
import SystemFD.Ctx
import SystemFD.Term.Definition
import SystemFD.Term.Substitution

namespace List
  @[simp]
  def inter [BEq T] (l1 l2 : List T) : List T := filter (elem · l2) l1
end List

namespace Term

  @[simp]
  def vars_inner (c : Nat) : Term -> List Nat
  | var x => if c.ble x then [x - c] else []
  | kind => []
  | type => []
  | ctor1 _ t => vars_inner c t
  | ctor2 _ t1 t2 => vars_inner c t1 ++ vars_inner c t2
  | bind2 _ t1 t2 => vars_inner c t1 ++ vars_inner (c + 1) t2
  | ite t1 t2 t3 t4 => vars_inner c t1 ++ vars_inner c t2 ++ vars_inner c t3 ++ vars_inner c t4
  | guard t1 t2 t3 => vars_inner c t1 ++ vars_inner c t2 ++ vars_inner c t3
  | letterm t1 t2 t3 => vars_inner c t1 ++ vars_inner c t2 ++ vars_inner (c + 1) t3

  def vars (t : Term) : List Nat := vars_inner 0 t

  -- theorem zero_not_var_inner (r : Ren) (σ : Subst Term) :
  --   (∀ x, c ≤ x -> (x - c) ∉ Term.vars_inner c t) ->
  --   (∀ n, n ≥ c -> σ n = r.to n) ->
  --   [σ]t = [r.to]t
  -- := by sorry

  -- theorem zero_not_var_implies_beta_noop {t : Term} a :
  --   0 ∉ t.vars -> t β[a] = [P]t
  -- := by
  -- intro h
  -- induction t <;> simp at *
  -- case _ y =>
  --   unfold Term.vars at h
  --   cases y <;> simp at *
  -- case _ ih => apply ih h
  -- case _ ih1 ih2 => sorry
  -- case _ ih1 ih2 =>

  --   sorry
  -- case _ => sorry
  -- case _ => sorry
  -- case _ => sorry

end Term
