-- import Hs.HsTerm.Definition

-- import Mathlib.SetTheory.ZFC.Basic

-- namespace HsTerm
--   @[simp]
--   def fvs : HsTerm -> Set Nat
--   | .HsType => {}
--   | .HsKind => {}
--   | (.HsVar x) => {x}
--   | .HsCtor2 _ t1 t2 => t1.fvs ∪ t2.fvs
--   | .HsBind2 _ t1 t2 => t1.fvs ∪ (t2.fvs \ {0})
--   | .HsLet t1 t2 t3 => t1.fvs ∪ t2.fvs ∪ (t3.fvs \ {0})
--   | .HsIte p s i e => p.fvs ∪ s.fvs ∪ i.fvs ∪ e.fvs
-- end HsTerm

-- theorem ex1 : ¬ x ∈ (`λ `#0).fvs := by
-- intro j
-- unfold HsTerm.fvs at j; simp at j;
