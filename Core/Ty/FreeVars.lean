import LeanSubst
import Core.Ty.Definition
import Core.Ty.BEq
import Core.Ty.Substitution

open LeanSubst

namespace Core

inductive Ty.FV : Ty -> Nat -> Prop where
| var : FV t#x x
| arrowr : FV a x -> FV (a -:> b) x
| arrowl : FV b x -> FV (a -:> b) x
| eqr : FV a x -> FV (a ~[K]~ b) x
| eql : FV b x -> FV (a ~[K]~ b) x
| appr : FV a x -> FV (a • b) x
| appl : FV b x -> FV (a • b) x
| all : FV p (a + 1) -> FV (∀[K] p) a

@[simp]
def Ty.fv : Ty -> Nat -> Bool
| gt#_, _ => false
| t#x, i => x == i
| A -:> B, i => A.fv i || B.fv i
| A ~[_]~ B, i => A.fv i || B.fv i
| .app A B, i => A.fv i || B.fv i
| ∀[_] P, i => P.fv (i + 1)

-- R[ℓ1 ++ σ] = R2[ℓ2 ++ τ] -> ℓ1 = ℓ2

instance instMembership_Nat_Ty : Membership Nat Ty where
  mem := Ty.FV

theorem Ty.FV.reflection {A : Ty} : i ∈ A <-> A.fv i := by
  apply Iff.intro <;> intro h
  case _ => induction h <;> simp [*]
  case _ =>
    fun_induction Ty.fv
    case _ => cases h
    case _ => simp at h; subst h; apply var
    case _ ih1 ih2 =>
      simp at h; cases h
      case _ h => apply arrowr (ih1 h)
      case _ h => apply arrowl (ih2 h)
    case _ ih1 ih2 =>
      simp at h; cases h
      case _ h => apply eqr (ih1 h)
      case _ h => apply eql (ih2 h)
    case _ ih1 ih2 =>
      simp at h; cases h
      case _ h => apply appr (ih1 h)
      case _ h => apply appl (ih2 h)
    case _ ih => apply all (ih h)

@[simp]
def iterate (f : T -> T) : Nat -> T -> T
| 0 => λ x => x
| n + 1 => λ x => f $ (iterate f n) x

notation f "^[" n "]" => iterate f n

@[simp]
theorem iterate_succ {x : Nat} : ((Ren.succ T).act^[n]) x = x + n := by
  induction n <;> simp at *
  case succ n ih => rw [ih]; omega

-- theorem lift_iterated_succ_is_re {y : Nat} :
--   ((Ren.lift^[n]) (Ren.succ Ty)).act y = z ->
--   ∃ i, z = re i
--  := by sorry
--   intro h
--   induction n generalizing y z <;> simp [-Subst.rewrite_lift_k] at *
--   case zero => exists y + 1; symm at h; assumption
--   case succ n ih =>
--     cases y <;> simp [-Subst.rewrite_lift_k] at *
--     case zero => exists 0; symm at h; assumption
--     case succ y =>
--       sorry
      -- simp [-Subst.rewrite_lift_k, Subst.compose] at *
      -- rcases (@ih y) with ⟨k, ih⟩
      -- generalize zdef : (((Subst.lift (T := Ty))^[n]) +1) y = z at *
      -- cases z <;> simp [-Subst.rewrite_lift_k] at *
      -- case _ a =>
      --   exists (a + 1); symm at h
      --   rw [zdef] at h; simp [*]
      -- case _ a =>
      --   rw [ih] at zdef
      --   injection zdef

-- x ∉ T[(x + 1)]
theorem FV.var_not_in_one_more {T : Ty} : (x ∉ T⟨((Ren.lift)^[x]) (Ren.succ Ty)⟩) := by
  intro h
  induction T generalizing x <;> simp [-Subst.rewrite_lift_k] at *
  case var y =>
    induction x generalizing y <;> simp [-Subst.rewrite_lift_k]  at *
    case zero => cases h
    case succ n ih =>
    cases y <;> simp [-Subst.rewrite_lift_k]  at *
    case zero => cases h
    case succ y =>
    replace ih := ih y; simp at ih;
    have h' : n ∈ t#(((((fun r => 0 :: r ∘ Ren.succ Ty)^[n]) (Ren.succ Ty)).act y)) := by
      generalize zdef : (((fun r => 0 :: r ∘ Ren.succ Ty)^[n]) (Ren.succ Ty)).act y = z at *
      unfold Ren.act at zdef;
      sorry
    exfalso; apply ih h'
    -- simp [Subst.compose] at h
    -- replace ih := ih y
    -- generalize zdef : (((Subst.lift (T := Ty))^[n]) +1 y) = z at *
    -- have lem := lift_iterated_succ_is_re zdef
    -- rcases lem with ⟨k , lem⟩
    -- subst z; simp [-Subst.rewrite_lift_k] at lem; rw [lem] at h; simp at h
    -- cases h; apply ih; rw[lem]; simp; apply Ty.FV.var
  case all P ih =>
    cases h; case _ h =>
    apply @ih (x + 1); simp; apply h
  case global => cases h
  all_goals (
  case _ ih1 ih2 =>
    replace ih1 := @ih1 x
    replace ih2 := @ih2 x
    cases h <;> simp at *
    case _ h => apply ih1 h
    case _ h => apply ih2 h)

theorem FV.zero_not_in_succ {T : Ty} : 0 ∉ T⟨.succ Ty⟩ := by
  have lem := @FV.var_not_in_one_more (T := T) 0
  simp at lem; apply lem

theorem Ren.lift_act_gt (h : k > i) {r : Ren T} : (r.lift k).act i = i := by
  induction k generalizing i; cases h
  case _ k ih =>
  cases i; simp; case _ i =>
  replace ih := @ih i (by omega)
  rw [Ren.lift_of_succ]
  simp [-Subst.rewrite_lift_k_ren]
  apply ih

theorem Subst.lift_act_gt
  [RenMap T T] [RenMapId T T] [RenMapCompose T T]
  (h : k > i) {σ : Subst T}
  : (σ.lift k).act i = re i
:= by
  induction k generalizing i; cases h
  case _ k ih =>
  cases i; simp; case _ i =>
  replace ih := @ih i (by omega)
  rw [Subst.rewrite_lift_succ]
  simp [-Subst.rewrite_lift_k_ren]
  rw [ih]; simp

theorem FV.rmap_lift {T : Ty} {r : Ren Ty} (h : k > i) :
  i ∈ T -> i ∈ T⟨r.lift k⟩
| .var => by simp [-Subst.rewrite_lift_k_ren]; rw [Ren.lift_act_gt h]; apply Ty.FV.var
| .arrowr j => .arrowr (rmap_lift h j)
| .arrowl j => .arrowl (rmap_lift h j)
| .eqr j => .eqr (rmap_lift h j)
| .eql j => .eql (rmap_lift h j)
| .appr j => .appr (rmap_lift h j)
| .appl j => .appl (rmap_lift h j)
| .all j =>
  have j' := rmap_lift (k := k + 1) (r := r) (by omega) j
  .all (by simp [Ty.rmap_promote]; simp at j'; exact j')

theorem FV.smap_lift {T : Ty} {σ : Subst Ty} (h : k > i) :
  i ∈ T -> i ∈ T[σ.lift k]
| .var => by simp [-Subst.rewrite_lift_k]; rw [Subst.lift_act_gt h]; apply Ty.FV.var
| .arrowr j => .arrowr (smap_lift h j)
| .arrowl j => .arrowl (smap_lift h j)
| .eqr j => .eqr (smap_lift h j)
| .eql j => .eql (smap_lift h j)
| .appr j => .appr (smap_lift h j)
| .appl j => .appl (smap_lift h j)
| .all j =>
  have j' := smap_lift (k := k + 1) (σ := σ) (by omega) j
  .all (by simp [Ty.smap_promote]; simp at j'; exact j')

theorem FV.mem_add {T : Ty} : x ∈ T⟨.add Ty k⟩ -> x ≥ k := by
  intro h
  generalize Zdef : T⟨Ren.add Ty k⟩ = Z at *
  induction h generalizing T k

  case var =>
    cases T <;> simp at Zdef
    subst Zdef; simp
  all_goals try (case _ ih =>
    cases T <;> simp at Zdef
    apply ih Zdef.1)
  all_goals try (case _ ih =>
    cases T <;> simp at Zdef
    apply ih Zdef.2)
  case eqr ih =>
    cases T <;> simp at Zdef
    apply ih Zdef.2.1
  case eql ih =>
    cases T <;> simp at Zdef
    apply ih Zdef.2.2
  case all A n K j ih =>
    cases T <;> simp at Zdef
    case _ K' B =>
    rcases Zdef with ⟨e1, e2⟩; subst e1 e2

    sorry


theorem FV.subst_congr_var {ℓ1 ℓ2 : List Ty} (σ τ : Subst Ty)
  (h1 : i < ℓ1.length)
  (h2 : ℓ1.length = ℓ2.length)
  : Ty.from_action ((ℓ1.map su ++ σ).act i) = ((ℓ2.map su ++ τ).act i) -> ℓ1[i] = ℓ2[i]
:= by
  intro h
  induction ℓ1 generalizing i ℓ2
  case _ => simp at h1
  case _ hd1 tl1 ih =>
    cases ℓ2; simp at h2
    case _ hd2 tl2 =>
      cases i
      case _ => simp; simp at h; apply h
      case _ i =>
        simp at h; simp
        simp at ih; apply ih _ _ h
        simp at h2; apply h2

theorem FV.subst_congr_append_get {T : Ty} {ℓ1 ℓ2 : List Ty} {σ τ : Subst Ty}
  (h1 : i < ℓ1.length)
  (h2 : ℓ1.length = ℓ2.length)
  (h3 : i ∈ T)
  : T[ℓ1.map su ++ σ] = T[ℓ2.map su ++ τ] -> ℓ1[i] = ℓ2[i]
:= by
  intro h; induction T generalizing i ℓ1 ℓ2 σ τ
  case var i =>
    cases h3; simp at h
    apply subst_congr_var σ τ h1 h2 h
  case global => cases h3
  all_goals try (case _ A B ih1 ih2 =>
    simp at h; cases h3
    case _ h3 => apply ih1 h1 h2 h3 h.1
    case _ h3 => apply ih2 h1 h2 h3 h.2)
  case all K T ih =>
    simp at h; cases h3; case _ h3 =>
    replace ih := @ih (i + 1) (t#0 :: ℓ1⟨.succ Ty⟩) (t#0 :: ℓ2⟨.succ Ty⟩)
      (σ ∘ Ren.succ Ty) (τ ∘ Ren.succ Ty)
      (by simp [h1]) (by simp [h2]) h3
    simp at ih;


    -- simp at ih; replace ih := ih h
    -- simp at lem
    sorry


theorem FV.subst_congr_append {T : Ty} {ℓ1 ℓ2 : List Ty} {σ τ : Subst Ty}
  (h1 : ∀ i, i < ℓ2.length -> i ∈ T)
  (h2 : ℓ1.length = ℓ2.length)
  : T[ℓ1.map su ++ σ] = T[ℓ2.map su ++ τ] -> ℓ1 = ℓ2
:= by
  intro h3
  apply List.ext_get h2
  intro i q1 q2; simp
  have lem := h1 i q2
  apply subst_congr_append_get q1 h2 lem h3

theorem FV.subst_congr_append_lift_get_lemma {T : Ty} {ℓ : List Ty} {σ τ : Subst Ty}
  : T[ℓ.map su ++ σ] = T[0..ℓ.length ++ τ] -> T[σ.lift ℓ.length] = T[τ.lift ℓ.length]
:= by
  sorry

theorem FV.subst_congr_append_append_get {T : Ty} {ℓ1 ℓ2 ℓ3 : List Ty} {σ τ : Subst Ty}
  (h1 : i < ℓ2.length)
  (h2 : ℓ1.length = ℓ2.length)
  (h3 : ℓ3.length = k)
  (h4 : i + ℓ3.length ∈ T)
  : T[ℓ3.map su ++ (ℓ1.map su ++ σ)] = T[0..k ++ (ℓ2.map su ++ τ)] -> ℓ1[i] = ℓ2[i]
:= by
  intro h
  induction T generalizing i ℓ1 ℓ2 ℓ3 σ τ
  case var =>
    cases h4; simp at h; subst h3

    sorry
  case global => cases h4
  case arrow ih1 ih2 =>
    simp at h; cases h4
    case _ h4 => apply ih1 h1 h2 h3 h4 h.1
    case _ h4 => apply ih2 h1 h2 h3 h4 h.2
  case all ih =>
    simp at h; cases h4; case _ h4 =>

    sorry
  case app ih1 ih2 =>
    simp at h; cases h4
    case _ h4 => apply ih1 h1 h2 h3 h4 h.1
    case _ h4 => apply ih2 h1 h2 h3 h4 h.2
  case eq ih1 ih2 =>
    simp at h; cases h4
    case _ h4 => apply ih1 h1 h2 h3 h4 h.1
    case _ h4 => apply ih2 h1 h2 h3 h4 h.2

theorem FV.subst_congr_append_append {T : Ty} {ℓ1 ℓ2 ℓ3 : List Ty} {σ τ : Subst Ty}
  (h1 : ∀ i, i < ℓ2.length -> i + ℓ3.length ∈ T)
  (h2 : ℓ1.length = ℓ2.length)
  (h3 : ℓ3.length = k)
  : T[ℓ3.map su ++ (ℓ1.map su ++ σ)] = T[0..k ++ (ℓ2.map su ++ τ)] -> ℓ1 = ℓ2
:= by
  intro h
  sorry
-- R[(List.map su As2⟨Ren.add Ty nb⟩.list).reverse ++ (List.map su As1⟨Ren.add Ty nb⟩.list).reverse ++ Subst.add Ty nb] =
--   R[0..nb ++ ((List.map su As⟨Ren.add Ty nb⟩.list).reverse ++ Subst.add Ty nb)]

end Core
