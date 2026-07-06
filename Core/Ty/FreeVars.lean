import LeanSubst
import Core.Ty.Definition
import Core.Ty.BEq
import Core.Ty.Substitution

open LeanSubst

namespace Core

-- should be in LeanSubst
@[simp, grind <-]
theorem Subst.hAppend_subst_action_ge {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ σ).act i = σ.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => Subst.hAppend_subst_action_ge (σ := σ) (i := i) (ℓ := tl) (by grind) |> cast (by simp)

@[simp, grind <-]
theorem Subst.hAppend_ren_action_ge {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i ≥ ℓ.length) -> (ℓ ++ r).act i = r.act (i - ℓ.length)
| .nil, h => by simp
| .cons hd tl, h =>
  match i with
  | 0 => by simp at h
  | i + 1 => Subst.hAppend_ren_action_ge (r := r) (i := i) (ℓ := tl) (by grind) |> cast (by simp)

@[simp, grind <-]
theorem Subst.hAppend_subst_action_lt {σ : Subst T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ σ).act i = re ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => Subst.hAppend_subst_action_lt (σ := σ) (ℓ := tl) (by grind)

@[simp, grind <-]
theorem Subst.hAppend_ren_action_lt {r : Ren T} {i}
  : {ℓ : List Nat} -> (h : i < ℓ.length) -> (ℓ ++ r).act i = ℓ[i]
| .cons hd tl, h =>
  match i with
  | 0 => rfl
  | i + 1 => Subst.hAppend_ren_action_lt (r := r) (ℓ := tl) (by grind)

theorem Subst.range_length_aux {s e : Nat} (h : s ≤ e) : (s..e).length = e - s
  := by
  fun_induction Ren.range <;> grind

theorem Subst.range_length : (0..k).length = k := by
  have lem := Subst.range_length_aux (s := 0) (e := k) (by grind)
  simp at lem; apply lem




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
    generalize zdef : (((fun r => 0 :: r ∘ Ren.succ Ty)^[n]) (Ren.succ Ty)).act y = z at *
    replace ih := ih y; simp at ih;
    cases h
    rw[zdef] at ih;
    apply ih (Ty.FV.var)
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


theorem FV.mem_add_k {T : Ty} : (x + n) ∈ T⟨(Ren.add Ty k).lift n⟩ -> (x + n) ≥ k := by
  intro h

  generalize Zdef : T⟨(Ren.add Ty k).lift n⟩ = Z at *
  generalize xndef : x + n = xn at *
  induction h generalizing T k n x
  case var =>
    cases T <;> simp [-Subst.rewrite_lift_k_ren] at Zdef
    subst Zdef; simp [-Subst.rewrite_lift_k_ren]
    case _ a =>
    cases Nat.decLt a n
    case _ h =>
      rw[Ren.lift_action_ge (by grind)] at *;
      simp at *; omega
    case _ h =>
      rw[Ren.lift_action_lt h] at *; omega
  case all ih =>
     cases T <;> simp [-Subst.rewrite_lift_k_ren, -Subst.rewrite_lift_ren] at Zdef
     rcases Zdef with ⟨e, Zdef⟩; subst e; subst xndef
     rw[<-Ren.lift_of_succ] at Zdef;
     case _ a =>
     replace ih := @ih (k + 1) (n + 1) x

     sorry
  repeat sorry
  -- case var =>
  --   cases T <;> simp at Zdef
  --   subst Zdef; simp
  -- all_goals try (case _ ih =>
  --   cases T <;> simp at Zdef
  --   apply ih Zdef.1)
  -- all_goals try (case _ ih =>
  --   cases T <;> simp at Zdef
  --   apply ih Zdef.2)
  -- case eqr ih =>
  --   cases T <;> simp at Zdef
  --   apply ih Zdef.2.1
  -- case eql ih =>
  --   cases T <;> simp at Zdef
  --   apply ih Zdef.2.2
  -- case all A n K j ih =>
  --   -- have lem := @FV.var_not_in_one_more (T := T) x;

  --   cases T <;> simp [-Subst.rewrite_lift] at Zdef
  --   case _ K' B =>
  --   rcases Zdef with ⟨e1, e2⟩; subst e1 e2
  --   replace ih := @ih (k + 1)


theorem FV.mem_add {T : Ty} : x ∈ T⟨Ren.add Ty k⟩ -> x ≥ k
  := by
  intro h
  let lem := FV.mem_add_k (n := 0) h; simp at lem; apply lem



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


theorem Ty.add_inj {T1 T2 : Ty} (h : r = Ren.add Ty k) : T1⟨r⟩ = T2⟨r⟩ -> T1 = T2
  := by
  intro h1
  have lem : ∀ {T : Ty}, T⟨Ren.sub Ty k⟩ = T⟨Ren.sub Ty k⟩ := by intro T; rfl
  have lemT1 := @lem T1⟨r⟩
  have lemT2 := @lem T2⟨r⟩
  conv at lemT2 =>
    rhs
    rw[<-h1]
  rw[lemT1] at lemT2;
  simp at lemT2; rw[h] at lemT2; simp at lemT2; symm at lemT2
  apply lemT2

theorem Ty.succ_inj {T1 T2 : Ty} : T1⟨Ren.succ Ty⟩ = T2⟨Ren.succ Ty⟩ -> T1 = T2
  := by
  intro h
  have lem := Ty.add_inj (k := 1) (T1 := T1) (T2 := T2) rfl
  rw[Ren.add_one] at lem; apply lem h


theorem Ty.ren_act_eq {T: Ty} {r1 r2 : Ren Ty} : T⟨r1⟩ = T⟨r2⟩ -> ∀ i, i ∈ T -> r1.act i = r2.act i
  := by
  intro h1 i h2
  induction T generalizing i r1 r2 <;> simp at *
  all_goals (cases h2)
  case var.var => apply h1
  case all.all ih h =>
    replace ih := ih h1 (i + 1) h; simp at ih
    apply ih
  all_goals try (case _ ih1 ih2 h =>
    rcases h1 with ⟨h1, h2⟩
    apply ih1 h1 i h)
  all_goals try (case _ ih1 ih2 h =>
    rcases h1 with ⟨h1, h2⟩
    apply ih2 h2 i h)

theorem Ty.sub_act_eq {T: Ty} {σ1 σ2 : Subst Ty} :
  T[σ1] = T[σ2] -> ∀ i, i ∈ T -> from_action (σ1.act i) = from_action (σ2.act i)
  := by
  intro h1 i h2
  induction h2 generalizing σ1 σ2
  case var =>
    simp at h1; apply h1
  case all i _ _ ih =>
    simp at h1; replace ih := ih h1; simp at ih
    generalize s1def : σ1.act i = s1 at *
    generalize s2def : σ2.act i = s2 at *
    cases s1 <;> cases s2
    case re.re =>
      simp at ih; subst ih; rfl
    case re.su a =>
      simp at ih
      cases a <;> simp at ih
      subst ih; rfl
    case su.re a _ =>
      simp at ih
      cases a <;> simp at ih
      subst ih; rfl
    case su.su =>
      simp at ih; simp
      apply Ty.succ_inj ih
  all_goals try (case _ ih =>
    simp at h1
    apply ih h1.1)
  all_goals try (case _ ih =>
    simp at h1
    apply ih h1.2)


theorem FV.subst_congr_append_get {T : Ty} {ℓ1 ℓ2 : List Ty} {σ τ : Subst Ty}
  (h1 : i < ℓ1.length)
  (h2 : ℓ1.length = ℓ2.length)
  (h3 : i ∈ T)
  : T[ℓ1.map su ++ σ] = T[ℓ2.map su ++ τ] -> ℓ1[i] = ℓ2[i]
:= by

  intro h;
  have lem := Ty.sub_act_eq h _ h3;
  rw[Subst.append_action_lt (by grind)] at lem;
  rw[Subst.append_action_lt (by grind)] at lem;
  rw[List.getElem_map] at lem; rw[List.getElem_map] at lem
  simp at lem; apply lem


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


theorem FV.subst_congr_append_append_get {T : Ty} {ℓ1 ℓ2 ℓ3 : List Ty} {σ τ : Subst Ty} {i : Nat}
  (h1 : i < ℓ2.length)
  (h2 : ℓ1.length = ℓ2.length)
  (h3 : ℓ3.length = k)
  (h4 : i + ℓ3.length ∈ T)
  : T[ℓ3.map su ++ (ℓ1.map su ++ σ)] = T[0..k ++ (ℓ2.map su ++ τ)] -> ℓ1[i] = ℓ2[i]
:= by
  intro h
  have lem := Ty.sub_act_eq h (i + ℓ3.length) h4
  simp at lem;
  rw[Subst.append_action_lt (by grind)] at lem;
  rw[List.getElem_map] at lem
  simp [h3] at lem; rw[Nat.add_comm] at lem;
  rw[Subst.hAppend_subst_action_ge (ℓ := 0..k) (σ := List.map su ℓ2 ++ τ) (i := k + i) (h := by rw[Subst.range_length (k := k)]; omega)] at lem
  rw[Subst.range_length] at lem; simp at lem;
  rw[Subst.append_action_lt (by grind)] at lem; simp at lem;
  apply lem


theorem FV.subst_congr_append_append {T : Ty} {ℓ1 ℓ2 ℓ3 : List Ty} {σ τ : Subst Ty}
  (h1 : ∀ i, i < ℓ2.length -> i + ℓ3.length ∈ T)
  (h2 : ℓ1.length = ℓ2.length)
  (h3 : ℓ3.length = k)
  : T[ℓ3.map su ++ (ℓ1.map su ++ σ)] = T[0..k ++ (ℓ2.map su ++ τ)] -> ℓ1 = ℓ2
:= by
  intro h
  rw[List.ext_getElem_iff]
  apply And.intro h2
  intro i h4 h5;
  replace h1 := h1 i h5
  apply FV.subst_congr_append_append_get h5 h2 h3 h1 h

end Core
