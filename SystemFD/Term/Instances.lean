import SystemFD.Substitution
import SystemFD.Ctx
import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Util

@[simp]
def instance_indices : Ctx Term -> Nat -> Nat -> List Nat -> List Nat
| .nil , _,  _ , acc => acc
| .cons (.inst (#x) _) Γ, n, opm , acc =>
        (if opm == x + n + 1
        then instance_indices Γ (n+1) opm (n::acc)
        else instance_indices Γ (n+1) opm acc)
| .cons _ Γ, n, opm , acc => instance_indices Γ (n + 1) opm acc

theorem instance_indices_leq_implies_empty :
  y ≤ x ->
  instance_indices Γ x y ℓ = ℓ
:= by
intro h
induction Γ, x, y, ℓ using instance_indices.induct
case _ => simp
case _ h2 ih =>
  simp; split
  case _ => exfalso; omega
  case _ h3 =>
    replace h2 := LawfulBEq.eq_of_beq h2
    exfalso; omega
case _ ih =>
  simp; split
  case _ => exfalso; omega
  case _ => apply ih; omega
case _ ih => simp; apply ih; omega

theorem instance_indices_acc_append (Γ : Ctx Term) x y ℓ1 ℓ2 :
  instance_indices Γ x y (ℓ1 ++ ℓ2) = instance_indices Γ x y ℓ1 ++ ℓ2
:= by
induction Γ, x, y, ℓ1 using instance_indices.induct generalizing ℓ2
case _ => simp
case _ h ih =>
  simp at *; split
  case _ => rw [ih]
  case _ => exfalso; omega
case _ ih =>
  simp at *; split
  case _ => exfalso; omega
  case _ => rw [ih]
case _ h ih => simp at *; rw [ih]

theorem instance_indices_shift :
  instance_indices Γ (x + k) (y + k) ℓ
    = List.map (· + k) (instance_indices Γ x y []) ++ ℓ
:= by
generalize udef : x + k = u at *
generalize vdef : y + k = v at *
induction Γ, u, v, ℓ using instance_indices.induct generalizing x y k
case _ => simp
case _ z _ Γ n opm acc h ih =>
  subst udef; subst vdef
  simp at *; split
  case _ =>
    split
    case _ acc e1 e2 =>
      replace ih := @ih (x + 1) k y (by omega) (by omega)
      have lem := instance_indices_acc_append Γ (x + 1) y [] [x]
      simp at lem; rw [lem]; simp; rw [ih]
    case _ => exfalso; omega
  case _ => exfalso; omega
case _ h ih =>
  subst udef; subst vdef
  simp at *; split
  case _ => exfalso; omega
  case _ z _ _ _ =>
    cases y <;> simp at *
    case _ =>
      rw [instance_indices_leq_implies_empty]
      rw [instance_indices_leq_implies_empty]
      simp; omega; omega
    case _ y _ =>
      have ih := @ih (x + 1) k (y + 1) (by omega) (by omega)
      split
      case _ h => exfalso; omega
      case _ => rw [<-ih]
case _ h ih =>
  subst udef; subst vdef
  simp at *
  replace ih := @ih (x + 1) k y (by omega) (by simp)
  rw [ih]

@[simp]
def get_instances : Ctx Term -> List Nat -> List Term
| _, [] => []
| Γ, .cons i t =>
  match Γ d@ i with
  | .inst _ b => b :: get_instances Γ t
  | _ => get_instances Γ t

theorem instance_indices_sound : i ∈ instance_indices Γ k x [] -> ∃ t, (Γ d@ i) = .inst #x t := by
intro j
generalize ℓdef : [] = ℓ at *
induction Γ, k, x, ℓ using instance_indices.induct generalizing i
case _ => sorry
case _ => sorry
case _ => sorry
case _ hd Γ n opm acc h ih =>
  subst ℓdef; cases i <;> simp at *
  case _ => sorry
  case _ => sorry

theorem get_instances_sound :
  ix = instance_indices Γ k x [] ->
  t ∈ get_instances Γ ix ->
  ∃ i, Γ d@ i = .inst #x t
:= by
intro h1 h2
induction Γ, ix using get_instances.induct generalizing x k t
case _ => simp at *
case _ Γ i ℓ a b h ih =>
  simp at *; split at h2
  case _ f u v e1 =>
    simp at h2; cases h2
    case _ h2 =>
      subst h2; have lem : i ∈ instance_indices Γ k x [] := by sorry
      replace lem := instance_indices_sound lem
      cases lem; case _ t' lem =>
        rw [e1] at lem; injection lem with e2 e3
        subst e2; subst e3; exists i
    case _ h2 =>
      have lem : ∃ k', ℓ = instance_indices Γ k' x [] := by sorry
      cases lem; case _ k' lem =>
        replace ih := ih lem h2
        apply ih
  case _ =>
    have lem : ∃ k', ℓ = instance_indices Γ k' x [] := by sorry
    cases lem; case _ k' lem =>
      replace ih := ih lem h2
      apply ih
case _ Γ i ℓ h ih =>
  simp at *
  have lem : ∃ k', ℓ = instance_indices Γ k' x [] := by sorry
  cases lem; case _ k' lem =>
    replace ih := ih lem h2
    apply ih

-- theorem get_instances_strengthen (f : Frame Term) :
--   (∀ i n, .some n = ix.get? i -> n > 0) ->
--   get_instances (f :: Γ) ix
--     = List.map ([S]·) (get_instances Γ (List.map (· - 1) ix))
-- := by
-- intro h; induction ix generalizing f Γ
-- case _ => simp
-- case _ hd tl ih =>
--   cases hd <;> simp at *
--   case _ =>
--     replace h := h 0 0 (by simp)
--     exfalso; omega
--   case _ x =>
--     generalize zdef : Γ d@ x = z at *
--     cases z
--     case inst => sorry
--     all_goals (
--       unfold Frame.apply; simp at *
--       rw [ih]
--       intro i n h'
--       replace h := h (i + 1) n; simp at h
--       apply h h'
--     )

-- theorem get_instances_succ {f : Frame Term} :
--   get_instances (f :: Γ) (instance_indices Γ (y + 1) (x + 1) [])
--     = List.map ([S]·) (get_instances Γ (instance_indices Γ y x []))
-- := by
-- rw [instance_indices_shift]
-- rw [get_instances_strengthen]; simp
-- unfold Function.comp; simp
-- intro i n h; simp at h
-- generalize zdef : (instance_indices Γ y x [])[i]? = z at *
-- cases z <;> simp at *; omega
