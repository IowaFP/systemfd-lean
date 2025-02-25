import SystemFD.Substitution
import SystemFD.Ctx
import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Util

@[simp]
def get_instances : Ctx Term -> Nat -> List Term
| .nil, _ => []
| .cons _ _, 0 => []
| .cons (.inst #y t) Γ, (opm + 1) =>
  if y == opm then ([S]t) :: (List.map ([S]·) (get_instances Γ opm))
  else List.map ([S]·) (get_instances Γ opm)
| .cons _ Γ, (opm + 1) => List.map ([S]·) (get_instances Γ opm)

theorem get_instances_sound :
  t ∈ get_instances Γ x ->
  ∃ i, Γ d@ i = .inst #x t
:= by
intro j
induction Γ, x using get_instances.induct generalizing t
case _ => simp at *
case _ => simp at *
case _ y t' Γ opm h ih =>
  simp at *; subst h; simp at *
  cases j
  case _ j =>
    subst j; apply Exists.intro 0
    simp; unfold Frame.apply; simp
  case _ j =>
    cases j; case _ a j =>
    cases j; case _ h1 h2 =>
      subst h2
      replace ih := ih h1
      cases ih; case _ i ih =>
        apply Exists.intro (i + 1)
        simp; rw [ih]
        unfold Frame.apply; simp
case _ y t' Γ opm h ih =>
  simp at *; split at j
  case _ h2 => exfalso; apply h h2
  case _ h2 =>
    simp at *
    cases j; case _ a j =>
    cases j; case _ h1 h2 =>
      subst h2
      replace ih := ih h1
      cases ih; case _ i ih =>
        apply Exists.intro (i + 1)
        simp; rw [ih]
        unfold Frame.apply; simp
case _ hd Γ opm h ih =>
  cases hd <;> simp at *
  case inst z _ =>
    cases z <;> simp at *
    all_goals (
      cases j; case _ a j =>
      cases j; case _ h1 h2 =>
        subst h2
        replace ih := ih h1
        cases ih; case _ i ih =>
          apply Exists.intro (i + 1)
          simp; rw [ih]
          unfold Frame.apply; simp
    )
  all_goals (
    cases j; case _ a j =>
    cases j; case _ h1 h2 =>
      subst h2
      replace ih := ih h1
      cases ih; case _ i ih =>
        apply Exists.intro (i + 1)
        simp; rw [ih]
        unfold Frame.apply; simp
  )

-- @[simp]
-- def instance_indices2 : Ctx Term -> Nat -> List Nat
-- | .nil, _ => []
-- | .cons (.inst #y _) Γ, opm =>
--   match (Γ d@ y) with
--   | .inst #z _ => sorry
--   | _ => instance_indices2 Γ opm
-- | .cons _ Γ, opm => instance_indices2 Γ opm

-- @[simp]
-- def instance_indices : Ctx Term -> Nat -> Nat -> List Nat -> List Nat
-- | .nil , _,  _ , acc => acc
-- | .cons (.inst (#x) _) Γ, n, opm , acc =>
--         (if opm == x + n + 1
--         then instance_indices Γ (n+1) opm (n::acc)
--         else instance_indices Γ (n+1) opm acc)
-- | .cons _ Γ, n, opm , acc => instance_indices Γ (n + 1) opm acc

-- -- opm = x + n + 1
-- -- x = opm - n - 1

-- theorem instance_indices_leq_implies_empty :
--   y ≤ x ->
--   instance_indices Γ x y ℓ = ℓ
-- := by
-- intro h
-- induction Γ, x, y, ℓ using instance_indices.induct
-- case _ => simp
-- case _ h2 ih =>
--   simp; split
--   case _ => exfalso; omega
--   case _ h3 =>
--     replace h2 := LawfulBEq.eq_of_beq h2
--     exfalso; omega
-- case _ ih =>
--   simp; split
--   case _ => exfalso; omega
--   case _ => apply ih; omega
-- case _ ih => simp; apply ih; omega

-- theorem instance_indices_acc_append (Γ : Ctx Term) x y ℓ1 ℓ2 :
--   instance_indices Γ x y (ℓ1 ++ ℓ2) = instance_indices Γ x y ℓ1 ++ ℓ2
-- := by
-- induction Γ, x, y, ℓ1 using instance_indices.induct generalizing ℓ2
-- case _ => simp
-- case _ h ih =>
--   simp at *; split
--   case _ => rw [ih]
--   case _ => exfalso; omega
-- case _ ih =>
--   simp at *; split
--   case _ => exfalso; omega
--   case _ => rw [ih]
-- case _ h ih => simp at *; rw [ih]

-- theorem instance_indices_shift :
--   instance_indices Γ (x + k) (y + k) ℓ
--     = List.map (· + k) (instance_indices Γ x y []) ++ ℓ
-- := by
-- generalize udef : x + k = u at *
-- generalize vdef : y + k = v at *
-- induction Γ, u, v, ℓ using instance_indices.induct generalizing x y k
-- case _ => simp
-- case _ z _ Γ n opm acc h ih =>
--   subst udef; subst vdef
--   simp at *; split
--   case _ =>
--     split
--     case _ acc e1 e2 =>
--       replace ih := @ih (x + 1) k y (by omega) (by omega)
--       have lem := instance_indices_acc_append Γ (x + 1) y [] [x]
--       simp at lem; rw [lem]; simp; rw [ih]
--     case _ => exfalso; omega
--   case _ => exfalso; omega
-- case _ h ih =>
--   subst udef; subst vdef
--   simp at *; split
--   case _ => exfalso; omega
--   case _ z _ _ _ =>
--     cases y <;> simp at *
--     case _ =>
--       rw [instance_indices_leq_implies_empty]
--       rw [instance_indices_leq_implies_empty]
--       simp; omega; omega
--     case _ y _ =>
--       have ih := @ih (x + 1) k (y + 1) (by omega) (by omega)
--       split
--       case _ h => exfalso; omega
--       case _ => rw [<-ih]
-- case _ h ih =>
--   subst udef; subst vdef
--   simp at *
--   replace ih := @ih (x + 1) k y (by omega) (by simp)
--   rw [ih]

-- -- theorem instance_indices_cons_miss :
-- --   (hd.is_inst = false) ∨ (∃ z t, hd = .inst #z t ∧ z ≠ (y - x)) ->
-- --   instance_indices (hd :: Γ) x (y + 1) ℓ
-- --     = instance_indices Γ (x + 1) (y + 1) ℓ
-- -- := by

-- -- theorem instance_indices_cons_inst :
-- --   instance_indices ((.inst #(y - x) t) :: Γ) x (y + 1) ℓ
-- --     = (instance_indices Γ (x + 1) (y + 1) []) ++ (x :: ℓ)
-- -- := by
-- -- generalize zdef : y + 1 = z at *
-- -- generalize Δdef : (.inst #(y - x) t) :: Γ = Δ at *
-- -- induction Δ, x, z, ℓ using instance_indices.induct generalizing t Γ y
-- -- case _ => simp at Δdef
-- -- case _ x a Γ' n opm acc h ih =>
-- --   injection Δdef with e1 e2; subst e2
-- --   injection e1 with e1 e2; subst e2
-- --   injection e1 with e1; subst e1
-- --   subst zdef <;> simp at *
-- --   sorry
-- -- case _ x a Γ' n opm acc h ih =>
-- --   injection Δdef with e1 e2; subst e2
-- --   injection e1 with e1 e2; subst e2
-- --   injection e1 with e1; subst e1
-- --   subst zdef <;> simp at *
-- --   split
-- --   case _ h2 => exfalso; apply h h2
-- --   case _ h2 =>
-- --     rw [<-instance_indices_shift]
-- -- case _ hd Γ n opm acc h ih =>
-- --   injection Δdef with e1 e2; subst e2; subst e1
-- --   subst zdef <;> simp at *
-- --   rw [<-instance_indices_shift]

-- theorem instance_indices_sound2 : i ∈ instance_indices Γ k x r -> i ∈ r ∨ ∃ t, (Γ d@ i) = .inst #x t := by
-- intro j
-- induction Γ generalizing i k x r <;> simp at *
-- case _ => apply j
-- case _ hd tl ih =>
--   cases x
--   case _ =>
--     rw [instance_indices_leq_implies_empty] at j
--     apply Or.inl; apply j; simp
--   case _ x =>
--     cases hd
--     case inst opm t =>
--       cases opm
--       case var opm =>
--         simp at j
--         cases Nat.decEq x (opm + k)
--         case _ h =>
--           split at j
--           case _ h2 => exfalso; apply h h2
--           case _ =>
--             rw [instance_indices_shift] at j
--             simp at j
--             cases j
--             case _ j =>
--               cases j; case _ a j =>
--               cases j; case _ h1 h2 =>
--                 subst h2; simp
--                 replace ih := ih h1
--                 cases ih
--                 case _ ih => cases ih
--                 case _ ih =>
--                   cases ih; case _ t ih =>
--                     apply Or.inr
--                     apply Exists.intro ([S]t)
--                     rw [ih]; unfold Frame.apply; simp
--             case _ j => apply Or.inl; apply j
--         case _ h =>
--           subst h; simp at *
--           rw [instance_indices_shift] at j
--           simp at j; cases j
--           case _ h2 =>
--             cases h2; case _ a h2 =>
--             cases h2; case _ h2 h3 =>
--               subst h3; simp at *
--               replace ih := ih h2
--               cases ih
--               case _ ih => cases ih
--               case _ ih =>
--                 cases ih; case _ t ih =>
--                   apply Or.inr
--                   apply Exists.intro ([S]t)
--                   rw [ih]; unfold Frame.apply; simp
--           case _ h2 =>
--             cases h2
--             case _ h2 =>
--               subst h2
--               sorry
--             case _ h2 => apply Or.inl; apply h2
--       all_goals (
--         simp at j; rw [instance_indices_shift] at j
--         simp at j
--         cases j
--         case _ j =>
--           cases j; case _ a j =>
--           cases j; case _ h1 h2 =>
--             subst h2; simp
--             replace ih := ih h1
--             cases ih
--             case _ ih => cases ih
--             case _ ih =>
--               cases ih; case _ t ih =>
--                 apply Or.inr
--                 apply Exists.intro ([S]t)
--                 rw [ih]; unfold Frame.apply; simp
--         case _ j => apply Or.inl; apply j
--       )
--     all_goals (
--       simp at j; rw [instance_indices_shift] at j
--       simp at j
--       cases j
--       case _ j =>
--         cases j; case _ a j =>
--         cases j; case _ h1 h2 =>
--           subst h2; simp
--           replace ih := ih h1
--           cases ih
--           case _ ih => cases ih
--           case _ ih =>
--             cases ih; case _ t ih =>
--               apply Or.inr
--               apply Exists.intro ([S]t)
--               rw [ih]; unfold Frame.apply; simp
--       case _ j => apply Or.inl; apply j
--     )

-- -- theorem instance_indices_sound_lift (r : List Nat) :
-- --   (∀ i, i ∈ r → ∃ t', (.inst (#opm) t :: Γ) d@ i = .inst #(x + 1) t') ->
-- --   (∀ i, i ∈ r -> ∃ t, (Γ d@ i) = .inst #x t)
-- -- := by
-- -- sorry

-- theorem instance_indices_sound :
--   (∀ i, i ∈ r -> ∃ t, (Γ d@ i) = .inst #x t) ->
--   i ∈ instance_indices Γ k x r ->
--   ∃ t, (Γ d@ i) = .inst #x t
-- := by
-- intro j1 j2
-- induction Γ generalizing i k x r <;> simp at *
-- case _ => exfalso; apply j1 i j2
-- case _ hd tl ih =>
--   cases x
--   case _ =>
--     rw [instance_indices_leq_implies_empty] at j2
--     apply j1 _ j2; simp
--   case _ x =>
--     cases hd
--     case inst opm t =>
--       cases opm
--       case var opm =>
--         simp at j2
--         cases Nat.decEq x (opm + k)
--         case _ h =>
--           split at j2
--           case _ h2 => exfalso; apply h h2
--           case _ =>
--             rw [instance_indices_shift] at j2
--             simp at j2
--             cases j2
--             case _ j2 =>
--               cases j2; case _ a j2 =>
--               cases j2; case _ h1 h2 =>
--                 subst h2; simp
--                 replace ih := @ih [] _ _ _ (by simp) h1
--                 cases ih; case _ t ih =>
--                   apply Exists.intro ([S]t)
--                   rw [ih]; unfold Frame.apply; simp
--             case _ j2 => apply j1 i j2
--         case _ h =>
--           subst h; simp at *
--           rw [instance_indices_shift] at j2
--           simp at j2; cases j2
--           case _ h2 =>
--             cases h2; case _ a h2 =>
--             cases h2; case _ h2 h3 =>
--               subst h3; simp
--               replace ih := @ih [] _ _ _ (by simp) h2
--               cases ih; case _ t ih =>
--                 apply Exists.intro ([S]t)
--                 rw [ih]; unfold Frame.apply; simp
--           case _ h2 =>
--             cases h2
--             case _ h2 =>
--               subst h2; cases i <;> simp at *
--               case _ => sorry
--               case _ i =>

--                 sorry
--             case _ h2 => apply j1 _ h2
--       all_goals (
--         simp at j2
--         rw [instance_indices_shift] at j2
--         simp at j2
--         cases j2
--         case _ j2 =>
--           cases j2; case _ a j2 =>
--           cases j2; case _ h1 h2 =>
--             subst h2; simp
--             replace ih := @ih [] _ _ _ (by simp) h1
--             cases ih; case _ t ih =>
--               apply Exists.intro ([S]t)
--               rw [ih]; unfold Frame.apply; simp
--         case _ j2 => apply j1 i j2
--       )
--     all_goals (
--       simp at j2
--       rw [instance_indices_shift] at j2
--       simp at j2
--       cases j2
--       case _ j2 =>
--         cases j2; case _ a j2 =>
--         cases j2; case _ h1 h2 =>
--           subst h2; simp
--           replace ih := @ih [] _ _ _ (by simp) h1
--           cases ih; case _ t ih =>
--             apply Exists.intro ([S]t)
--             rw [ih]; unfold Frame.apply; simp
--       case _ j2 => apply j1 i j2
--     )

-- @[simp]
-- def get_instances : Ctx Term -> List Nat -> List Term
-- | _, [] => []
-- | Γ, .cons i t =>
--   match Γ d@ i with
--   | .inst _ b => b :: get_instances Γ t
--   | _ => get_instances Γ t

-- theorem get_instances_sound :
--   ix = instance_indices Γ k x [] ->
--   t ∈ get_instances Γ ix ->
--   ∃ i, Γ d@ i = .inst #x t
-- := by sorry
-- -- intro h1 h2
-- -- induction Γ, ix using get_instances.induct generalizing x k t
-- -- case _ => simp at *
-- -- case _ Γ i ℓ a b h ih =>
-- --   simp at *; split at h2
-- --   case _ f u v e1 =>
-- --     simp at h2; cases h2
-- --     case _ h2 =>
-- --       subst h2
-- --       have lem : i ∈ instance_indices Γ k x [] := by
-- --         generalize qdef : instance_indices Γ k x [] = q at *
-- --         subst h1; simp
-- --       replace lem := instance_indices_sound lem
-- --       cases lem; case _ t' lem =>
-- --         rw [e1] at lem; injection lem with e2 e3
-- --         subst e2; subst e3; exists i
-- --     case _ h2 =>
-- --       have lem : ∃ k', ℓ = instance_indices Γ k' x [] := sorry
-- --       cases lem; case _ k' lem =>
-- --         replace ih := ih lem h2
-- --         apply ih
-- --   case _ =>
-- --     have lem : ∃ k', ℓ = instance_indices Γ k' x [] := sorry
-- --     cases lem; case _ k' lem =>
-- --       replace ih := ih lem h2
-- --       apply ih
-- -- case _ Γ i ℓ h ih =>
-- --   simp at *
-- --   have lem : ∃ k', ℓ = instance_indices Γ k' x [] := sorry
-- --   cases lem; case _ k' lem =>
-- --     replace ih := ih lem h2
-- --     apply ih

-- -- theorem get_instances_strengthen (f : Frame Term) :
-- --   (∀ i n, .some n = ix.get? i -> n > 0) ->
-- --   get_instances (f :: Γ) ix
-- --     = List.map ([S]·) (get_instances Γ (List.map (· - 1) ix))
-- -- := by
-- -- intro h; induction ix generalizing f Γ
-- -- case _ => simp
-- -- case _ hd tl ih =>
-- --   cases hd <;> simp at *
-- --   case _ =>
-- --     replace h := h 0 0 (by simp)
-- --     exfalso; omega
-- --   case _ x =>
-- --     generalize zdef : Γ d@ x = z at *
-- --     cases z
-- --     case inst => sorry
-- --     all_goals (
-- --       unfold Frame.apply; simp at *
-- --       rw [ih]
-- --       intro i n h'
-- --       replace h := h (i + 1) n; simp at h
-- --       apply h h'
-- --     )

-- -- theorem get_instances_succ {f : Frame Term} :
-- --   get_instances (f :: Γ) (instance_indices Γ (y + 1) (x + 1) [])
-- --     = List.map ([S]·) (get_instances Γ (instance_indices Γ y x []))
-- -- := by
-- -- rw [instance_indices_shift]
-- -- rw [get_instances_strengthen]; simp
-- -- unfold Function.comp; simp
-- -- intro i n h; simp at h
-- -- generalize zdef : (instance_indices Γ y x [])[i]? = z at *
-- -- cases z <;> simp at *; omega
