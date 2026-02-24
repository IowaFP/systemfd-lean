import Surface.Term
import Core.Term

import Translation.Term
import Surface.Metatheory.Rename
import Core.Metatheory.Rename
open LeanSubst

theorem Translation.Ty.Rename (r : Ren) {Δ Δr : Core.KindEnv} {T : Surface.Ty}{T' : Core.Ty}:
  (∀ i, Δ[i]? = Δr[r i]?) ->
  T.translate G' Δ = some T' ->
  (T[r]).translate G' Δr = some (T'[r]) := by
intro h h1
fun_induction Surface.Ty.translate generalizing T' Δr r <;> simp at *
case _ Δ x =>
  replace h := h x
  simp at h; subst h1;
  -- coercion bs
  sorry
case _ => subst h1; simp
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h1
  rcases h1 with ⟨A', h1, h2⟩
  rw[Option.bind_eq_some_iff] at h2
  rcases h2 with ⟨B', h2, h3⟩
  cases h3
  rw[Option.bind_eq_some_iff]; exists A'[r]
  apply And.intro
  · apply @ih1 r _ _ h h1
  · rw[Option.bind_eq_some_iff]; exists B'[r]
    apply And.intro
    · apply @ih2 r _ _ h h2
    · simp
case _ ih1 ih2 =>
  rw[Option.bind_eq_some_iff] at h1
  rcases h1 with ⟨A', h1, h2⟩
  rw[Option.bind_eq_some_iff] at h2
  rcases h2 with ⟨B', h2, h3⟩
  cases h3
  rw[Option.bind_eq_some_iff];  exists A'[r]
  apply And.intro
  · apply @ih1 r _ _ h h1
  · rw[Option.bind_eq_some_iff]; exists B'[r]
    apply And.intro
    · apply @ih2 r _ _ h h2
    · simp
case _ Δ K P K' ih =>
  rw[Option.bind_eq_some_iff] at h1
  rcases h1 with ⟨P', h1, h2⟩
  cases h2
  replace h := Core.Kinding.rename_lift (Δ := Δ) (Δr := Δr) (K := K') r h
  replace ih := ih (Δr := K'::Δr) (T' := P') (r := r.lift) h h1
  simp at *
  rw[Option.bind_eq_some_iff]
  exists P'[re 0 :: r ∘ +1]


theorem Translation.Ty.Weaken {T : Surface.Ty} {T' : Core.Ty} :
  T.translate G' Δ' = some T' ->
  (T[+1]).translate G' (K' :: Δ') = some (T'[+1]) := by
intro h
apply Translation.Ty.Rename (r := (· + 1)) (Δ := Δ') (Δr := K' :: Δ') _ h
intro i; simp [Core.KindEnv, Core.inst_getElem?_KindEnv]
