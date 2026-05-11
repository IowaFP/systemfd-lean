import LeanSubst
import Core.Term.Definition

open LeanSubst
open Lilac

namespace Core

@[coe]
def Term.from_action : Subst.Action Term -> Term
| .re y => #y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0 n) = #n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1 n) = #(n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = #n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Subst.Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren) : Term -> Term
| #x => #(r x)
| d#x => d#x
| spctor v x t1 t2 => spctor v x t1 (rmap r <$> t2)
| ctor0 c => ctor0 c
| ctor1 c t => ctor1 c (rmap r t)
| ctor2 c t1 t2 => ctor2 c (rmap r t1) (rmap r t2)
| tbind v A t => tbind v A (rmap r t)
| lam A t => lam A (rmap r.lift t)
| cast T c t => cast T (rmap r c) (rmap r t)
| mtch m n t1 t2 t3 => mtch m n (rmap r <$> t1) t2 (λ i => rmap (r.lift (t2 i).bind) (t3 i))

instance : RenMap Term where
  rmap := Term.rmap

@[simp]
theorem Term.ren_var : (#x)⟨r⟩ = #(r x) := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_global : (d#x)⟨r⟩ = d#x := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_spctor
  : (spctor v x t1 t2)⟨r⟩ = spctor v x t1 (λ i => (t2 i)⟨r⟩)
:= by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_ctor0 : (ctor0 v)⟨r⟩ = ctor0 v := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_ctor1 : (ctor1 v t)⟨r⟩ = ctor1 v t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_ctor2 : (ctor2 v t1 t2)⟨r⟩ = ctor2 v t1⟨r⟩ t2⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_tbind : (tbind v A t)⟨r⟩ = tbind v A t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_lam : (lam A t)⟨r⟩ = lam A t⟨r.lift⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_cast : (cast T c t)⟨r⟩ = cast T c⟨r⟩ t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_match
  : (mtch m n t1 t2 t3)⟨r⟩
    = mtch m n (λ i => (t1 i)⟨r⟩) t2 (λ i => (t3 i)⟨r.lift (t2 i).bind⟩)
:= by
  simp [RenMap.rmap]

instance : RenMapId Term where
  apply_id := by subst_solve_id

instance : RenMapCompose Term where
  apply_compose := by subst_solve_compose

@[simp]
def Ctor0Variant.rmap (_ : Ren) : Ctor0Variant -> Ctor0Variant
| c => c

instance : RenMap Ctor0Variant where
  rmap := Ctor0Variant.rmap

@[simp]
def Ctor0Variant.smap (_ : Subst Ctor0Variant) : Ctor0Variant -> Ctor0Variant
| c => c

instance : SubstMap Ctor0Variant Ctor0Variant where
  smap := Ctor0Variant.smap

@[simp]
theorem Ctor0Variant.subst_ {c : Ctor0Variant} : c[σ:Ctor0Variant] = c := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor0Variant Ctor0Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor0Variant Ctor0Variant where
  apply_compose := by simp

@[simp]
def Ctor0Variant.Ty.smap (σ : Subst Ty) : Ctor0Variant -> Ctor0Variant
| fail => fail
| refl A => refl A[σ:_]

instance : SubstMap Ctor0Variant Ty where
  smap := Ctor0Variant.Ty.smap

@[simp]
theorem Ctor0Variant.subst_fail : fail[σ:Ty] = fail := by
  simp [SubstMap.smap]

@[simp]
theorem Ctor0Variant.subst_refl : (refl A)[σ:Ty] = refl A[σ:_] := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor0Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor0Variant Ty where
  apply_compose := by intro s σ τ; cases s <;> simp

instance : SubstMapHetCompose Ctor0Variant Ty where
  apply_hcompose := by simp

@[simp]
def Ctor1Variant.rmap (_ : Ren) : Ctor1Variant -> Ctor1Variant
| c => c

instance : RenMap Ctor1Variant where
  rmap := Ctor1Variant.rmap

@[simp]
def Ctor1Variant.smap (_ : Subst Ctor1Variant) : Ctor1Variant -> Ctor1Variant
| c => c

instance : SubstMap Ctor1Variant Ctor1Variant where
  smap := Ctor1Variant.smap

@[simp]
theorem Ctor1Variant.subst_ {c : Ctor1Variant} : c[σ:Ctor1Variant] = c := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor1Variant Ctor1Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor1Variant Ctor1Variant where
  apply_compose := by simp

@[simp]
def Ctor1Variant.Ty.smap (σ : Subst Ty) : Ctor1Variant -> Ctor1Variant
| prj n => prj n
| appt a => appt a[σ:_]

instance : SubstMap Ctor1Variant Ty where
  smap := Ctor1Variant.Ty.smap

@[simp]
theorem Ctor1Variant.subst_fst : (prj n)[σ:Ty] = prj n := by
  simp [SubstMap.smap]

@[simp]
theorem Ctor1Variant.subst_appt : (appt a)[σ:Ty] = appt a[σ:_] := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor1Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor1Variant Ty where
  apply_compose := by intro s σ τ; cases s <;> simp

instance : SubstMapHetCompose Ctor1Variant Ty where
  apply_hcompose := by simp

@[simp]
def Ctor2Variant.rmap (_ : Ren) : Ctor2Variant -> Ctor2Variant
| c => c

instance : RenMap Ctor2Variant where
  rmap := Ctor2Variant.rmap

@[simp]
def Ctor2Variant.smap (_ : Subst Ctor2Variant) : Ctor2Variant -> Ctor2Variant
| c => c

instance : SubstMap Ctor2Variant Ctor2Variant where
  smap := Ctor2Variant.smap

@[simp]
theorem Ctor2Variant.subst_ {c : Ctor2Variant} : c[σ:Ctor2Variant] = c := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor2Variant Ctor2Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor2Variant Ctor2Variant where
  apply_compose := by simp

@[simp]
def Ctor2Variant.Ty.smap (_ : Subst Ty) : Ctor2Variant -> Ctor2Variant
| c => c

instance : SubstMap Ctor2Variant Ty where
  smap := Ctor2Variant.Ty.smap

@[simp]
theorem Ctor2Variant.Ty.subst_ {c : Ctor2Variant} : c[σ:Ty] = c := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor2Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor2Variant Ty where
  apply_compose := by simp

instance : SubstMapHetCompose Ctor2Variant Ty where
  apply_hcompose := by simp

@[simp]
def Term.Ty.smap (σ : Subst Ty) : Term -> Term
| #x => #x
| d#x => d#x
| spctor v x t1 t2 => spctor v x t1[σ:_] (smap σ <$> t2)
| ctor0 c => ctor0 c[σ:Ty]
| ctor1 c t => ctor1 c[σ:Ty] (smap σ t)
| ctor2 c t1 t2 => ctor2 c[σ:Ty] (smap σ t1) (smap σ t2)
| tbind v A t => tbind v A (smap σ.lift t)
| lam A t => lam A[σ:_] (smap σ t)
| cast T c t => cast T[σ.lift:_] (smap σ c) (smap σ t)
| mtch m n t1 t2 t3 => mtch m n (smap σ <$> t1) t2 (smap σ <$> t3)

instance : SubstMap Term Ty where
  smap := Term.Ty.smap

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| #x => σ x
| d#x => d#x
| spctor v x t1 t2 => spctor v x t1 (smap σ <$> t2)
| ctor0 c => ctor0 c
| ctor1 c t => ctor1 c (smap σ t)
| ctor2 c t1 t2 => ctor2 c (smap σ t1) (smap σ t2)
| tbind v A t => tbind v A (smap (σ ◾ +1@Ty) t)
| lam A t => lam A (smap σ.lift t)
| cast T c t => cast T (smap σ c) (smap σ t)
| mtch m n t1 t2 t3 => mtch m n (smap σ <$> t1) t2 (λ i => smap (σ.lift (t2 i).bind) (t3 i))

instance : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem Term.subst_var : (#x)[σ:Term] = σ x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_global : (d#x)[σ:Term] = d#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_spctor
  : (spctor v x t1 t2)[σ:Term] = spctor v x t1 (λ i => (t2 i)[σ:_])
:= by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_ctor0 : (ctor0 v)[σ:Term] = ctor0 v := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_ctor1 : (ctor1 v t)[σ:Term] = ctor1 v t[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_ctor2 : (ctor2 v t1 t2)[σ:Term] = ctor2 v t1[σ:_] t2[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_tbind : (tbind v A t)[σ:Term] = tbind v A t[σ ◾ +1@Ty:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_lam : (lam A t)[σ:Term] = lam A t[σ.lift:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_cast : (cast T c t)[σ:Term] = cast T c[σ:_] t[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_match
  : (mtch m n t1 t2 t3)[σ:Term]
    = mtch m n (λ i => (t1 i)[σ:_]) t2 (λ i => (t3 i)[σ.lift (t2 i).bind:_])
:= by
  simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x} {σ τ : Subst Term}
  : (from_action (σ x))[τ] = from_action ((σ ∘ τ) x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ x = z
  cases z <;> simp [Term.from_action]

@[simp]
theorem Term.Ty.subst_var : (#x)[σ:Ty] = #x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_global : (d#x)[σ:Ty] = d#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_spctor
  : (spctor v x t1 t2)[σ:Ty] = spctor v x t1[σ:_] (λ i => (t2 i)[σ:_])
:= by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor0 : (ctor0 c)[σ:Ty] = ctor0 c[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor1 : (ctor1 c t)[σ:Ty] = ctor1 c[σ:_] t[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor2 : (ctor2 c t1 t2)[σ:Ty] = ctor2 c[σ:_] t1[σ:_] t2[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_tbind : (tbind b A t)[σ:Ty] = tbind b A t[σ.lift:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lam : (lam A t)[σ:Ty] = lam A[σ:_] t[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.cast_lam : (cast T c t)[σ:Ty] = cast T[σ.lift:_] c[σ:_] t[σ:_] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_match
  : (mtch m n t1 t2 t3)[σ:Ty]
    = mtch m n (λ i => (t1 i)[σ:_]) t2 (λ i => (t3 i)[σ:_])
:= by
  simp [SubstMap.smap]

theorem Term.Ty.apply_id {t : Term} : t[+0:Ty] = t := by
  induction t
  all_goals (simp at * <;> try simp [*])

instance : SubstMapId Term Ty where
  apply_id := Term.Ty.apply_id

@[simp]
theorem Term.hcompose_var {σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ) x = (Term.from_action (σ x))[τ:Ty]
:= by
  simp [Subst.hcompose, Term.from_action]
  generalize zdef : σ x = z
  cases z <;> simp

instance : SubstMapStable Term where
  apply_stable := by subst_solve_stable

theorem Term.apply_ren_commute {s : Term} (r : Ren) (τ : Subst Ty)
  : s⟨r⟩[τ:Ty] = s[τ:Ty]⟨r⟩
:= by
  induction s generalizing r τ <;> simp at *
  all_goals try simp [*]

instance : SubstMapRenCommute Term Ty where
  apply_ren_commute := Term.apply_ren_commute

instance : SubstMapRenComposeLeft Term Ty where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Term Ty where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose Term Ty where
  apply_compose := by subst_solve_compose

instance : SubstMapId Term Term where
  apply_id := by subst_solve_id

instance : SubstMapHetCompose Term Ty where
  apply_hcompose := by subst_solve_compose

instance : SubstMapRenComposeLeft Term Term where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Term Term where
  apply_ren_compose_right := by subst_solve_compose

instance : SubstMapCompose Term Term where
  apply_compose := by subst_solve_compose

-- inductive IteratedSubst where
-- | nil : IteratedSubst
-- | term : Subst Term -> IteratedSubst -> IteratedSubst
-- | type : Subst Ty -> IteratedSubst -> IteratedSubst

-- def Term.isubst (t : Term) : IteratedSubst -> Term
-- | .nil => t
-- | .term σ tl => t[σ].isubst tl
-- | .type σ tl => t[σ:Ty].isubst tl

@[simp]
def Pattern.smap (σ : Subst Ty) : Pattern m -> Pattern m
| .nil => .nil
| .cons ⟨s, i, ℓ, j⟩ tl => ⟨s, i, ℓ[σ:Ty], j⟩::(smap σ tl)

instance : SubstMap (Pattern m) Ty where
  smap := Pattern.smap

@[simp]
theorem Pattern.subst_nil : (.nil : Pattern 0)[σ:Ty] = .nil := by
  simp [SubstMap.smap]

@[simp]
theorem Pattern.subst_cons {tl : Pattern m} : (⟨s, i, ℓ, j⟩::tl)[σ:Ty] = ⟨s, i, ℓ[σ:Ty], j⟩::tl[σ:_] := by
  simp [SubstMap.smap]

end Core
