import LeanSubst
import Core.Util
import Core.Vec
import Core.Term.Definition

import Core.Ty

open LeanSubst
open Lilac

namespace Core

@[coe]
def Term.from_action : Action Term -> Term
| .re y => #y
| .su t => t

@[simp]
theorem Term.from_action_id {n} : from_action (+0σ.act n) = #n := by
  simp [from_action, Subst.id]

@[simp]
theorem Term.from_action_succ {n} : from_action (+1σ.act n) = # (n + 1) := by
  simp [from_action, Subst.succ]

@[simp]
theorem Term.from_acton_re {n} : from_action (re n) = #n := by simp [from_action]

@[simp]
theorem Term.from_action_su {t} : from_action (su t) = t := by simp [from_action]

instance : Coe (Action Term) Term where
  coe := Term.from_action

@[simp]
def Term.rmap (r : Ren Term) : Term -> Term
| #x => # (r.act x)
| d#x => d#x
| spctor v x t1 t2 t3 => spctor v x t1 t2 (rmap r <$> t3)
| ctor0 c => ctor0 c
| ctor1 c t => ctor1 c (rmap r t)
| ctor2 c t1 t2 => ctor2 c (rmap r t1) (rmap r t2)
| tbind v A t => tbind v A (rmap r t)
| lam A t => lam A (rmap r.lift t)
| cast T c t => cast T (rmap r c) (rmap r t)
| mtch m n t1 t2 t3 => mtch m n (rmap r <$> t1) t2 (λ i => rmap (r.lift (t2 i).bind) (t3 i))

instance : RenMap Term Term where
  rmap := Term.rmap

@[simp]
theorem Term.ren_var {r : Ren Term} : (#x)⟨r⟩ = # (r.act x) := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_global {r : Ren Term} : (d#x)⟨r⟩ = d#x := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_spctor {r : Ren Term}
  : (spctor v x t1 t2 t3)⟨r⟩ = spctor v x t1 t2 (λ i => (t3 i)⟨r⟩)
:= by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_ctor0 {r : Ren Term} : (ctor0 v)⟨r⟩ = ctor0 v := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_ctor1 {r : Ren Term} : (ctor1 v t)⟨r⟩ = ctor1 v t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_ctor2 {r : Ren Term} : (ctor2 v t1 t2)⟨r⟩ = ctor2 v t1⟨r⟩ t2⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_tbind {r : Ren Term} : (tbind v A t)⟨r⟩ = tbind v A t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_lam {r : Ren Term} : (lam A t)⟨r⟩ = lam A t⟨r.lift⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_cast {r : Ren Term} : (cast T c t)⟨r⟩ = cast T c⟨r⟩ t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.ren_match {r : Ren Term}
  : (mtch m n t1 t2 t3)⟨r⟩
    = mtch m n (λ i => (t1 i)⟨r⟩) t2 (λ i => (t3 i)⟨r.lift (t2 i).bind⟩)
:= by
  simp [RenMap.rmap]

instance : RenMapId Term Term where
  apply_id := by subst_solve_id

instance : RenMapCompose Term Term where
  apply_compose := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift, *]
      try grind)
    case mtch ih1 ih2 =>
      simp [-Subst.rewrite_lift_k_ren, *]
    --subst_solve_compose

@[simp]
def Ctor0Variant.rmap (r : Ren Ty) : Ctor0Variant -> Ctor0Variant
| refl A => refl A⟨r⟩

instance : RenMap Ctor0Variant Ty where
  rmap := Ctor0Variant.rmap

@[simp]
theorem Ctor0Variant.ren_refl {r : Ren Ty} : (refl A)⟨r⟩ = refl A⟨r⟩ := by
  simp [RenMap.rmap]

instance : RenMapId Ctor0Variant Ty where
  apply_id := by intro s; cases s <;> simp

instance : RenMapCompose Ctor0Variant Ty where
  apply_compose := by intro s; cases s <;> simp

@[simp]
def Ctor0Variant.smap (_ : Subst Ctor0Variant) : Ctor0Variant -> Ctor0Variant
| c => c

instance : SubstMap Ctor0Variant Ctor0Variant where
  smap := Ctor0Variant.smap

@[simp]
theorem Ctor0Variant.subst_ {c : Ctor0Variant} {σ : Subst Ctor0Variant} : c[σ] = c := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor0Variant Ctor0Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor0Variant Ctor0Variant where
  apply_compose := by simp

@[simp]
def Ctor0Variant.Ty.smap (σ : Subst Ty) : Ctor0Variant -> Ctor0Variant
| refl A => refl A[σ]

instance : SubstMap Ctor0Variant Ty where
  smap := Ctor0Variant.Ty.smap

@[simp]
theorem Ctor0Variant.subst_refl {σ : Subst Ty} : (refl A)[σ] = refl A[σ] := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor0Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor0Variant Ty where
  apply_compose := by intro s σ τ; cases s <;> simp

instance : SubstMapHetCompose Ctor0Variant Ty where
  apply_hcompose := by simp

@[simp]
def Ctor1Variant.rmap (r : Ren Ty) : Ctor1Variant -> Ctor1Variant
| prj n => prj n
| appt a => appt a⟨r⟩

instance : RenMap Ctor1Variant Ty where
  rmap := Ctor1Variant.rmap

@[simp]
theorem Ctor1Variant.ren_fst {r : Ren Ty} : (prj n)⟨r⟩ = prj n := by
  simp [RenMap.rmap]

@[simp]
theorem Ctor1Variant.ren_appt {r : Ren Ty} : (appt a)⟨r⟩ = appt a⟨r⟩ := by
  simp [RenMap.rmap]

instance : RenMapId Ctor1Variant Ty where
  apply_id := by intro s; cases s <;> simp

instance : RenMapCompose Ctor1Variant Ty where
  apply_compose := by intro s; cases s <;> simp

@[simp]
def Ctor1Variant.smap (_ : Subst Ctor1Variant) : Ctor1Variant -> Ctor1Variant
| c => c

instance : SubstMap Ctor1Variant Ctor1Variant where
  smap := Ctor1Variant.smap

@[simp]
theorem Ctor1Variant.subst_ {c : Ctor1Variant} {σ : Subst Ctor1Variant} : c[σ] = c := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor1Variant Ctor1Variant where
  apply_id := by simp

instance : SubstMapCompose Ctor1Variant Ctor1Variant where
  apply_compose := by simp

@[simp]
def Ctor1Variant.Ty.smap (σ : Subst Ty) : Ctor1Variant -> Ctor1Variant
| prj n => prj n
| appt a => appt a[σ]

instance : SubstMap Ctor1Variant Ty where
  smap := Ctor1Variant.Ty.smap

@[simp]
theorem Ctor1Variant.subst_fst {σ : Subst Ty} : (prj n)[σ] = prj n := by
  simp [SubstMap.smap]

@[simp]
theorem Ctor1Variant.subst_appt {σ : Subst Ty} : (appt a)[σ] = appt a[σ] := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor1Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor1Variant Ty where
  apply_compose := by intro s σ τ; cases s <;> simp

instance : SubstMapHetCompose Ctor1Variant Ty where
  apply_hcompose := by simp

@[simp]
def Ctor2Variant.rmap (_ : Ren Ty) : Ctor2Variant -> Ctor2Variant
| c => c

instance : RenMap Ctor2Variant Ty where
  rmap := Ctor2Variant.rmap

instance : RenMapId Ctor2Variant Ty where
  apply_id := by intro s; cases s <;> simp [rmap]

instance : RenMapCompose Ctor2Variant Ty where
  apply_compose := by intro s; cases s <;> simp [rmap]

@[simp]
theorem Ctor2Variant.subst_ren {c : Ctor2Variant} {r : Ren Ty} : c⟨r⟩ = c := by
  simp [RenMap.rmap]

@[simp]
def Ctor2Variant.smap (_ : Subst Ctor2Variant) : Ctor2Variant -> Ctor2Variant
| c => c

instance : SubstMap Ctor2Variant Ctor2Variant where
  smap := Ctor2Variant.smap

@[simp]
theorem Ctor2Variant.subst_ {c : Ctor2Variant} {σ : Subst Ctor2Variant}: c[σ] = c := by
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
theorem Ctor2Variant.Ty.subst_ {c : Ctor2Variant} {σ : Subst Ty} : c[σ] = c := by
  simp [SubstMap.smap]

instance : SubstMapId Ctor2Variant Ty where
  apply_id := by intro t; cases t <;> simp

instance : SubstMapCompose Ctor2Variant Ty where
  apply_compose := by simp

instance : SubstMapHetCompose Ctor2Variant Ty where
  apply_hcompose := by simp

@[simp]
def Pattern.rmap (r : Ren Ty) : Pattern m -> Pattern m
| .nil => .nil
| .cons ⟨s, i, ℓ, j⟩ tl => ⟨s, i, ℓ⟨r⟩, j⟩::(rmap r tl)

instance : RenMap (Pattern m) Ty where
  rmap := Pattern.rmap

@[simp]
theorem Pattern.ren_nil {r : Ren Ty} : (.nil : Pattern 0)⟨r⟩ = .nil := by
  simp [RenMap.rmap]

@[simp]
theorem Pattern.ren_cons {r : Ren Ty} {tl : Pattern m} : (⟨s, i, ℓ, j⟩::tl)⟨r⟩ = ⟨s, i, ℓ⟨r⟩, j⟩::tl⟨r⟩ := by
  simp [RenMap.rmap]

instance : RenMapId (Pattern m) Ty where
  apply_id := by
    intro s; induction s; simp
    case _ t1 t2 ih =>
      rcases t1 with ⟨s, i, ℓ, j⟩; simp [*]

instance : RenMapCompose (Pattern m) Ty where
  apply_compose := by
    intro s r1 r2; induction s generalizing r1 r2; simp
    case _ t1 t2 ih =>
      rcases t1 with ⟨s, i, ℓ, j⟩; simp [*]

@[simp]
def Pattern.smap (σ : Subst Ty) : Pattern m -> Pattern m
| .nil => .nil
| .cons ⟨s, i, ℓ, j⟩ tl => ⟨s, i, ℓ[σ], j⟩::(smap σ tl)

instance : SubstMap (Pattern m) Ty where
  smap := Pattern.smap

@[simp]
theorem Pattern.subst_nil {σ : Subst Ty} : (.nil : Pattern 0)[σ] = .nil := by
  simp [SubstMap.smap]

@[simp]
theorem Pattern.subst_cons {σ : Subst Ty} {tl : Pattern m} : (⟨s, i, ℓ, j⟩::tl)[σ] = ⟨s, i, ℓ[σ], j⟩::tl[σ] := by
  simp [SubstMap.smap]

instance : SubstMapId (Pattern m) Ty where
  apply_id := by
    intro t; induction t; simp
    case _ x p ih =>
    rcases x with ⟨a, b, c, d⟩; simp [*]

instance : SubstMapCompose (Pattern m) Ty where
  apply_compose := by
    intro s σ τ; induction s; simp
    case _ x p ih =>
    rcases x with ⟨n, a, m, b⟩; simp [*]

@[simp]
theorem Pattern.subst_bind {σ : Subst Ty} {p : Pattern m} : p[σ].bind = p.bind := by
  induction p; simp; case _ x p ih =>
  rcases x with ⟨n, a, m, b⟩; simp [bind, *]

@[simp]
theorem Pattern.ren_bind {r : Ren Ty} {p : Pattern m} : p⟨r⟩.bind = p.bind := by
  induction p; simp; case _ x p ih =>
  rcases x with ⟨n, a, m, b⟩; simp [bind, *]

@[simp]
theorem Pattern.subst_bind_type {σ : Subst Ty} {p : Pattern m} : p[σ].bind_type = p.bind_type := by
  induction p; simp; case _ x p ih =>
  rcases x with ⟨n, a, m, b⟩; simp [bind_type, *]

@[simp]
theorem Pattern.ren_bind_type {r : Ren Ty} {p : Pattern m} : p⟨r⟩.bind_type = p.bind_type := by
  induction p; simp; case _ x p ih =>
  rcases x with ⟨n, a, m, b⟩; simp [bind_type, *]

@[simp]
def Term.Ty.rmap (r : Ren Ty) : Term -> Term
| #x => #x
| d#x => d#x
| spctor v x t1 t2 t3 => spctor v x t1⟨r⟩ t2⟨r⟩ (rmap r <$> t3)
| ctor0 c => ctor0 c⟨r⟩
| ctor1 c t => ctor1 c⟨r⟩ (rmap r t)
| ctor2 c t1 t2 => ctor2 c⟨r⟩ (rmap r t1) (rmap r t2)
| tbind v A t => tbind v A (rmap r.lift t)
| lam A t => lam A⟨r⟩ (rmap r t)
| cast T c t => cast T⟨r.lift⟩ (rmap r c) (rmap r t)
| mtch m n t1 t2 t3 =>
  let t2' : Fun.Vec (Pattern m) n := λ i => (t2 i)⟨r⟩
  let t3' := λ i => rmap (r.lift (t2 i).bind_type) (t3 i)
  mtch m n (rmap r <$> t1) t2' t3'

instance : RenMap Term Ty where
  rmap := Term.Ty.rmap

@[simp]
def Term.Ty.smap (σ : Subst Ty) : Term -> Term
| #x => #x
| d#x => d#x
| spctor v x t1 t2 t3 => spctor v x t1[σ] t2[σ] (smap σ <$> t3)
| ctor0 c => ctor0 c[σ]
| ctor1 c t => ctor1 c[σ] (smap σ t)
| ctor2 c t1 t2 => ctor2 c[σ] (smap σ t1) (smap σ t2)
| tbind v A t => tbind v A (smap σ.lift t)
| lam A t => lam A[σ] (smap σ t)
| cast T c t => cast T[σ.lift] (smap σ c) (smap σ t)
| mtch m n t1 t2 t3 =>
  let t2' : Fun.Vec (Pattern m) n := λ i => (t2 i)[σ]
  let t3' := λ i => smap (σ.lift (t2 i).bind_type) (t3 i)
  mtch m n (smap σ <$> t1) t2' t3'

instance : SubstMap Term Ty where
  smap := Term.Ty.smap

@[simp]
def Term.smap (σ : Subst Term) : Term -> Term
| #x => σ.act x
| d#x => d#x
| spctor v x t1 t2 t3 => spctor v x t1 t2 (smap σ <$> t3)
| ctor0 c => ctor0 c
| ctor1 c t => ctor1 c (smap σ t)
| ctor2 c t1 t2 => ctor2 c (smap σ t1) (smap σ t2)
| tbind v A t => tbind v A (smap (σ ◾ Ren.succ Ty) t)
| lam A t => lam A (smap σ.lift t)
| cast T c t => cast T (smap σ c) (smap σ t)
| mtch m n t1 t2 t3 =>
  let t3' := λ i => smap ((σ.lift (t2 i).bind) ◾ (@Subst.add Ty (t2 i).bind_type)) (t3 i)
  mtch m n (smap σ <$> t1) t2 t3'

instance : SubstMap Term Term where
  smap := Term.smap

@[simp]
theorem Term.subst_var {σ : Subst Term} : (#x)[σ] = σ.act x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_global {σ : Subst Term} : (d#x)[σ] = d#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_spctor {σ : Subst Term}
  : (spctor v x t1 t2 t3)[σ] = spctor v x t1 t2 (λ i => (t3 i)[σ])
:= by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_ctor0 {σ : Subst Term} : (ctor0 v)[σ] = ctor0 v := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_ctor1 {σ : Subst Term} : (ctor1 v t)[σ] = ctor1 v t[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_ctor2 {σ : Subst Term} : (ctor2 v t1 t2)[σ] = ctor2 v t1[σ] t2[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_tbind {σ : Subst Term} : (tbind v A t)[σ] = tbind v A t[σ ◾ Ren.succ Ty] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_lam {σ : Subst Term}: (lam A t)[σ] = lam A t[σ.lift] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_cast {σ : Subst Term}: (cast T c t)[σ] = cast T c[σ] t[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.subst_match {σ : Subst Term}
  : (mtch m n t1 t2 t3)[σ]
    = mtch m n (λ i => (t1 i)[σ]) t2 (λ i => (t3 i)[(σ.lift (t2 i).bind) ◾ (@Subst.add Ty (t2 i).bind_type)])
:= by
  simp [SubstMap.smap]

@[simp]
theorem Term.from_action_compose {x : Nat} {σ τ : Subst Term}
  : (from_action (σ.act x))[τ] = from_action ((σ ∘ τ).act x)
:= by
  simp [Term.from_action, Subst.compose]
  generalize zdef : σ.act x = z
  cases z <;> simp [Term.from_action]

@[simp]
theorem Term.Ty.rmap_var {r : Ren Ty} : (#x)⟨r⟩ = #x := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_global {r : Ren Ty} : (d#x)⟨r⟩ = d#x := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_spctor {r : Ren Ty}
  : (spctor v x t1 t2 t3)⟨r⟩ = spctor v x t1⟨r⟩ t2⟨r⟩ (λ i => (t3 i)⟨r⟩)
:= by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_ctor0 {r : Ren Ty} : (ctor0 c)⟨r⟩ = ctor0 c⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_ctor1 {r : Ren Ty} : (ctor1 c t)⟨r⟩ = ctor1 c⟨r⟩ t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_ctor2 {r : Ren Ty} : (ctor2 c t1 t2)⟨r⟩ = ctor2 c⟨r⟩ t1⟨r⟩ t2⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_tbind {r : Ren Ty} : (tbind b A t)⟨r⟩ = tbind b A t⟨r.lift⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_lam {r : Ren Ty} : (lam A t)⟨r⟩ = lam A⟨r⟩ t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_cast {r : Ren Ty} : (cast T c t)⟨r⟩ = cast T⟨r.lift⟩ c⟨r⟩ t⟨r⟩ := by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.rmap_match {r : Ren Ty}
  : (mtch m n t1 t2 t3)⟨r⟩
    = mtch m n (λ i => (t1 i)⟨r⟩) (λ i => (t2 i)⟨r⟩) (λ i => (t3 i)⟨r.lift (t2 i).bind_type⟩)
:= by
  simp [RenMap.rmap]

@[simp]
theorem Term.Ty.subst_var {σ : Subst Ty} : (#x)[σ] = #x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_global {σ : Subst Ty} : (d#x)[σ] = d#x := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_spctor {σ : Subst Ty}
  : (spctor v x t1 t2 t3)[σ] = spctor v x t1[σ] t2[σ] (λ i => (t3 i)[σ])
:= by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor0 {σ : Subst Ty} : (ctor0 c)[σ] = ctor0 c[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor1 {σ : Subst Ty} : (ctor1 c t)[σ] = ctor1 c[σ] t[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_ctor2 {σ : Subst Ty} : (ctor2 c t1 t2)[σ] = ctor2 c[σ] t1[σ] t2[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_tbind {σ : Subst Ty} : (tbind b A t)[σ] = tbind b A t[σ.lift] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_lam {σ : Subst Ty} : (lam A t)[σ] = lam A[σ] t[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_cast {σ : Subst Ty} : (cast T c t)[σ] = cast T[σ.lift] c[σ] t[σ] := by
  simp [SubstMap.smap]

@[simp]
theorem Term.Ty.subst_match {σ : Subst Ty}
  : (mtch m n t1 t2 t3)[σ]
    = mtch m n (λ i => (t1 i)[σ]) (λ i => (t2 i)[σ]) (λ i => (t3 i)[σ.lift (t2 i).bind_type])
:= by
  simp [SubstMap.smap]

instance : RenMapId Term Ty where
  apply_id := by intro s; induction s <;> simp [*]

instance : RenMapCompose Term Ty where
  apply_compose := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapId Term Ty where
  apply_id := by subst_solve_id

@[simp]
theorem Term.from_action_hcompose {x : Nat} {σ : Subst Term} {τ : Subst Ty}
  : (from_action (σ.act x))[τ] = from_action ((σ ◾ τ).act x)
:= by
  simp [from_action]
  generalize zdef : σ.act x = z
  cases z <;> simp

@[simp]
theorem Term.from_action_compose_ren {x : Nat} {σ : Subst Term} {r : Ren Term}
  : (from_action (σ.act x))⟨r⟩ = from_action ((σ ∘ r).act x)
:= by
  simp [Term.from_action]
  generalize zdef : σ.act x = z
  cases z <;> simp

@[simp]
theorem Term.from_action_hcompose_ren {x : Nat} {σ : Subst Term} {r : Ren Ty}
  : (from_action (σ.act x))⟨r⟩ = from_action ((σ ◾ r).act x)
:= by
  simp [Term.from_action]
  generalize zdef : σ.act x = z
  cases z <;> simp

@[simp]
theorem Term.hcompose_var {x : Nat} {σ : Subst Term} {τ : Subst Ty}
  : (σ ◾ τ).act x = (Term.from_action (σ.act x))[τ]
:= by
  simp [Subst.hcompose, Term.from_action]
  generalize zdef : σ.act x = z
  cases z <;> simp

instance : SubstMapStable Term Term where
  apply_stable := by
    intro r σ h; funext; case _ t =>
    replace h := Eq.symm h
    induction t generalizing r σ <;> simp [*]
    case lam => congr
    case mtch t1 t2 t3 ih1 ih2 =>
      funext; case _ i =>
      rw [<-Ren.to_lift]; simp
      generalize zdef : (0..(t2 i).bind ++ r ∘ Ren.add Term (t2 i).bind) = z
      generalize wdef : (0..(t2 i).bind ++ r.to ∘ Subst.add Term (t2 i).bind) = w
      have lem : z.to = w := by subst zdef wdef; simp
      rw [<-lem]; simp

instance : SubstMapRenCommute Term Ty where
  apply_commute_ren_subst := by
    intro s r τ; induction s generalizing r τ <;> simp [*]
  apply_commute_ren_ren := by
    intro s r τ; induction s generalizing r τ <;> simp [*]

instance : SubstMapRenComposeLeft Ctor0Variant Ty where
  apply_ren_compose_left := by intro s r τ; cases s <;> simp

instance : SubstMapRenComposeLeft Ctor1Variant Ty where
  apply_ren_compose_left := by intro s r τ; cases s <;> simp

instance : SubstMapRenComposeLeft Ctor2Variant Ty where
  apply_ren_compose_left := by intro s r τ; cases s <;> simp

instance : SubstMapRenComposeLeft (Pattern m) Ty where
  apply_ren_compose_left := by
    intro s r τ; induction s; simp
    case _ t1 t2 ih =>
      rcases t1 with ⟨q1, q2, q3, q4⟩; simp [*]

instance : SubstMapRenComposeLeft Term Ty where
  apply_ren_compose_left := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapRenComposeRight Ctor0Variant Ty where
  apply_ren_compose_right := by intro s r τ; cases s <;> simp

instance : SubstMapRenComposeRight Ctor1Variant Ty where
  apply_ren_compose_right := by intro s r τ; cases s <;> simp

instance : SubstMapRenComposeRight Ctor2Variant Ty where
  apply_ren_compose_right := by intro s r τ; cases s <;> simp

instance : SubstMapRenComposeRight (Pattern m) Ty where
  apply_ren_compose_right := by
    intro s r τ; induction s; simp
    case _ t1 t2 ih =>
      rcases t1 with ⟨q1, q2, q3, q4⟩; simp [*]

instance : SubstMapRenComposeRight Term Ty where
  apply_ren_compose_right := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapCompose Term Ty where
  apply_compose := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapId Term Term where
  apply_id := by subst_solve_id

instance : SubstMapRenComposeLeft Term Term where
  apply_ren_compose_left := by subst_solve_compose

instance : SubstMapRenComposeRight Term Term where
  apply_ren_compose_right := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapHetCompose Term Ty where
  apply_hcompose := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapRenHetCompose Term Ty where
  apply_hcompose_ren := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapCompose Term Term where
  apply_compose := by
    intro s σ τ
    induction s generalizing σ τ
    any_goals solve | simp +instances [*]
    try any_goals solve | (
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try funext; case _ x =>
      try rw [<-Ren.to_lift]
      try simp [-Subst.rewrite_lift_k, -Subst.rewrite_lift_k_ren, *]
      try grind)

instance : SubstMapStable Ctor0Variant Ty where
  apply_stable := by subst_solve_stable

instance : SubstMapStable Ctor1Variant Ty where
  apply_stable := by subst_solve_stable

instance : SubstMapStable Ctor2Variant Ty where
  apply_stable := by subst_solve_stable

instance [RenMap S T] [SubstMap S T] [SubstMapStable S T] : SubstMapStable (Vec S n) T where
  apply_stable := by subst_solve_stable

instance : SubstMapStable Term Ty where
  apply_stable := by
    intro r σ h; funext; case _ t =>
    induction t generalizing r σ <;> simp [*]
    all_goals try (· rw[Subst.apply_stable h])
    case mtch t1 t2 t3 ih1 ih2 =>
      funext; case _ i j =>
      apply And.intro
      · funext; case _ x => congr; simp [Pattern] at *; sorry
      · funext; case _ x => congr; sorry
      -- generalize zdef : [0..(t2 i).bind ++ r ∘ Ren.add Term (t2 i).bind] = z
      -- generalize wdef : (0..(t2 i).bind ++ r.to ∘ Subst.add Term (t2 i).bind) = w
      -- have lem : z.to = w := by subst zdef wdef; simp
      -- rw [<-lem]; simp
    case tbind ih => sorry
    case spctor ih => sorry
    case cast ih1 ih2 =>  sorry


theorem Term.Ty.smap_promote : Term.Ty.smap σ A = A[σ] := by simp [SubstMap.smap]

theorem Term.Ty.rmap_promote : Term.Ty.rmap r A = A⟨r⟩ := by simp [RenMap.rmap]

theorem Term.smap_promote : Term.smap σ t = t[σ] := by simp [SubstMap.smap]

theorem Term.rmap_promote : Term.rmap r t = t⟨r⟩ := by simp [RenMap.rmap]

end Core
