-- import LeanSubst

-- namespace LeanSubst.Examples.ArityGeneric

--   inductive Vec.{u} (A : Sort u) : Nat -> Sort (imax u 1) where
--   | nil : Vec A 0
--   | cons {n} : A -> Vec A n -> Vec A (n + 1)

--   @[simp]
--   def Vec.map {A B n} (f : A -> B) : Vec A n -> Vec B n
--   | nil => nil
--   | cons hd tl => cons (f hd) (tl.map f)

--   inductive VariantSort where
--   | ctor | bind

--   inductive Term (V : VariantSort -> Nat -> Prop) where
--   | var : Nat -> Term V
--   | bind {n} : V .bind n -> Vec (Term V) n -> Term V -> Term V
--   | ctor {n} : V .ctor n -> Vec (Term V) n -> Term V
--   | variadic n : Term V -> Vec (Term V) n -> Term V

--   variable {V : VariantSort -> Nat -> Prop}

--   @[coe]
--   def Term.from_action : Subst.Action (Term V) -> Term V
--   | .re y => var y
--   | .su t => t

--   @[coe]
--   def Term.Vec.from_action {n} (v : Vec (Subst.Action (Term V)) n) : Vec (Term V) n :=
--     Vec.map Term.from_action v

--   @[simp]
--   theorem Term.from_action_id {n}
--     : from_action (+0.act n) = @var V n
--   := by
--     simp [from_action, Subst.id]

--   @[simp]
--   theorem Term.from_action_succ {n}
--     : from_action (+1.act n) = @var V (n + 1)
--   := by
--     simp [from_action, Subst.succ]

--   @[simp]
--   theorem Term.from_acton_re {n}
--     : from_action (.re n) = @var V n
--   := by simp [from_action]

--   @[simp]
--   theorem Term.from_action_su {t : Term V} : from_action (.su t) = t := by simp [from_action]

--   instance instCoe_SubstActionTerm_Term : Coe (Subst.Action (Term V)) (Term V) where
--     coe := Term.from_action

--   instance {n} : Coe (Vec (Subst.Action (Term V)) n) (Vec (Term V) n) where
--     coe := Term.Vec.from_action

--   mutual
--     @[simp]
--     def Term.rmap (r : Ren) : Term V -> Term V
--     | var x => var (r.act x)
--     | bind v ts t => bind v (Vec.rmap r ts) (rmap r.lift t)
--     | ctor v ts => ctor v (Vec.rmap r ts)
--     | variadic n t ts => variadic n (rmap r t) (Vec.rmap r ts)

--     @[simp]
--     def Term.Vec.rmap {n} (r : Ren) : Vec (Term V) n -> Vec (Term V) n
--     | .nil => .nil
--     | .cons hd tl => .cons (hd.rmap r) (Vec.rmap r tl)
--   end

--   instance : RenMap (Term V) where
--     rmap := Term.rmap

--   @[simp, grind =]
--   theorem Term.Vec.rmap_is_map {n} (r : Ren) : (v : Vec (Term V) n) -> Vec.rmap r v = v.map (·⟨r⟩)
--   | .nil => by rfl
--   | .cons hd tl =>
--     have ih := Term.Vec.rmap_is_map r tl
--     by simp [RenMap.rmap, ih]

--   @[simp]
--   theorem Term.ren_var {x} {r : Ren} : (Term.var (V := V) x)⟨r⟩ = .var (r.act x) := by
--     simp [RenMap.rmap]

--   @[simp]
--   theorem Term.ren_bind {n} {v : V .bind n} {ts t} {r : Ren}
--     : (bind v ts t)⟨r⟩ = .bind v (ts.map (·⟨r⟩)) t⟨r.lift⟩
--   := by
--     simp [RenMap.rmap]

--   @[simp]
--   theorem Term.ren_ctor {n} {v : V .ctor n} {ts} {r : Ren}
--     : (Term.ctor v ts)⟨r⟩ = .ctor v (ts.map (·⟨r⟩))
--   := by
--     simp [RenMap.rmap]

--   @[simp]
--   theorem Term.ren_variadic {n} {t : Term V} {ts} {r : Ren}
--     : (Term.variadic n t ts)⟨r⟩ = .variadic n t⟨r⟩ (ts.map (·⟨r⟩))
--   := by
--     simp [RenMap.rmap]

--   instance : RenMapId (Term V) where
--     apply_id := sorry

--   instance : RenMapCompose (Term V) where
--     apply_compose := sorry

--   mutual
--     @[simp]
--     def Term.smap (σ : Subst (Term V)) : Term V -> Term V
--     | var x => σ.act x
--     | bind v ts t => bind v (Vec.smap σ ts) (smap σ.lift t)
--     | ctor v ts => ctor v (Vec.smap σ ts)
--     | variadic n t ts => variadic n (smap σ t) (Vec.smap σ ts)

--     @[simp]
--     def Term.Vec.smap {n} (σ : Subst (Term V)) : Vec (Term V) n -> Vec (Term V) n
--     | .nil => .nil
--     | .cons hd tl => .cons (hd.smap σ) (Vec.smap σ tl)
--   end

--   @[simp, grind =]
--   theorem Term.Vec.smap_is_map {n} (σ : Subst (Term V)) : (v : Vec (Term V) n) -> Vec.smap σ v = Vec.map (Term.smap σ ·) v
--   | .nil => by rfl
--   | .cons hd tl => sorry

--   instance : SubstMap (Term V) (Term V) where
--     smap := Term.smap

--   @[simp]
--   theorem Term.subst_var {x} {σ : Subst (Term V)} : (.var x)[σ] = σ.act x := by
--     simp [SubstMap.smap]

--   @[simp]
--   theorem Term.subst_bind {n} {v : V .bind n} {ts t} {σ : Subst (Term V)}
--     : (bind v ts t)[σ:Term V] = .bind v (ts.map (·[σ])) t[σ.lift]
--   := by
--     simp [SubstMap.smap]

--   @[simp]
--   theorem Term.subst_ctor {n} {v : V .ctor n} {ts} {σ : Subst (Term V)}
--     : (.ctor v ts)[σ] = .ctor v (ts.map (·[σ]))
--   := by
--     simp [SubstMap.smap]

--   @[simp]
--   theorem Term.subst_variadic {n t ts} {σ : Subst (Term V)}
--     : (.variadic n t ts)[σ] = .variadic n t[σ] (ts.map (·[σ]))
--   := by
--     simp [SubstMap.smap]

--   @[simp]
--   theorem Term.from_action_compose {x} {σ τ : Subst (Term V)}
--     : (from_action (σ.act x))[τ] = from_action ((σ ∘ τ).act x)
--   := by
--     simp [Term.from_action, Subst.compose]
--     generalize zdef : σ.act x = z
--     cases z <;> simp [Term.from_action]

--   instance : SubstMapId (Term V) (Term V) where
--     apply_id := by subst_solve_id

--   instance : SubstMapStable (Term V) where
--     apply_stable := by subst_solve_stable

--   instance : SubstMapRenComposeLeft (Term V) (Term V) where
--     apply_ren_compose_left := by subst_solve_compose

--   instance : SubstMapRenComposeRight (Term V) (Term V) where
--     apply_ren_compose_right := by subst_solve_compose

--   instance : SubstMapCompose (Term V) (Term V) where
--     apply_compose := by subst_solve_compose

-- end LeanSubst.Examples.ArityGeneric
