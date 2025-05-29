import SystemFD.Util
import SystemFD.Term
import SystemFD.Ctx


@[simp]
def bind2_frame (T : Term) : Bind2Variant -> Frame Term
| .all => .kind T
| .lamt => .kind T
| .lam => .type T
| .arrow => .empty
| .allc => .kind T
| .arrowc => .empty

inductive Red : Ctx Term -> Term -> Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red Γ ((`λ[A] b) `@ t) (b β[t])
| betat : Red Γ ((Λ[A] b) `@t t) (b β[t])
| letbeta : Red Γ (.letterm A t b) (b β[t])
| cast : Red Γ (t ▹ refl! K A) t
| sym : Red Γ (sym! (refl! K A)) (refl! K A)
| seq : Red Γ ((refl! K A) `; (refl! K A)) (refl! K A)
| appc : Red Γ (refl! (K1 -k> K2) A `@c (refl! K1 B)) (refl! K2 (A `@k B))
| apptc : Red Γ (refl! K1 (∀[K2] A) `@c[refl! K2 B]) (refl! K1 (A β[B]))
| fst : Red Γ (fst! K1 (refl! K2 (A `@k B))) (refl! (K1 -k> K2) A)
| snd : Red Γ (snd! K1 (refl! K2 (A `@k B))) (refl! K1 B)
| allc : Red Γ (∀c[A] refl! K B) (refl! K (∀[A] B))
| arrowc : Red Γ (refl! ★ A -c> refl! ★ B) (refl! ★ (A -t> B))
| choice1 : Red Γ (`0 ⊕ t) t
| choice2 : Red Γ (t ⊕ `0) t
----------------------------------------------------------------
---- Ite Matching
----------------------------------------------------------------
| ite_matched :
  .some (x, sp) = Term.neutral_form p ->
  .some (x, sp') = Term.neutral_form s ->
  .some q = prefix_equal sp sp' ->
  Γ.is_ctor x ->
  Red Γ (.ite p s b e) (b.apply_spine q)
| ite_missed :
  .some (x, sp) = Term.neutral_form p ->
  .some (x', sp') = Term.neutral_form s ->
  Γ.is_stable_red x' ->
  x ≠ x' ∨ prefix_equal sp sp' = .none ->
  Red Γ (.ite p s b e) e
----------------------------------------------------------------
---- Guard Matching
----------------------------------------------------------------
| guard_matched :
  .some (x, sp) = Term.neutral_form p ->
  .some (x, sp') = Term.neutral_form s ->
  .some q = prefix_equal sp sp' ->
  Red Γ (.guard p s b) (b.apply_spine q)
| guard_missed :
  .some (x, sp) = Term.neutral_form p ->
  .some (x', sp') = Term.neutral_form s ->
  Γ.is_stable_red x' ->
  x ≠ x' ∨ prefix_equal sp sp' = .none ->
  Red Γ (.guard p s b) `0
----------------------------------------------------------------
---- Instance Instantiation
----------------------------------------------------------------
| inst :
  .some (x, sp) = Term.neutral_form h ->
  Γ.is_openm x ->
  tl = get_instances Γ x ->
  tl' = List.map (λ x => x.apply_spine sp) tl ->
  h' = List.foldl (·⊕·) `0 tl' ->
  Red Γ h h'
----------------------------------------------------------------
---- Local Let Substitution
----------------------------------------------------------------
| letterm :
  .some (x, sp) = Term.neutral_form h ->
  .term _ t = Γ d@ x ->
  Red Γ h (t.apply_spine sp)
----------------------------------------------------------------
---- Congruence Rules
----------------------------------------------------------------
| ctor1_congr :
  Red Γ t t' ->
  Red Γ (.ctor1 v t) (.ctor1 v t')
| ctor2_congr1 :
  ctor2_has_congr1 v ->
  Red Γ t1 t1' ->
  Red Γ (.ctor2 v t1 t2) (.ctor2 v t1' t2)
| ctor2_congr2 :
  ctor2_has_congr2 v ->
  Red Γ t2 t2' ->
  Red Γ (.ctor2 v t1 t2) (.ctor2 v t1 t2')
| bind2_congr1 :
  bind2_has_congr1 v ->
  Red Γ t1 t1' ->
  Red Γ (.bind2 v t1 t2) (.bind2 v t1' t2)
| bind2_congr2 :
  bind2_has_congr2 v ->
  Red (bind2_frame t1 v :: Γ) t2 t2' ->
  Red Γ (.bind2 v t1 t2) (.bind2 v t1 t2')
| ite_congr :
  Red Γ s s' ->
  Red Γ (.ite p s b e) (.ite p s' b e)
| guard_congr :
  Red Γ s s' ->
  Red Γ (.guard p s b) (.guard p s' b)
----------------------------------------------------------------
---- Absorption Rules
----------------------------------------------------------------
| ctor1_absorb :
  Red Γ (.ctor1 v `0) `0
| ctor2_absorb1 :
  ctor2_has_congr1 v ->
  Red Γ (.ctor2 v `0 t2) `0
| ctor2_absorb2 :
  ctor2_has_congr2 v ->
  Red Γ (.ctor2 v t1 `0) `0
| bind2_absorb1 :
  bind2_has_congr1 v ->
  Red Γ (.bind2 v `0 t2) `0
| bind2_absorb2 :
  bind2_has_congr2 v ->
  Red Γ (.bind2 v t1 `0) `0
| ite_absorb :
  Red Γ (.ite p `0 b e) `0
| guard_absorb :
  Red Γ (.guard p `0 b) `0
----------------------------------------------------------------
---- Mapping Rules
----------------------------------------------------------------
| ctor1_map :
  Red Γ (.ctor1 v (c1 ⊕ c2)) (.ctor1 v c1 ⊕ .ctor1 v c2)
| ctor2_map1 :
  ctor2_has_congr1 v ->
  v ≠ .choice ->
  Red Γ (.ctor2 v (c1 ⊕ c2) t2) (.ctor2 v c1 t2 ⊕ .ctor2 v c2 t2)
| ctor2_map2 :
  ctor2_has_congr2 v ->
  v ≠ .choice ->
  Red Γ (.ctor2 v t1 (c1 ⊕ c2)) (.ctor2 v t1 c1 ⊕ .ctor2 v t1 c2)
| bind2_map1 :
  bind2_has_congr1 v ->
  Red Γ (.bind2 v (c1 ⊕ c2) t2) (.bind2 v c1 t2 ⊕ .bind2 v c2 t2)
| bind2_map2 :
  bind2_has_congr2 v ->
  Red Γ (.bind2 v t1 (c1 ⊕ c2)) (.bind2 v t1 c1 ⊕ .bind2 v t1 c2)
| ite_map :
  Red Γ (.ite p (c1 ⊕ c2) b e) (.ite p c1 b e ⊕ .ite p c2 b e)
| guard_map :
  Red Γ (.guard p (c1 ⊕ c2) b) (.guard p c1 b ⊕ .guard p c2 b)

inductive RedStar : Ctx Term -> Term -> Term -> Prop where
| refl : RedStar Γ x x
| step : RedStar Γ x y -> Red Γ y z -> RedStar Γ x z
