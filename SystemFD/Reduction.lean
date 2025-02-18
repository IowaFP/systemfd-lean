import SystemFD.Util
import SystemFD.Term
import SystemFD.Ctx

inductive Red : Ctx Term -> Term -> List Term -> Prop where
----------------------------------------------------------------
---- Basic Reduction Steps
----------------------------------------------------------------
| beta : Red Γ ((`λ[A] b) `@ t) [b β[t]]
| betat : Red Γ ((Λ[A] b) `@t t) [b β[t]]
| letbeta : Red Γ (.letterm A t t') [t' β[t]]
| cast : Red Γ (t ▹ refl! A) [t]
| sym : Red Γ (sym! (refl! A)) [refl! A]
| seq : Red Γ ((refl! A) `; (refl! A)) [refl! A]
| appc : Red Γ (refl! (A -t> B) `@c (refl! A)) [refl! B]
| fst : Red Γ (.ctor1 .fst (refl! (A `@k B))) [refl! A]
| snd : Red Γ (.ctor1 .snd (refl! (A `@k B))) [refl! B]
| allc : Red Γ (∀c[A] refl! B) [refl! (∀[A] B)]
| arrowc : Red Γ (refl! A -c> refl! B) [refl! (A -t> B)]

----------------------------------------------------------------
---- Ite matching
----------------------------------------------------------------
| ite_matched :
  .some (x, sp) = Term.neutral_form p ->
  .some (x, sp') = Term.neutral_form s ->
  .some q = prefix_equal sp sp' ->
  Term.is_ctorid Γ x ->
  Red Γ (.ite p s b e) [b.apply_spine q]
| ite_missed :
  .some (x, sp) = Term.neutral_form p ->
  .some (x', sp') = Term.neutral_form s ->
  x ≠ x' ∨ prefix_equal sp sp' = .none ->
  Red Γ (.ite p s b e) [e]

----------------------------------------------------------------
---- Guard Matching
----------------------------------------------------------------
| guard_matched :
  .some (x, sp) = Term.neutral_form p ->
  .some (x, sp') = Term.neutral_form s ->
  .some q = prefix_equal sp sp' ->
  Red Γ (.guard p s b) [b.apply_spine q]
| guard_missed :
  .some (x, sp) = Term.neutral_form p ->
  .some (x', sp') = Term.neutral_form s ->
  x ≠ x' ∨ prefix_equal sp sp' = .none ->
  Red Γ (.guard p s b) []

----------------------------------------------------------------
---- Instance Instantiation
----------------------------------------------------------------
| inst :
  .some (x, sp) = Term.neutral_form h ->
  Term.is_openmethod Γ x ->
  indices = instance_indices' Γ 0 x [] -> -- searches for the instances of open method x
  -- indices.length > 0 ->
  tl = get_instances Γ indices -> -- weakens the instances
  tl' = List.map (λ x => x.apply_spine sp) tl ->
  Red Γ h tl'


| letterm :
  .some (x, sp) = Term.neutral_form h ->
  .term _ t = Γ d@ x ->
  Red Γ h [t.apply_spine sp]

----------------------------------------------------------------
---- Contextual/Congruence rules
----------------------------------------------------------------
| app_congr :
  Red Γ f tl ->
  tl' = List.map (λ x => x `@ a) tl ->
  Red Γ (f `@ a) tl'
| appt_congr :
  Red Γ f tl ->
  tl' = List.map (λ x => x `@t a) tl ->
  Red Γ (f `@t a) tl'
| cast_congr :
  Red Γ e tl ->
  tl' = List.map (λ x => t ▹ x) tl ->
  Red Γ (t ▹ e) tl'
| ite_congr :
  Red Γ s tl ->
  tl' = List.map (λ x => .ite p x b e) tl ->
  Red Γ (.ite p s b e) tl'
| sym_congr :
  Red Γ e tl ->
  tl' = List.map (λ x => sym! x) tl ->
  Red Γ (sym! e) tl'
| seq_congr1 :
  Red Γ u tl ->
  tl' = List.map (λ x => x `; v) tl ->
  Red Γ (u `; v) tl'
| seq_congr2 :
  Red Γ v tl ->
  tl' = List.map (λ x => u `; x) tl ->
  Red Γ (u `; v) tl'
| arrowc_congr1 :
  Red Γ u tl ->
  tl' = List.map (λ x => x -c> v) tl ->
  Red Γ (u -c> v) tl'
| arrowc_congr2 :
  Red (.empty :: Γ) v tl ->
  tl' = List.map (λ x => u -c> x) tl ->
  Red Γ (u -c> v) tl'
| appc_congr1 :
  Red Γ f tl ->
  tl' = List.map (λ x => x `@c a) tl ->
  Red Γ (f `@c a) tl'
| appc_congr2 :
  Red Γ a tl ->
  tl' = List.map (λ x => f `@c x) tl ->
  Red Γ (f `@c a) tl'
| fst_congr :
  Red Γ u tl ->
  tl' = List.map (λ x => .ctor1 .fst x) tl ->
  Red Γ (.ctor1 .fst u) tl'
| snd_congr :
  Red Γ u tl ->
  tl' = List.map (λ x => .ctor1 .snd x) tl ->
  Red Γ (.ctor1 .snd u) tl'
| apptc_congr1 :
  Red Γ f tl ->
  tl' = List.map (λ x => x `@c[a]) tl ->
  Red Γ (f `@c[a]) tl'
| apptc_congr2 :
  Red Γ a tl ->
  tl' = List.map (λ x => f `@c[x]) tl ->
  Red Γ (f `@c[a]) tl'
| allc_congr :
  Red (.kind A ::Γ) e tl ->
  tl' = List.map (λ x => ∀c[A] x) tl ->
  Red Γ (∀c[A] e) tl'
| guard_congr :
  Red Γ s tl ->
  tl' = List.map (λ x => .guard p x b) tl ->
  Red Γ (.guard p s b) tl'

inductive ListRed : Ctx Term -> List Term -> List Term -> Prop where
| head : Red Γ h htl -> ListRed Γ (h::tl) (htl ++ tl)
| tail : ListRed Γ tl tl' -> ListRed Γ (h::tl) (h::tl')

inductive ListRedStar : Ctx Term -> List Term -> List Term -> Prop where
| refl : ListRedStar Γ x x
| step : ListRedStar Γ x y -> ListRed Γ y z -> ListRedStar Γ x z
