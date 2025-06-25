import SystemFD.Term
import SystemFD.Term.Definition
import SystemFD.Term.Variant
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Reduction
import SystemFD.Metatheory.Canonicity
import SystemFD.Metatheory.Progress

-- Haskell Style Statically Determined Instances (HSSDI)

-- Idea:
-- Every open method definition should look like this:
-- λ ... λ guard ... guard body
-- i.e., a preamble of lambdas followed by a preamble of guards followed by a body
-- Moreover, every guard should be relative to some constant open instance pattern

-- Every invocation of an open method should be applied to concrete instances
-- where the specified instances exist in the preamble of guards

-- For example: `eq Bool BoolEq a b` with:
-- `eq = λ t i a b. guard BoolEq i with body`
-- is HSSDI
-- Moreover, it reduces to: `body a b`

-- Claim: If a SystemFD term is HSSDI then it cannot reduce to 0

def unfold_openm (Γ : Ctx Term) : Nat -> Nat -> Term -> Term
| n + 1, x, #v =>
  if x == v then
    match (Γ d@ x) with
    | .openm _ =>
      let ιs := get_instances Γ x
      let ιs' := List.map (unfold_openm Γ n x ·) ιs
      List.foldl (·⊕·) `0 ιs'
    | _ => #v
  else #v
| n + 1, x, .ctor1 v t =>
  let t' := unfold_openm Γ (n + 1) x t
  .ctor1 v t'
| n + 1, x, .ctor2 v t1 t2 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  .ctor2 v t1' t2'
| n + 1, x, .bind2 v t1 t2 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  .bind2 v t1' t2'
| n + 1, x, .letterm t1 t2 t3 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  .letterm t1' t2' t3'
| n + 1, x, .guard t1 t2 t3 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  .guard t1' t2' t3'
| n + 1, x, .ite t1 t2 t3 t4 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  let t4' := unfold_openm Γ (n + 1) x t4
  .ite t1' t2' t3' t4'
| n + 1, x, .eq t1 t2 t3 =>
  let t1' := unfold_openm Γ (n + 1) x t1
  let t2' := unfold_openm Γ (n + 1) x t2
  let t3' := unfold_openm Γ (n + 1) x t3
  .eq t1' t2' t3'
| _ + 1, _, `0 => `0
| _ + 1, _, ★ => ★
| _ + 1, _, □ => □
| 0, _, t => t
termination_by n _ t => (n, t.size)

def elim_openm (Γ : Ctx Term) (n : Nat) : Term -> Term
| #x =>
  match (Γ d@ x) with
  | .openm _ => unfold_openm Γ n x #x
  | _ => #x
| .ctor1 v t =>
  let t' := elim_openm Γ n t
  .ctor1 v t'
| .ctor2 v t1 t2 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  .ctor2 v t1' t2'
| .bind2 v t1 t2 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  .bind2 v t1' t2'
| .letterm t1 t2 t3 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  .letterm t1' t2' t3'
| .guard t1 t2 t3 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  .guard t1' t2' t3'
| .ite t1 t2 t3 t4 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  let t4' := elim_openm Γ n t4
  .ite t1' t2' t3' t4'
| .eq t1 t2 t3 =>
  let t1' := elim_openm Γ n t1
  let t2' := elim_openm Γ n t2
  let t3' := elim_openm Γ n t3
  .eq t1' t2' t3'
| `0 => `0
| ★ => ★
| □ => □


@[simp]
abbrev HssdiCondition (Γ : Ctx Term) (t : Term) : Prop :=
  ¬ ContainsVariant Γ.variants .guard t
  ∧ ¬ ContainsVariant Γ.variants .var_openm t
  ∧ ¬ ContainsVariant Γ.variants .zero t

theorem hssdi_no_zero_preservation_step :
  HssdiCondition Γ t ->
  Red Γ t t' ->
  HssdiCondition Γ t'
:= by
intro h r; simp at h
cases h; case _ h1 h2 =>
cases h2; case _ h2 h3 =>
induction r
case beta =>
  simp; apply And.intro _; apply And.intro _ _
  case _ =>
    sorry
  case _ => sorry
  case _ =>
    sorry
case betat => sorry
case letbeta => sorry
case cast => sorry
case sym => sorry
case seq => sorry
case appc => sorry
case apptc => sorry
case fst => sorry
case snd => sorry
case allc => sorry
case arrowc => sorry
case choice1 => sorry
case choice2 => sorry
case ite_matched => sorry
case ite_missed => sorry
case guard_matched => sorry
case guard_missed => sorry
case inst => sorry
case letterm => sorry
case ctor1_congr => sorry
case ctor2_congr1 => sorry
case ctor2_congr2 => sorry
case bind2_congr1 => sorry
case bind2_congr2 => sorry
case ite_congr => sorry
case guard_congr => sorry
case ctor1_absorb => sorry
case ctor2_absorb1 => sorry
case ctor2_absorb2 => sorry
case bind2_absorb1 => sorry
case bind2_absorb2 => sorry
case ite_absorb => sorry
case guard_absorb => sorry
case ctor1_map => sorry
case ctor2_map1 => sorry
case ctor2_map2 => sorry
case bind2_map1 => sorry
case bind2_map2 => sorry
case ite_map => sorry
case guard_map => sorry

theorem hssdi_no_zero_preservation :
  HssdiCondition Γ t ->
  RedStar Γ t t' ->
  HssdiCondition Γ t'
:= by
intro h r
induction r; apply h
case _ r1 r2 ih =>
  apply hssdi_no_zero_preservation_step ih r2

theorem hssdi_no_zero_step :
  HssdiCondition Γ t ->
  ¬ Red Γ t `0
:= by
have lem : ∀ i tl, `0 = List.foldl (·⊕·) i tl -> tl = [] ∧ i = `0 := by
  intro i tl h; induction tl generalizing i
  case _ => simp at *; subst h; rfl
  case _ hd tl ih =>
    simp at *
    replace ih := ih _ h
    simp at ih
intro h r
simp at h
cases h; case _ h1 h2 =>
cases h2; case _ h2 h3 =>
  generalize sdef : `0 = s at r
  induction r
  all_goals (try simp at *)
  case beta => sorry
  case betat => sorry
  case letbeta => sorry
  case cast =>
    subst sdef; apply h3
    apply Term.Subexpr.ctor2_1
    constructor
  case choice1 =>
    apply h3; apply Term.Subexpr.ctor2_1
    constructor
  case choice2 =>
    apply h3; apply Term.Subexpr.ctor2_2
    constructor
  case ite_matched => sorry
  case ite_missed => sorry
  case guard_matched => sorry
  case guard_missed => sorry
  case letterm => sorry
  case inst h x sp tl Γ tl' h' q1 q2 q3 q4 q5 =>
    subst sdef; apply h2 _ q2
    have lem := Term.neutral_form_law q1
    subst lem
    sorry
  case ctor1_absorb => sorry
  case ctor2_absorb1 => sorry
  case ctor2_absorb2 => sorry
  case bind2_absorb1 => sorry
  case bind2_absorb2 => sorry
  case guard_absorb =>
    apply h3; apply Term.Subexpr.guard2
    constructor
  case ite_absorb => sorry

theorem syntactic_guarantee_of_reduction_to_zero_impossible :
  HssdiCondition Γ t ->
  ¬ RedStar Γ t `0
:= by
intro h r
generalize sdef : `0 = s at r
induction r
case refl =>
  subst sdef; simp at h
  apply h.2.2
  constructor
case step y z r1 r2 ih =>
  subst sdef
  have lem := hssdi_no_zero_preservation h r1
  apply hssdi_no_zero_step lem r2
