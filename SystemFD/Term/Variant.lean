import SystemFD.Ctx
import SystemFD.Term.Definition
import SystemFD.Term.Substitution
import SystemFD.Reduction

inductive FrameVariant where
| empty
| kind
| type
| datatype
| ctor
| opent
| openm
| insttype
| inst
| term

namespace FrameVariant

  @[simp]
  def beq : FrameVariant -> FrameVariant -> Bool
  | .empty, .empty => true
  | .kind, .kind => true
  | .type, .type => true
  | .datatype, .datatype => true
  | .ctor, .ctor => true
  | .opent, .opent => true
  | .openm, .openm => true
  | .insttype, .insttype => true
  | .inst, .inst => true
  | .term, .term => true
  | _, _ => false
end FrameVariant

@[simp]
instance instBEq_FrameVariant : BEq FrameVariant where
  beq := FrameVariant.beq

instance instLawfulBEq_FrameVariant : LawfulBEq FrameVariant where
  eq_of_beq := by {
    intro a b h; simp at h
    cases a; all_goals (
        cases b <;> simp at *
    )
  }
  rfl := by intro a; cases a <;> simp

namespace Frame
  def variant : Frame T -> FrameVariant
  | .empty => .empty
  | .kind _ => .kind
  | .type _ => .type
  | .datatype _ => .datatype
  | .ctor _ => .ctor
  | .opent _ => .opent
  | .openm _ => .openm
  | .insttype _ => .insttype
  | .inst _ _ => .inst
  | .term _ _ => .term

  theorem variant_invariant_under_subst [SubstitutionType T] {f : Frame T} :
    (f.apply σ).variant = f.variant
  := by
  unfold Frame.variant; unfold Frame.apply
  cases f <;> simp
end Frame

namespace Ctx
  @[simp]
  def variants : Ctx T -> List FrameVariant
  | [] => []
  | .cons h t => Frame.variant h :: variants t

  theorem variant_is_sound [SubstitutionType T] {Γ : Ctx T} :
    Γ d@ x = f -> f ≠ .empty -> Γ.variants[x]? = .some f.variant
  := by
  intro h1 h2
  induction Γ generalizing x f; simp at *
  case _ => apply h2; rw [h1]
  case _ hd tl ih =>
    cases x <;> simp at *
    case _ =>
      subst h1; rw [Frame.variant_invariant_under_subst]
    case _ x =>
      subst h1; rw [Frame.variant_invariant_under_subst]
      apply ih; intro h; rw [h] at h2
      unfold Frame.apply at h2; simp at h2

  theorem variant_is_openm [SubstitutionType T] {Γ : Ctx T} :
    (Γ d@ x).is_openm -> Γ.variants[x]? = .some .openm
  := by
  intro h
  induction Γ generalizing x; simp at *
  case _ =>
    unfold Frame.is_openm at h; simp at h
  case _ hd tl ih =>
    cases x <;> simp at *
    case _ =>
      rw [<-Frame.is_openm_apply] at h
      unfold Frame.is_openm at h
      cases hd <;> simp at h
      unfold Frame.variant; simp
    case _ x =>
      rw [<-Frame.is_openm_apply] at h
      apply ih h
end Ctx

def bind2_frame_variant : Bind2Variant -> FrameVariant
| .all => .kind
| .lamt => .kind
| .lam => .type
| .arrow => .empty
| .allc => .kind
| .arrowc => .empty

inductive CtorVariant where
| kind
| var (f : FrameVariant)
| type
| zero
| ctor1 (v : Ctor1Variant)
| ctor2 (v : Ctor2Variant)
| bind2 (v : Bind2Variant)
| eq
| ite
| guard
| letterm

namespace CtorVariant
  def is_spine_variant : CtorVariant -> SpineVariant -> Bool
  | .ctor2 .app, .term => true
  | .ctor2 .appt, .type => true
  | .ctor2 .appk, .kind => true
  | _, _ => false

  @[simp]
  def is_ctor1 : CtorVariant -> Ctor1Variant -> Bool
  | .ctor1 .sym, .sym => true
  | _, _ => false

  @[simp]
  def is_ctor2 : CtorVariant -> Ctor2Variant -> Bool
  | .ctor2 .refl, .refl
  | .ctor2 .fst, .fst
  | .ctor2 .snd, .snd
  | .ctor2 .arrowk, .arrowk
  | .ctor2 .appk, .appk
  | .ctor2 .appt, .appt
  | .ctor2 .app, .app
  | .ctor2 .cast, .cast
  | .ctor2 .seq, .seq
  | .ctor2 .appc, .appc
  | .ctor2 .apptc, .apptc
  | .ctor2 .choice, .choice => true
  | _, _ => false

  @[simp]
  def is_bind2 : CtorVariant -> Bind2Variant -> Bool
  | .bind2 .all, .all
  | .bind2 .lamt, .lamt
  | .bind2 .lam, .lam
  | .bind2 .arrow, .arrow
  | .bind2 .allc, .allc
  | .bind2 .arrowc, .arrowc => true
  | _, _ => false

  @[simp]
  def beq : CtorVariant -> CtorVariant -> Bool
  | .kind, .kind => true
  | .var f1, .var f2 => f1 == f2
  | .type, .type => true
  | .zero, .zero => true
  | .ctor1 v1, .ctor1 v2 => v1 == v2
  | .ctor2 v1, .ctor2 v2 => v1 == v2
  | .bind2 v1, .bind2 v2 => v1 == v2
  | .eq, .eq => true
  | .ite, .ite => true
  | .guard, .guard => true
  | .letterm, .letterm => true
  | _, _ => false

end CtorVariant

@[simp]
instance instBEq_CtorVariant : BEq CtorVariant where
  beq := CtorVariant.beq

instance instLawfulBEq_CtorVariant : LawfulBEq CtorVariant where
  eq_of_beq := by {
    intro a b h
    cases a <;> cases b
    case var.var f' f =>
      unfold BEq.beq at h
      unfold instBEq_CtorVariant at h
      unfold CtorVariant.beq at h
      have lem : f' == f := by rw [<-h]
      replace lem := eq_of_beq lem
      subst lem; rfl
    case ctor2.ctor2 v' v =>
      unfold BEq.beq at h
      unfold instBEq_CtorVariant at h
      unfold CtorVariant.beq at h
      have lem : v' == v := by rw [<-h]
      replace lem := eq_of_beq lem
      subst lem; rfl
    case bind2.bind2 v' v =>
      unfold BEq.beq at h
      unfold instBEq_CtorVariant at h
      unfold CtorVariant.beq at h
      have lem : v' == v := by rw [<-h]
      replace lem := eq_of_beq lem
      subst lem; rfl
    all_goals (simp at h; try rfl)
  }
  rfl := by intro a; cases a <;> simp

@[simp]
def contains_variant (Γ : List FrameVariant) (cv : List CtorVariant) : Term -> Bool
| .kind => List.contains cv .kind
| .var x =>
  match Γ[x]? with
  | .some f => List.contains cv (.var f)
  | .none => false
| .type => List.contains cv .type
| .zero => List.contains cv .zero
| .ctor1 v t => List.any cv (·.is_ctor1 v)
  || contains_variant Γ cv t
| .ctor2 v t1 t2 => List.any cv (·.is_ctor2 v)
  || contains_variant Γ cv t1
  || contains_variant Γ cv t2
| .bind2 v t1 t2 => List.any cv (·.is_bind2 v)
  || contains_variant Γ cv t1
  || contains_variant (bind2_frame_variant v :: Γ) cv t2
| .eq t1 t2 t3 => List.contains cv .eq
  || contains_variant Γ cv t1
  || contains_variant Γ cv t2
  || contains_variant Γ cv t3
| .ite t1 t2 t3 t4 => List.contains cv .ite
  || contains_variant Γ cv t1
  || contains_variant Γ cv t2
  || contains_variant Γ cv t3
  || contains_variant Γ cv t4
| .guard t1 t2 t3 => List.contains cv .guard
  || contains_variant Γ cv t1
  || contains_variant Γ cv t2
  || contains_variant Γ cv t3
| .letterm t1 t2 t3 => List.contains cv .letterm
  || contains_variant Γ cv t1
  || contains_variant Γ cv t2
  || contains_variant (.term :: Γ) cv t3

inductive ContainsVariant : List FrameVariant -> List CtorVariant -> Term -> Prop where
| kind : .kind ∈ cv -> ContainsVariant Γ cv □
| var : .var f ∈ cv -> Γ[x]? = .some f -> ContainsVariant Γ cv (#x)
| type : .type ∈ cv -> ContainsVariant Γ cv ★
| zero : .zero ∈ cv -> ContainsVariant Γ cv `0
| ctor1 : List.any cv (·.is_ctor1 v) -> ContainsVariant Γ cv (.ctor1 v t)
| ctor1_ : ContainsVariant Γ cv t -> ContainsVariant Γ cv (.ctor1 v t)
| ctor2 : List.any cv (·.is_ctor2 v) -> ContainsVariant Γ cv (.ctor2 v t1 t2)
| ctor2_1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.ctor2 v t1 t2)
| ctor2_2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.ctor2 v t1 t2)
| bind2 : List.any cv (·.is_bind2 v) -> ContainsVariant Γ cv (.bind2 v t1 t2)
| bind2_1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.bind2 v t1 t2)
| bind2_2 : ContainsVariant (bind2_frame_variant v :: Γ) cv t2 -> ContainsVariant Γ cv (.bind2 v t1 t2)
| eq : .eq ∈ cv -> ContainsVariant Γ cv (.eq t1 t2 t3)
| eq1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.eq t1 t2 t3)
| eq2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.eq t1 t2 t3)
| eq3 : ContainsVariant Γ cv t3 -> ContainsVariant Γ cv (.eq t1 t2 t3)
| ite : .ite ∈ cv -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| ite1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| ite2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| ite3 : ContainsVariant Γ cv t3 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| ite4 : ContainsVariant Γ cv t4 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| guard : .guard ∈ cv -> ContainsVariant Γ cv (.guard t1 t2 t3)
| guard1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.guard t1 t2 t3)
| guard2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.guard t1 t2 t3)
| guard3 : ContainsVariant Γ cv t3 -> ContainsVariant Γ cv (.guard t1 t2 t3)
| letterm : .letterm ∈ cv -> ContainsVariant Γ cv (.letterm t1 t2 t3)
| letterm1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.letterm t1 t2 t3)
| letterm2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.letterm t1 t2 t3)
| letterm3 : ContainsVariant (.term :: Γ) cv t3 -> ContainsVariant Γ cv (.letterm t1 t2 t3)

theorem contains_variant_reflection :
  ContainsVariant Γ cv t <-> contains_variant Γ cv t
:= by
apply Iff.intro
case mp =>
  intro h
  induction h
  all_goals simp at *; simp [*]
case mpr =>
  intro h
  induction Γ, t using contains_variant.induct <;> simp at h
  case _ => apply ContainsVariant.kind h
  case _ xh =>
    rw [xh] at h; simp at h
    apply ContainsVariant.var h xh
  case _ xh => rw [xh] at h; simp at h
  case _ => apply ContainsVariant.type h
  case _ => apply ContainsVariant.zero h
  case _ ih =>
    cases h
    case _ h => apply ContainsVariant.ctor1; simp; apply h
    case _ h => apply ContainsVariant.ctor1_ (ih h)
  case _ ih1 ih2 =>
    cases h
    case _ h =>
      cases h
      case _ h =>
        apply ContainsVariant.ctor2; simp
        apply h
      case _ h =>
        replace ih1 := ih1 h
        apply ContainsVariant.ctor2_1 ih1
    case _ h =>
      replace ih2 := ih2 h
      apply ContainsVariant.ctor2_2 ih2
  case _ ih1 ih2 =>
    cases h
    case _ h =>
      cases h
      case _ h =>
        apply ContainsVariant.bind2; simp
        apply h
      case _ h =>
        replace ih1 := ih1 h
        apply ContainsVariant.bind2_1 ih1
    case _ h =>
      replace ih2 := ih2 h
      apply ContainsVariant.bind2_2 ih2
  case _ ih1 ih2 ih3 =>
    cases h
    case _ h =>
      cases h
      case _ h =>
        cases h
        case _ h => apply ContainsVariant.eq h
        case _ h =>
          replace ih1 := ih1 h
          apply ContainsVariant.eq1 ih1
      case _ h =>
        replace ih2 := ih2 h
        apply ContainsVariant.eq2 ih2
    case _ h =>
      replace ih3 := ih3 h
      apply ContainsVariant.eq3 ih3
  case _ ih1 ih2 ih3 ih4 =>
    cases h
    case _ h =>
      cases h
      case _ h =>
        cases h
        case _ h =>
          cases h
          case _ h => apply ContainsVariant.ite h
          case _ h =>
            replace ih1 := ih1 h
            apply ContainsVariant.ite1 ih1
        case _ h =>
          replace ih2 := ih2 h
          apply ContainsVariant.ite2 ih2
      case _ h =>
        replace ih3 := ih3 h
        apply ContainsVariant.ite3 ih3
    case _ h =>
      replace ih4 := ih4 h
      apply ContainsVariant.ite4 ih4
  case _ ih1 ih2 ih3 =>
    cases h
    case _ h =>
      cases h
      case _ h =>
        cases h
        case _ h => apply ContainsVariant.guard h
        case _ h =>
          replace ih1 := ih1 h
          apply ContainsVariant.guard1 ih1
      case _ h =>
        replace ih2 := ih2 h
        apply ContainsVariant.guard2 ih2
    case _ h =>
      replace ih3 := ih3 h
      apply ContainsVariant.guard3 ih3
  case _ ih1 ih2 ih3 =>
    cases h
    case _ h =>
      cases h
      case _ h =>
        cases h
        case _ h => apply ContainsVariant.letterm h
        case _ h =>
          replace ih1 := ih1 h
          apply ContainsVariant.letterm1 ih1
      case _ h =>
        replace ih2 := ih2 h
        apply ContainsVariant.letterm2 ih2
    case _ h =>
      replace ih3 := ih3 h
      apply ContainsVariant.letterm3 ih3

theorem not_contains_variant_ctor1 :
  ¬ ContainsVariant Γ cv (.ctor1 v t) -> ¬ ContainsVariant Γ cv t
:= by
intro h1 h2
apply h1; apply ContainsVariant.ctor1_ h2

theorem not_contains_variant_ctor2 :
  ¬ ContainsVariant Γ cv (.ctor2 v t1 t2) ->
  ¬ ContainsVariant Γ cv t1 ∧ ¬ ContainsVariant Γ cv t2
:= by
intro h1; apply And.intro
intro h2; apply h1; apply ContainsVariant.ctor2_1 h2
intro h2; apply h1; apply ContainsVariant.ctor2_2 h2

theorem not_contains_variant_bind2 :
  ¬ ContainsVariant Γ cv (.bind2 v t1 t2) ->
  ¬ ContainsVariant Γ cv t1 ∧ ¬ ContainsVariant (bind2_frame_variant v :: Γ) cv t2
:= by
intro h1; apply And.intro
intro h2; apply h1; apply ContainsVariant.bind2_1 h2
intro h2; apply h1; apply ContainsVariant.bind2_2 h2

theorem not_contains_variant_eq :
  ¬ ContainsVariant Γ cv (.eq t1 t2 t3) ->
  ¬ ContainsVariant Γ cv t1 ∧ ¬ ContainsVariant Γ cv t2 ∧ ¬ ContainsVariant Γ cv t3
:= by
intro h1; apply And.intro _; apply And.intro
intro h2; apply h1; apply ContainsVariant.eq2 h2
intro h2; apply h1; apply ContainsVariant.eq3 h2
intro h2; apply h1; apply ContainsVariant.eq1 h2

theorem not_contains_variant_ite :
  ¬ ContainsVariant Γ cv (.ite t1 t2 t3 t4) ->
  ¬ ContainsVariant Γ cv t1 ∧ ¬ ContainsVariant Γ cv t2
   ∧ ¬ ContainsVariant Γ cv t3 ∧ ¬ ContainsVariant Γ cv t4
:= by
intro h1; apply And.intro _; apply And.intro _; apply And.intro
intro h2; apply h1; apply ContainsVariant.ite3 h2
intro h2; apply h1; apply ContainsVariant.ite4 h2
intro h2; apply h1; apply ContainsVariant.ite2 h2
intro h2; apply h1; apply ContainsVariant.ite1 h2

theorem not_contains_variant_guard :
  ¬ ContainsVariant Γ cv (.guard t1 t2 t3) ->
  ¬ ContainsVariant Γ cv t1 ∧ ¬ ContainsVariant Γ cv t2 ∧ ¬ ContainsVariant Γ cv t3
:= by
intro h1; apply And.intro _; apply And.intro
intro h2; apply h1; apply ContainsVariant.guard2 h2
intro h2; apply h1; apply ContainsVariant.guard3 h2
intro h2; apply h1; apply ContainsVariant.guard1 h2

theorem not_contains_variant_letterm :
  ¬ ContainsVariant Γ cv (.letterm t1 t2 t3) ->
  ¬ ContainsVariant Γ cv t1 ∧ ¬ ContainsVariant Γ cv t2 ∧ ¬ ContainsVariant (.term :: Γ) cv t3
:= by
intro h1; apply And.intro _; apply And.intro
intro h2; apply h1; apply ContainsVariant.letterm2 h2
intro h2; apply h1; apply ContainsVariant.letterm3 h2
intro h2; apply h1; apply ContainsVariant.letterm1 h2

macro "not_contains_variant_spine_variant_case!" h1:term "," ih:term : tactic => `(tactic| {
  replace ih := $ih $h1
  cases ih; case _ ih1 ih2 =>
  replace ih1 := not_contains_variant_ctor2 ih1
  apply And.intro ih1.1
  intro t th h2; simp at th
  cases th
  case _ th => subst th; simp at h2; apply ih1.2 h2
  case _ th => apply ih2 t th h2
})

theorem not_contains_variant_spine :
  ¬ ContainsVariant Γ cv (h.apply_spine sp) ->
  ¬ ContainsVariant Γ cv h ∧ (∀ t ∈ sp, ¬ ContainsVariant Γ cv t.2)
:= by
intro h1
induction sp generalizing h
case _ => simp at *; apply h1
case _ hd tl ih =>
  cases hd; case _ sv z =>
  cases sv <;> not_contains_variant_spine_variant_case! h1, ih

macro "contains_variant_spine_sv_case!" q:Lean.Parser.Tactic.elimTarget "," ih:term "," t:term : tactic => `(tactic| {
  replace ih := @$ih $t
  apply ih
  cases $q
  case _ q =>
    apply Or.inl
    apply ContainsVariant.ctor2_1 q
  case _ q =>
    cases q
    case _ q =>
      cases q
      case _ q =>
        apply Or.inl
        cases q; case _ x q =>
        apply ContainsVariant.ctor2; simp
        apply Exists.intro x
        apply And.intro q.1
        unfold CtorVariant.is_spine_variant at q
        cases x <;> simp at *
        case _ v => cases v <;> simp at *
      case _ q =>
        apply Or.inl
        apply ContainsVariant.ctor2_2 q
    case _ q => apply Or.inr q
})

theorem contains_variant_spine :
  ContainsVariant Γ cv (h.apply_spine sp) <->
  ContainsVariant Γ cv h ∨ (∃ t ∈ sp, List.any cv (·.is_spine_variant t.1) ∨ ContainsVariant Γ cv t.2)
:= by
apply Iff.intro
case mp =>
  intro q
  induction sp generalizing h <;> simp at *
  case _ => apply q
  case _ hd tl ih =>
    cases hd; case _ sv t =>
    cases sv; all_goals (
      simp at *
      replace ih := ih q
      cases ih
      case _ ih =>
        cases ih
        case _ ih =>
          apply Or.inr; apply Or.inl
          apply Or.inl; simp at ih
          cases ih; case _ x ih =>
          cases ih; case _ ih1 ih2 =>
          apply Exists.intro x
          apply And.intro ih1
          cases x <;> try simp at *
          all_goals (
            unfold CtorVariant.is_spine_variant
            case _ v => cases v <;> simp at *
          )
        case _ ih => apply Or.inl; apply ih
        case _ ih =>
          apply Or.inr; apply Or.inl
          apply Or.inr ih
      case _ ih =>
        cases ih; case _ sv ih =>
        cases ih; case _ a ih =>
        cases ih; case _ q2 ih =>
        cases ih
        case _ ih =>
          apply Or.inr; apply Or.inr
          apply Exists.intro sv
          apply Exists.intro a
          apply And.intro q2
          apply Or.inl ih
        case _ ih =>
          apply Or.inr; apply Or.inr
          apply Exists.intro sv
          apply Exists.intro a
          apply And.intro q2
          apply Or.inr ih
    )
case mpr =>
  intro q; induction sp generalizing h <;> simp at *
  case _ => apply q
  case _ hd tl ih =>
    cases hd; case _ sv a =>
    cases sv <;> simp at *
    case _ => contains_variant_spine_sv_case! q, ih, (h `@ a)
    case _ => contains_variant_spine_sv_case! q, ih, (h `@t a)
    case _ => contains_variant_spine_sv_case! q, ih, (h `@k a)

theorem is_openm_rename_lift {Γ Δ : List FrameVariant} (A : FrameVariant) (r : Ren) :
  (∀ x, Γ[x]? = Δ[r x]?) ->
  (∀ x, (A :: Γ)[x]? = (A :: Δ)[r.lift x]?)
:= by
intro h x
unfold Ren.lift
cases x <;> simp at *
case _ x => rw [h x]

theorem contains_variant_rename (r : Ren) :
  (∀ x, Γ[x]? = Δ[r x]?) ->
  (ContainsVariant Γ v b <-> ContainsVariant Δ v ([r.to]b))
:= by
intro rh
apply Iff.intro
case _ =>
  intro h
  induction h generalizing r Δ <;> simp
  case kind h => apply ContainsVariant.kind h
  case var h1 h2 =>
    apply ContainsVariant.var h1
    rw [<-rh _]; apply h2
  case type h => apply ContainsVariant.type h
  case zero h => apply ContainsVariant.zero h
  case ctor1 h => apply ContainsVariant.ctor1 h
  case ctor1_ ih => apply ContainsVariant.ctor1_ (ih r rh)
  case ctor2 h => apply ContainsVariant.ctor2 h
  case ctor2_1 ih => apply ContainsVariant.ctor2_1 (ih r rh)
  case ctor2_2 ih => apply ContainsVariant.ctor2_2 (ih r rh)
  case bind2 h => apply ContainsVariant.bind2 h
  case bind2_1 ih => apply ContainsVariant.bind2_1 (ih r rh)
  case bind2_2 v _ _ _ _ _ ih =>
    replace ih := ih (r.lift) (is_openm_rename_lift (bind2_frame_variant v) r rh)
    rw [Subst.lift_lemma] at ih; simp at ih
    apply ContainsVariant.bind2_2 ih
  case eq h => apply ContainsVariant.eq h
  case eq1 ih => apply ContainsVariant.eq1 (ih r rh)
  case eq2 ih => apply ContainsVariant.eq2 (ih r rh)
  case eq3 ih => apply ContainsVariant.eq3 (ih r rh)
  case ite h => apply ContainsVariant.ite h
  case ite1 ih => apply ContainsVariant.ite1 (ih r rh)
  case ite2 ih => apply ContainsVariant.ite2 (ih r rh)
  case ite3 ih => apply ContainsVariant.ite3 (ih r rh)
  case ite4 ih => apply ContainsVariant.ite4 (ih r rh)
  case guard h => apply ContainsVariant.guard h
  case guard1 ih => apply ContainsVariant.guard1 (ih r rh)
  case guard2 ih => apply ContainsVariant.guard2 (ih r rh)
  case guard3 ih => apply ContainsVariant.guard3 (ih r rh)
  case letterm h => apply ContainsVariant.letterm h
  case letterm1 ih => apply ContainsVariant.letterm1 (ih r rh)
  case letterm2 ih => apply ContainsVariant.letterm2 (ih r rh)
  case letterm3 ih =>
    replace ih := ih (r.lift) (is_openm_rename_lift .term r rh)
    rw [Subst.lift_lemma] at ih; simp at ih
    apply ContainsVariant.letterm3 ih
case _ =>
  intro h
  induction b generalizing r Γ Δ
  all_goals simp at h
  case kind => cases h; case _ h => apply ContainsVariant.kind h
  case var x =>
    unfold Ren.to at h; simp at h
    cases h;
    case _ h1 h2 =>
      rw [<-rh _] at h2
      apply ContainsVariant.var h1 h2
  case type => cases h; case _ h => apply ContainsVariant.type h
  case zero => cases h; case _ h => apply ContainsVariant.zero h
  case ctor1 ih =>
    cases h
    case ctor1 h => apply ContainsVariant.ctor1 h
    case ctor1_ h => apply ContainsVariant.ctor1_ (ih _ rh h)
  case ctor2 ih1 ih2 =>
    cases h
    case ctor2 h => apply ContainsVariant.ctor2 h
    case ctor2_1 h => apply ContainsVariant.ctor2_1 (ih1 _ rh h)
    case ctor2_2 h => apply ContainsVariant.ctor2_2 (ih2 _ rh h)
  case bind2 ih1 ih2 =>
    cases h
    case bind2 h => apply ContainsVariant.bind2 h
    case bind2_1 h => apply ContainsVariant.bind2_1 (ih1 _ rh h)
    case bind2_2 v _ _ h =>
      replace ih2 := @ih2
        (bind2_frame_variant v :: Γ)
        (bind2_frame_variant v :: Δ)
        (r.lift)
        (is_openm_rename_lift (bind2_frame_variant v) r rh)
      rw [Subst.lift_lemma] at ih2; simp at ih2
      replace ih2 := ih2 h
      apply ContainsVariant.bind2_2 ih2
  case eq ih1 ih2 ih3 =>
    cases h
    case eq h => apply ContainsVariant.eq h
    case eq1 h => apply ContainsVariant.eq1 (ih1 _ rh h)
    case eq2 h => apply ContainsVariant.eq2 (ih2 _ rh h)
    case eq3 h => apply ContainsVariant.eq3 (ih3 _ rh h)
  case ite ih1 ih2 ih3 ih4 =>
    cases h
    case ite h => apply ContainsVariant.ite h
    case ite1 h => apply ContainsVariant.ite1 (ih1 _ rh h)
    case ite2 h => apply ContainsVariant.ite2 (ih2 _ rh h)
    case ite3 h => apply ContainsVariant.ite3 (ih3 _ rh h)
    case ite4 h => apply ContainsVariant.ite4 (ih4 _ rh h)
  case guard ih1 ih2 ih3 =>
    cases h
    case guard h => apply ContainsVariant.guard h
    case guard1 h => apply ContainsVariant.guard1 (ih1 _ rh h)
    case guard2 h => apply ContainsVariant.guard2 (ih2 _ rh h)
    case guard3 h => apply ContainsVariant.guard3 (ih3 _ rh h)
  case letterm ih1 ih2 ih3 =>
    cases h
    case letterm h => apply ContainsVariant.letterm h
    case letterm1 h => apply ContainsVariant.letterm1 (ih1 _ rh h)
    case letterm2 h => apply ContainsVariant.letterm2 (ih2 _ rh h)
    case letterm3 h =>
      replace ih3 := @ih3
        (.term :: Γ)
        (.term :: Δ)
        (r.lift)
        (is_openm_rename_lift (.term) r rh)
      rw [Subst.lift_lemma] at ih3; simp at ih3
      replace ih3 := ih3 h
      apply ContainsVariant.letterm3 ih3

macro "contains_variant_from_subst_ih_case!" ih:Lean.Parser.Tactic.elimTarget "," ctor:term : tactic => `(tactic| {
  cases $ih
  case _ ih1 =>
    apply Or.inl
    apply $ctor ih1
  case _ ih1 =>
    cases ih1; case _ i ih1 =>
    cases ih1; case _ t ih1 =>
    apply Or.inr
    apply Exists.intro i
    apply Exists.intro t
    apply ih1
})

theorem variant_subst_rename_lift {Γ Δ : List FrameVariant} (A : FrameVariant) (σ : Subst Term) :
  (∀ x y, σ x = .re y -> Γ[x]? = Δ[y]?) ->
  (∀ x y, ^σ x = .re y -> (A :: Γ)[x]? = (A :: Δ)[y]?)
:= by
intro h1 x y h2
cases x <;> simp at *
case _ => subst h2; simp
case _ x =>
  unfold Subst.compose at h2; simp at h2
  generalize zdef : σ x = z at *
  cases z <;> simp at *
  case _ j =>
    subst h2; simp
    rw [h1 _ _ zdef]

theorem contains_variant_from_subst :
  (∀ x y, σ x = .re y -> Γ[x]? = Δ[y]?) ->
  ContainsVariant Δ v ([σ]b) ->
    ContainsVariant Γ v b
    ∨ (∃ i, ∃ t, σ i = .su t ∧ ContainsVariant Δ v t)
:= by
intro rh h
induction b generalizing σ Γ Δ
case kind =>
  simp at h; cases h; case _ h =>
  apply Or.inl; apply ContainsVariant.kind h
case var x =>
  simp at h
  generalize zdef : σ x = z at *
  cases z
  case _ y =>
    cases h
    case var h1 h2 =>
      apply Or.inl
      apply ContainsVariant.var h1
      rw [rh _ _ zdef]; apply h2
  case _ t =>
    apply Or.inr
    apply Exists.intro x
    apply Exists.intro t
    simp at h; apply And.intro zdef h
case type =>
  simp at h; cases h; case _ h =>
  apply Or.inl; apply ContainsVariant.type h
case zero =>
  simp at h; cases h; case _ h =>
  apply Or.inl; apply ContainsVariant.zero h
case ctor1 ih =>
  simp at *; cases h
  case ctor1 h =>
    apply Or.inl; apply ContainsVariant.ctor1 h
  case ctor1_ h =>
    replace ih := ih rh h
    contains_variant_from_subst_ih_case! ih, ContainsVariant.ctor1_
case ctor2 ih1 ih2 =>
  simp at *; cases h
  case ctor2 h =>
    apply Or.inl; apply ContainsVariant.ctor2 h
  case ctor2_1 h =>
    replace ih1 := ih1 rh h
    contains_variant_from_subst_ih_case! ih1, ContainsVariant.ctor2_1
  case ctor2_2 h =>
    replace ih2 := ih2 rh h
    contains_variant_from_subst_ih_case! ih2, ContainsVariant.ctor2_2
case bind2 ih1 ih2 =>
  simp at *
  cases h
  case bind2 h =>
    apply Or.inl; apply ContainsVariant.bind2 h
  case bind2_1 h =>
    replace ih1 := ih1 rh h
    contains_variant_from_subst_ih_case! ih1, ContainsVariant.bind2_1
  case bind2_2 v t1 t2 h =>
    replace ih2 := @ih2 (^σ) (bind2_frame_variant v :: Γ) (bind2_frame_variant v :: Δ); simp at ih2
    have rh' := variant_subst_rename_lift (bind2_frame_variant v) σ rh; simp at rh'
    replace ih2 := ih2 rh' h
    cases ih2
    case _ ih2 =>
      apply Or.inl
      apply ContainsVariant.bind2_2 ih2
    case _ ih2 =>
      cases ih2; case _ i ih2 =>
      cases ih2; case _ t ih2 =>
      apply Or.inr; simp at ih2
      cases i <;> simp at *
      case _ i =>
        unfold Subst.compose at ih2; simp at ih2
        generalize zdef : σ i = z at ih2
        cases z <;> simp at *
        case _ t' =>
          cases ih2; case _ e ih2 =>
          subst e; apply Exists.intro i
          apply Exists.intro t'
          apply And.intro zdef
          apply (contains_variant_rename _ _).2 ih2
          simp
case eq ih1 ih2 ih3 =>
  simp at *; cases h
  case eq h =>
    apply Or.inl; apply ContainsVariant.eq h
  case eq1 h =>
    replace ih1 := ih1 rh h
    contains_variant_from_subst_ih_case! ih1, ContainsVariant.eq1
  case eq2 h =>
    replace ih2 := ih2 rh h
    contains_variant_from_subst_ih_case! ih2, ContainsVariant.eq2
  case eq3 h =>
    replace ih3 := ih3 rh h
    contains_variant_from_subst_ih_case! ih3, ContainsVariant.eq3
case ite ih1 ih2 ih3 ih4 =>
  simp at *; cases h
  case ite h =>
    apply Or.inl; apply ContainsVariant.ite h
  case ite1 h =>
    replace ih1 := ih1 rh h
    contains_variant_from_subst_ih_case! ih1, ContainsVariant.ite1
  case ite2 h =>
    replace ih2 := ih2 rh h
    contains_variant_from_subst_ih_case! ih2, ContainsVariant.ite2
  case ite3 h =>
    replace ih3 := ih3 rh h
    contains_variant_from_subst_ih_case! ih3, ContainsVariant.ite3
  case ite4 h =>
    replace ih4 := ih4 rh h
    contains_variant_from_subst_ih_case! ih4, ContainsVariant.ite4
case guard ih1 ih2 ih3 =>
  simp at *; cases h
  case guard h =>
    apply Or.inl; apply ContainsVariant.guard h
  case guard1 h =>
    replace ih1 := ih1 rh h
    contains_variant_from_subst_ih_case! ih1, ContainsVariant.guard1
  case guard2 h =>
    replace ih2 := ih2 rh h
    contains_variant_from_subst_ih_case! ih2, ContainsVariant.guard2
  case guard3 h =>
    replace ih3 := ih3 rh h
    contains_variant_from_subst_ih_case! ih3, ContainsVariant.guard3
case letterm ih1 ih2 ih3 =>
  simp at *; cases h
  case letterm h =>
    apply Or.inl; apply ContainsVariant.letterm h
  case letterm1 h =>
    replace ih1 := ih1 rh h
    contains_variant_from_subst_ih_case! ih1, ContainsVariant.letterm1
  case letterm2 h =>
    replace ih2 := ih2 rh h
    contains_variant_from_subst_ih_case! ih2, ContainsVariant.letterm2
  case letterm3 h =>
    replace ih3 := @ih3 (^σ) (.term :: Γ) (.term :: Δ); simp at ih3
    have rh' := variant_subst_rename_lift (.term) _ rh; simp at rh'
    replace ih3 := ih3 rh' h
    cases ih3
    case _ ih3 =>
      apply Or.inl
      apply ContainsVariant.letterm3 ih3
    case _ ih3 =>
      cases ih3; case _ i ih3 =>
      cases ih3; case _ t ih3 =>
      apply Or.inr; simp at ih3
      cases i <;> simp at *
      case _ i =>
        unfold Subst.compose at ih3; simp at ih3
        generalize zdef : σ i = z at ih3
        cases z <;> simp at *
        case _ t' =>
          cases ih3; case _ e ih3 =>
          subst e; apply Exists.intro i
          apply Exists.intro t'
          apply And.intro zdef
          apply (contains_variant_rename _ _).2 ih3
          simp

theorem contains_variant_from_beta f :
  ContainsVariant Γ v (b β[t]) -> ContainsVariant (f :: Γ) v b ∨ ContainsVariant Γ v t
:= by
intro h
have lem := @contains_variant_from_subst (.su t :: I) (f :: Γ) Γ v b (by {
  intro x y q
  cases x <;> simp at *
  case _ x =>
    subst q; rfl
})
replace lem := lem h
cases lem
case _ lem => apply Or.inl lem
case _ lem =>
  cases lem; case _ i lem =>
  cases lem; case _ t' lem =>
  cases i <;> simp at *
  rw [lem.1]; apply Or.inr lem.2
