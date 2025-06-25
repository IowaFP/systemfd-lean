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
end Frame

namespace Ctx
  @[simp]
  def variants : Ctx T -> List FrameVariant
  | [] => []
  | .cons h t => Frame.variant h :: variants t
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
| var
| var_openm
| type
| zero
| sym
| refl
| fst
| snd
| arrowk
| appk
| appt
| app
| cast
| seq
| appc
| apptc
| choice
| all
| lamt
| lam
| arrow
| allc
| arrowc
| eq
| ite
| guard
| letterm

namespace CtorVariant

@[simp]
def is_ctor1 : CtorVariant -> Ctor1Variant -> Bool
| .sym, .sym => true
| _, _ => false

@[simp]
def is_ctor2 : CtorVariant -> Ctor2Variant -> Bool
| .refl, .refl
| .fst, .fst
| .snd, .snd
| .arrowk, .arrowk
| .appk, .appk
| .appt, .appt
| .app, .app
| .cast, .cast
| .seq, .seq
| .appc, .appc
| .apptc, .apptc
| .choice, .choice => true
| _, _ => false

@[simp]
def is_bind2 : CtorVariant -> Bind2Variant -> Bool
| .all, .all
| .lamt, .lamt
| .lam, .lam
| .arrow, .arrow
| .allc, .allc
| .arrowc, .arrowc => true
| _, _ => false

end CtorVariant

inductive ContainsVariant : List FrameVariant -> CtorVariant -> Term -> Prop where
| kind : ContainsVariant Γ .kind □
| var : ContainsVariant Γ .var (#x)
| var_openm : Γ[x]? = .some .openm -> ContainsVariant Γ .var_openm (#x)
| type : ContainsVariant Γ .type ★
| zero : ContainsVariant Γ .zero `0
| ctor1 : cv.is_ctor1 v -> ContainsVariant Γ cv (.ctor1 v t)
| ctor1_ : ContainsVariant Γ cv t -> ContainsVariant Γ cv (.ctor1 v t)
| ctor2 : cv.is_ctor2 v -> ContainsVariant Γ cv (.ctor2 v t1 t2)
| ctor2_1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.ctor2 v t1 t2)
| ctor2_2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.ctor2 v t1 t2)
| bind2 : cv.is_bind2 v -> ContainsVariant Γ cv (.bind2 v t1 t2)
| bind2_1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.bind2 v t1 t2)
| bind2_2 : ContainsVariant (bind2_frame_variant v :: Γ) cv t2 -> ContainsVariant Γ cv (.bind2 v t1 t2)
| eq : ContainsVariant Γ .eq (.eq t1 t2 t3)
| eq1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.eq t1 t2 t3)
| eq2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.eq t1 t2 t3)
| eq3 : ContainsVariant Γ cv t3 -> ContainsVariant Γ cv (.eq t1 t2 t3)
| ite : ContainsVariant Γ .ite (.ite t1 t2 t3 t4)
| ite1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| ite2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| ite3 : ContainsVariant Γ cv t3 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| ite4 : ContainsVariant Γ cv t4 -> ContainsVariant Γ cv (.ite t1 t2 t3 t4)
| guard : ContainsVariant Γ .guard (.guard t1 t2 t3)
| guard1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.guard t1 t2 t3)
| guard2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.guard t1 t2 t3)
| guard3 : ContainsVariant Γ cv t3 -> ContainsVariant Γ cv (.guard t1 t2 t3)
| letterm : ContainsVariant Γ .letterm (.letterm t1 t2 t3)
| letterm1 : ContainsVariant Γ cv t1 -> ContainsVariant Γ cv (.letterm t1 t2 t3)
| letterm2 : ContainsVariant Γ cv t2 -> ContainsVariant Γ cv (.letterm t1 t2 t3)
| letterm3 : ContainsVariant (.term :: Γ) cv t3 -> ContainsVariant Γ cv (.letterm t1 t2 t3)

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
  case kind => constructor
  case var => constructor
  case var_openm h =>
    apply ContainsVariant.var_openm
    rw [<-rh _]; apply h
  case type => constructor
  case zero => constructor
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
  case eq h => apply ContainsVariant.eq
  case eq1 ih => apply ContainsVariant.eq1 (ih r rh)
  case eq2 ih => apply ContainsVariant.eq2 (ih r rh)
  case eq3 ih => apply ContainsVariant.eq3 (ih r rh)
  case ite h => apply ContainsVariant.ite
  case ite1 ih => apply ContainsVariant.ite1 (ih r rh)
  case ite2 ih => apply ContainsVariant.ite2 (ih r rh)
  case ite3 ih => apply ContainsVariant.ite3 (ih r rh)
  case ite4 ih => apply ContainsVariant.ite4 (ih r rh)
  case guard h => apply ContainsVariant.guard
  case guard1 ih => apply ContainsVariant.guard1 (ih r rh)
  case guard2 ih => apply ContainsVariant.guard2 (ih r rh)
  case guard3 ih => apply ContainsVariant.guard3 (ih r rh)
  case letterm h => apply ContainsVariant.letterm
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
  case kind => cases h; constructor
  case var x =>
    unfold Ren.to at h; simp at h
    cases h;
    case _ => apply ContainsVariant.var
    case _ h =>
      rw [<-rh _] at h
      apply ContainsVariant.var_openm h
  case type => cases h; constructor
  case zero => cases h; constructor
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
    case eq => apply ContainsVariant.eq
    case eq1 h => apply ContainsVariant.eq1 (ih1 _ rh h)
    case eq2 h => apply ContainsVariant.eq2 (ih2 _ rh h)
    case eq3 h => apply ContainsVariant.eq3 (ih3 _ rh h)
  case ite ih1 ih2 ih3 ih4 =>
    cases h
    case ite => apply ContainsVariant.ite
    case ite1 h => apply ContainsVariant.ite1 (ih1 _ rh h)
    case ite2 h => apply ContainsVariant.ite2 (ih2 _ rh h)
    case ite3 h => apply ContainsVariant.ite3 (ih3 _ rh h)
    case ite4 h => apply ContainsVariant.ite4 (ih4 _ rh h)
  case guard ih1 ih2 ih3 =>
    cases h
    case guard => apply ContainsVariant.guard
    case guard1 h => apply ContainsVariant.guard1 (ih1 _ rh h)
    case guard2 h => apply ContainsVariant.guard2 (ih2 _ rh h)
    case guard3 h => apply ContainsVariant.guard3 (ih3 _ rh h)
  case letterm ih1 ih2 ih3 =>
    cases h
    case letterm => apply ContainsVariant.letterm
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

theorem is_openm_subst_rename_lift {Γ Δ : List FrameVariant} (A : FrameVariant) (σ : Subst Term) :
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
  simp at h; cases h
  apply Or.inl; constructor
case var x =>
  simp at h
  generalize zdef : σ x = z at *
  cases z
  case _ y =>
    cases h
    case var =>
      apply Or.inl
      apply ContainsVariant.var
    case var_openm h =>
      apply Or.inl
      apply ContainsVariant.var_openm
      rw [rh _ _ zdef]; apply h
  case _ t =>
    apply Or.inr
    apply Exists.intro x
    apply Exists.intro t
    simp at h; apply And.intro zdef h
case type =>
  simp at h; cases h
  apply Or.inl; constructor
case zero =>
  simp at h; cases h
  apply Or.inl; constructor
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
    have rh' := is_openm_subst_rename_lift (bind2_frame_variant v) σ rh; simp at rh'
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
  case eq =>
    apply Or.inl; apply ContainsVariant.eq
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
  case ite =>
    apply Or.inl; apply ContainsVariant.ite
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
  case guard =>
    apply Or.inl; apply ContainsVariant.guard
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
  case letterm =>
    apply Or.inl; apply ContainsVariant.letterm
  case letterm1 h =>
    replace ih1 := ih1 rh h
    contains_variant_from_subst_ih_case! ih1, ContainsVariant.letterm1
  case letterm2 h =>
    replace ih2 := ih2 rh h
    contains_variant_from_subst_ih_case! ih2, ContainsVariant.letterm2
  case letterm3 h =>
    replace ih3 := @ih3 (^σ) (.term :: Γ) (.term :: Δ); simp at ih3
    have rh' := is_openm_subst_rename_lift (.term) _ rh; simp at rh'
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
