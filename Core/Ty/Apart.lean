import Core.Ty.Definition
import Core.Ty.Substitution
import Core.Ty.Structure

namespace Core.Ty

inductive Apart : Ty -> Ty -> Prop where
| data : x ≠ y -> Apart gt#x gt#y
| appl : Apart t s -> Apart (t • ta) (s • sa)
| appr : Apart t s -> Apart (ta • t) (sa • s)
| arrowl : Apart t s -> Apart (t -:> ta) (s -:> sa)
| arrowr : Apart t s -> Apart (ta -:> t) (sa -:> s)
| eql : Apart t s -> Apart (t ~[K]~ ta) (s ~[K]~ sa)
| eqr : Apart t s -> Apart (ta ~[K]~ t) (sa ~[K]~ s)
| eqk : K1 ≠ K2 -> Apart (ta ~[K1]~ t) (sa ~[K2]~ s)
| alli : Apart t s -> Apart (∀[K]t) (∀[K]s)
| allk : K1 ≠ K2 -> Apart (∀[K1]t) (∀[K2]s)

def apart : Ty -> Ty -> Bool
| gt#x, gt#y => x != y
| app A1 B1, app A2 B2 => apart A1 A2 || apart B1 B2
| arrow A1 B1, arrow A2 B2 => apart A1 A2 || apart B1 B2
| eq K1 A1 B1, eq K2 A2 B2 => (K1 != K2) || (K1 == K2 && apart A1 A2) || (K1 == K2 && apart B1 B2)
| all k1 t1, all k2 t2 => k1 != k2 || (k1 == k2 && apart t1 t2)
| _, _ => false


theorem Apart.reflection : Apart T S <-> apart T S
  := by
  apply Iff.intro
  · intro h
    induction h <;> simp [apart] at *
    all_goals try (assumption)
    all_goals try (case _ ih => apply Or.inl ih)
    all_goals try (case _ ih => apply Or.inr ih)
    apply Or.inl; apply Or.inl; assumption

  · intro h
    fun_induction apart <;> simp at h
    · apply data h
    · cases h
      case _ ih1 ih2 h => replace ih1 := ih1 h; apply appl ih1
      case _ ih1 ih2 h => replace ih2 := ih2 h; apply appr ih2
    · cases h
      case _ ih1 ih2 h => replace ih1 := ih1 h; apply arrowl ih1
      case _ ih1 ih2 h => replace ih2 := ih2 h; apply arrowr ih2
    · cases h
      case _ ih1 ih2 h =>
        cases h; case _ h => apply eqk h
        case _ h =>
        rcases h with ⟨e, h⟩; subst e
        replace ih1 := ih1 h
        apply eql ih1
      case _ ih1 ih2 h =>
        rcases h with ⟨e, h⟩; subst e
        replace ih2 := ih2 h
        apply eqr ih2
    · cases h
      case _ ih h => apply allk h
      case _ ih h => rcases h with ⟨e, h⟩; subst e; apply alli (ih h)


theorem apart_never_eq {T : Ty} : ¬ (Apart T T)
  := by
  intro h; induction T
  cases h
  case _ => cases h; simp at *
  all_goals try (case _ h ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h)
  case _ h ih =>
    cases h; case _ h => apply ih h
    simp at *
  case _ h ih1 ih2 =>
    cases h
    case _ h => apply ih1 h
    case _ h => apply ih2 h
    simp at *


end Core.Ty
