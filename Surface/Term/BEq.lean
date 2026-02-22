import Surface.Ty
import Surface.Term.Definition

namespace Surface

def Term.beq : Term -> Term -> Bool
| var x, var y => x == y
| global x, global y => x == y
| appt a1 b1, appt a2 b2 => beq a1 a2 && b1 == b2
| app a1 b1, app a2 b2 => beq a1 a2 && beq b1 b2
| lamt K1 t1, lamt K2 t2 => K1 == K2 && beq t1 t2
| lam A1 t1, lam A2 t2 => A1 == A2 && beq t1 t2
| .match (n := n1) a1 b1 c1 d1, .match (n := n2) a2 b2 c2 d2 =>
  if h : n1 = n2 then
    let c : Vect n1 Bool := λ i => beq (c1 i) (c2 (by rw[h] at i; exact i))
    let p : Vect n1 Bool := λ i => beq (b1 i) (b2 (by rw[h] at i; exact i))
    beq a1 a2 && Vect.fold true (·&&·) c && Vect.fold true (·&&·) p && beq d1 d2
  else false
| _, _ => false

instance instBEq_Term : BEq Term where
  beq := Term.beq

instance instReflBEq_Term : ReflBEq Term where
  rfl := by
    intro a; induction a <;> simp [instBEq_Term, Term.beq] at *
    all_goals (repeat assumption)
    constructor; assumption; assumption
    case «match» ih1 ih2 ih3 ih4 =>
    constructor
    · constructor
      · constructor; assumption;
        unfold Vect.fold;
        case _ n _ _ _ _ =>
        induction n
        case _ => simp
        case _ n ih v1 v2 =>
        -- case _ => rfl
        -- case _ =>
        --   split; case _ h =>
        --   cases h; simp at *
        --   constructor
        --   apply ih3
          sorry
      · sorry
    · assumption

instance instLawfulBEq_Term : LawfulBEq Term where
  eq_of_beq := by
    intro a b; cases a <;> simp [instBEq_Term] at *
    all_goals (induction b <;>
      simp [Term.beq] at *)
    sorry
    sorry
    sorry
    sorry
    sorry

end Surface
