
import Surface.Term.Definition

open Lilac

namespace Surface

def Term.beq : Term -> Term -> Bool
| var x, var y => x == y
| global (p := p1) (m := m1) (n := n1) x τ1a τ1b as1, global (p := p2) (m := m2) (n := n2) y τ2a τ2b as2 =>
  if h : p1 == p2 && m1 = m2 && n1 == n2 then
    let as : Fun.Vec Bool p1 := λ i => beq (as1 i) (as2 (by simp at h; rw[h.1.1] at i; exact i))
    x == y && Vec.beq τ1a τ2a && Vec.beq τ1b τ2b && as.to.foldl (·&&·) true
  else false
| appt a1 b1 c1, appt a2 b2 c2 => beq a1 a2 && b1 == b2 && c1 == c2
| app a1 b1 τ1, app a2 b2 τ2 => beq a1 a2 && beq b1 b2 && τ1 == τ2
| lamt K1 t1, lamt K2 t2 => K1 == K2 && beq t1 t2
| lam A1 t1, lam A2 t2 => A1 == A2 && beq t1 t2
| .mtch m1 n1 a1 b1 c1 d1, .mtch m2 n2 a2 b2 c2 d2 =>
  if h : m1 == m2 && n1 == n2 then
    let a : Fun.Vec Bool m1 := λ i => beq (a1 i) (a2 (by simp at h; rw[<-h.1]; exact i))
    let c : Fun.Vec Bool n1 := λ i => (c1 i).beq (c2 (by simp at h; rw[<-h.2]; exact i))
    let d : Fun.Vec Bool n1 := λ i => beq (d1 i) (d2 (by simp at h; rw[<-h.2]; exact i))
    a.to.foldl (·&&·) true && b1.to.beq b2.to && c.to.foldl (·&&·) true && d.to.foldl (·&&·) true
   else false
| annot t1 A1, annot t2 A2 => beq t1 t2 && A1 == A2
| _, _ => false

instance instBEq_Term : BEq Term where
  beq := Term.beq

instance instReflBEq_Term : ReflBEq Term where
  rfl := by
    intro a; induction a <;> simp +instances [instBEq_Term, Term.beq] at *
    all_goals try (grind)
    case global =>
      apply And.intro;
      case _ =>
        apply And.intro
        apply instReflBEqVec.rfl
        apply instReflBEqVec.rfl
      case _ ih =>
        simp [Vec.foldl_and_true]; intro h;
        replace h := Vec.getElem_of_mem h;
        rcases h with ⟨i, h⟩
        replace ih := ih i;
        grind
    case mtch m n ss sτs ps rhs ih1 ih2 =>
      apply And.intro
      · apply And.intro
        · generalize zdef : Fun.Vec.to (λ i => (ss i).beq (ss i)) = z at *;
          replace zdef := Vec.refl_indexing.1 zdef;
          rw[Vec.foldl_and_true]
          apply And.intro;
          · intro v v_in_vs
            replace v_in_vs := Vec.getElem_of_mem v_in_vs
            rcases v_in_vs with ⟨i, v_in_vs⟩
            replace zdef := zdef i;
            conv at zdef =>
              lhs
              simp [<-Vec.to_get_elem]
            subst v; rw[<-zdef]; apply ih1 i
          · apply instReflBEqVec.rfl
        · generalize zdef : Fun.Vec.to (λ i => (ps i).beq  (ps i)) = z at *;
          replace zdef := Vec.refl_indexing.1 zdef;
          rw[Vec.foldl_and_true]
          intro v v_in_vs
          replace v_in_vs := Vec.getElem_of_mem v_in_vs
          rcases v_in_vs with ⟨i, v_in_vs⟩
          replace zdef := zdef i;
          conv at zdef =>
            lhs
            simp [<-Vec.to_get_elem]
          subst v; rw[<-zdef]; apply Core.instBEq_Pattern.rfl
      · generalize zdef : Fun.Vec.to (λ i => (rhs i).beq  (rhs i)) = z at *;
        replace zdef := Vec.refl_indexing.1 zdef;
        rw[Vec.foldl_and_true]
        intro v v_in_vs
        replace v_in_vs := Vec.getElem_of_mem v_in_vs
        rcases v_in_vs with ⟨i, v_in_vs⟩
        replace zdef := zdef i;
        conv at zdef =>
           lhs
           simp [<-Vec.to_get_elem]
        subst v; rw[<-zdef]; apply ih2 i

private theorem Term.eq_of_beq : ∀ {a b : Term}, (a == b) = true -> a = b
:= by
  intro a b
  cases a
  all_goals (cases b <;> simp [Term.beq, BEq.beq] at *)
  case global.global m1 n1 p1 x p1s q1s s1s m2 n2 p2 y p2s q2s s2s =>
    intro e1 e2 e3 ⟨⟨e4, e5⟩, e6⟩ e7
    subst e1 e4 e5 e6
    replace e2 := instLawfulBEqVec.eq_of_beq e2
    replace e3 := instLawfulBEqVec.eq_of_beq e3
    subst e2 e3; simp
    simp [Vec.foldl_and_true] at e7
    funext; case _ i =>
    simp [Vec.exists_mem_iff_getElem] at e7;
    replace e7 := e7 i; simp [<-Vec.to_get_elem] at e7
    apply Term.eq_of_beq e7
  case appt.appt p1 t1 q1 p2 t2 q2 =>
    intro e1 e2 e3
    replace e1 := eq_of_beq e1
    subst e1; simp; apply And.intro
    · apply Core.instLawfulBEq_Ty.eq_of_beq e2
    · apply Core.instLawfulBEq_Ty.eq_of_beq e3
  case app.app p1 t1 q1 p2 t2 q2 =>
    intro e1 e2 e3
    replace e1 := Term.eq_of_beq e1
    replace e2 := Term.eq_of_beq e2
    replace e3 := Core.instLawfulBEq_Ty.eq_of_beq e3
    subst e1 e2 e3; simp
  case lamt.lamt K1 t1 K2 t2 =>
    intro e1 e2
    replace e1 := Core.instLawfulBeq_Kind.eq_of_beq e1
    replace e2 := Term.eq_of_beq e2
    subst e1 e2; simp
  case lam.lam K1 t1 K2 t2 =>
    intro e1 e2
    replace e1 := Core.instLawfulBEq_Ty.eq_of_beq e1
    replace e2 := Term.eq_of_beq e2
    subst e1 e2; simp
  case annot.annot t1 K1 t2 K2 =>
    intro e1 e2
    replace e2 := Core.instLawfulBEq_Ty.eq_of_beq e2
    replace e1 := Term.eq_of_beq e1
    subst e1 e2; simp
  case mtch.mtch m1 n1 ss1 sτs1 ps1 b1 m2 n2 ss2 sτs2 ps2 b2 =>
    intro ⟨e1, e2⟩ e3 e4 e5 e6
    subst e1 e2; simp at *
    generalize z1def : Fun.Vec.to (λ i => (ss1 i).beq (ss2 i)) = z1 at *
    generalize z2def : Fun.Vec.to (λ i => (ps1 i).beq (ps2 i)) = z2 at *
    generalize z3def : Fun.Vec.to (λ i => (b1 i).beq (b2 i)) = z3 at *
    replace z1def := Vec.refl_indexing.1 z1def;
    replace z2def := Vec.refl_indexing.1 z2def;
    replace z3def := Vec.refl_indexing.1 z3def;
    simp [Vec.foldl_and_true] at e3 e5 e6;
    simp [Vec.exists_mem_iff_getElem] at e3 e5 e6
    apply And.intro
    · funext; case _ i =>
      replace e3 := e3 i; replace z1def := z1def i
      simp [e3] at z1def; simp [<-Vec.to_get_elem] at z1def
      apply Term.eq_of_beq z1def
    · apply And.intro
      · replace e4 := instLawfulBEqVec.eq_of_beq e4
        funext; case _ i =>
        simp [Fun.Vec.to_get_elem, e4]
      · apply And.intro;
        · funext; case _ i =>
          replace e5 := e5 i; replace z2def := z2def i
          simp [e5] at z2def; simp [<-Vec.to_get_elem] at z2def
          apply Core.instLawfulBEq_Pattern.eq_of_beq z2def
        · funext; case _ i =>
          replace e6 := e6 i; replace z3def := z3def i
          simp [e6] at z3def; simp [<-Vec.to_get_elem] at z3def
          apply Term.eq_of_beq z3def

instance instLawfulBEq_Term : LawfulBEq Term where
  eq_of_beq := Term.eq_of_beq

end Surface
