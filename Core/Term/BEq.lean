import Core.Ty
import Core.Term.Definition
import Core.Vec

open Lilac

namespace Core
def DataConst.beq : DataConst -> DataConst -> Bool
| .opn, .opn => true
| .cls, .cls => true
| _, _ => false

instance instBEq_DataConst : BEq DataConst where
  beq := DataConst.beq

instance instReflBEq_DataConst : ReflBEq DataConst where
  rfl := by
         intro a; induction a <;> simp +instances [instBEq_DataConst, DataConst.beq] at *

instance instLawfulBEq_DataConst : LawfulBEq DataConst where
  eq_of_beq := by
    intro a b h
    cases a <;> (cases b)
    all_goals (simp +instances [instBEq_DataConst, DataConst.beq] at *)

def Ctor0Variant.beq : Ctor0Variant -> Ctor0Variant -> Bool
| refl A, refl B => A == B

def SpCtorVariant.beq : SpCtorVariant -> SpCtorVariant -> Bool
| .openm, .openm => true
| .data c1, .data c2 => c1 == c2
| _, _ => false

instance instBEq_SpCtorVariant : BEq SpCtorVariant where
  beq := SpCtorVariant.beq

instance instReflBEq_SpCtorVariant : ReflBEq SpCtorVariant where
  rfl := by
         intro a; induction a <;> simp +instances [instBEq_SpCtorVariant, SpCtorVariant.beq] at *

instance instBEq_Ctor0Variant : BEq Ctor0Variant where
  beq := Ctor0Variant.beq

instance instReflBEq_Ctor0Variant : ReflBEq Ctor0Variant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_Ctor0Variant, Ctor0Variant.beq] at *

instance instLawfulBEq_Ctor0Variant : LawfulBEq Ctor0Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_Ctor0Variant, Ctor0Variant.beq] at *
    all_goals (induction b <;> simp at *)

def Ctor1Variant.beq : Ctor1Variant -> Ctor1Variant -> Bool
| prj n1, prj n2 => n1 == n2
| appt a, appt b => a == b
| _, _ => false

instance instBEq_Ctor1Variant : BEq Ctor1Variant where
  beq := Ctor1Variant.beq

instance instReflBEq_Ctor1Variant : ReflBEq Ctor1Variant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_Ctor1Variant, Ctor1Variant.beq] at *

instance instLawfulBEq_Ctor1Variant : LawfulBEq Ctor1Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_Ctor1Variant, Ctor1Variant.beq] at *
    all_goals (induction b <;> simp at *)


def Ctor2Variant.beq : Ctor2Variant -> Ctor2Variant -> Bool
| app, app => true
| apptc, apptc => true
| _, _ => false

instance instBEq_Ctor2Variant : BEq Ctor2Variant where
  beq := Ctor2Variant.beq


instance instReflBEq_Ctor2Variant : ReflBEq Ctor2Variant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_Ctor2Variant, Ctor2Variant.beq] at *

instance instLawfulBEq_Ctor2Variant : LawfulBEq Ctor2Variant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_Ctor2Variant, Ctor2Variant.beq] at *
    all_goals (induction b <;> simp at *)

def TyBindVariant.beq : TyBindVariant -> TyBindVariant -> Bool
| lamt, lamt => true
| allc, allc => true
| _, _ => false

instance instBEq_TyBindVariant : BEq TyBindVariant where
  beq := TyBindVariant.beq

instance instReflBEq_TyBindVariant : ReflBEq TyBindVariant where
  rfl := by
    intro x; induction x <;> simp +instances [instBEq_TyBindVariant, TyBindVariant.beq] at *

instance instLawfulBEq_TyBindVariant : LawfulBEq TyBindVariant where
  eq_of_beq := by
    intro x b; induction x <;> simp +instances [instBEq_TyBindVariant, TyBindVariant.beq] at *
    all_goals (induction b <;> simp at *)

def Pattern.beq : Pattern m1 -> Pattern m2 -> Bool
| .nil, .nil => true
| .cons (x1, ⟨n1, v1, k1⟩) xs, .cons (x2, ⟨n2, v2, k2⟩) ys =>
  if n1 == n2 && k1 == k2 && x1 == x2
  then let v1' : Lilac.Vec Ty n1 := v1.to
       let v2' : Lilac.Vec Ty n2 := v2.to
       Pattern.beq xs ys && Lilac.Vec.beq v1' v2'
  else false
| _, _ => false

instance instBEq_Pattern : BEq (Pattern n) where
  beq := Pattern.beq

private def Pattern.rfl : {n : Nat} -> {p : Pattern n} -> (p == p) = true
| 0, .nil => by rfl
| n + 1, .cons p ps => by
  simp +instances [instBEq_Pattern, Pattern.beq]
  apply And.intro
  apply Pattern.rfl
  apply Vec.beq_refl (a := p.2.2.1)

instance instReflBEq_Pattern : ReflBEq (Pattern n) where
  rfl := Pattern.rfl

private def Pattern.eq_of_beq : {n : Nat} -> {a b : Pattern n} -> (a == b) = true → a = b
| 0, .nil, .nil => by simp
| n + 1, .cons a as, .cons b bs => by
  intro h
  simp +instances [instBEq_Pattern, Pattern.beq] at *
  rcases h with ⟨⟨⟨e1, e2⟩, e3⟩, e4, e5⟩;
  rcases a with ⟨a1, a2, a3, a4⟩
  rcases b with ⟨b1, b2, b3, b4⟩
  simp at *; subst e1; subst e2; subst e3; simp;

  apply And.intro
  · apply Vec.beq_lawful e5
  · apply eq_of_beq e4

instance instLawfulBEq_Pattern : LawfulBEq (Pattern n) where
  eq_of_beq := Pattern.eq_of_beq

def Term.beq : Term -> Term -> Bool
| var x, var y => x == y
| defn x, defn y => x == y
| ctor0 c1, ctor0 c2 => c1 == c2
| ctor1 c1 a1, ctor1 c2 a2 => c1 == c2 && beq a1 a2
| ctor2 c1 a1 b1, ctor2 c2 a2 b2 => c1 == c2 && beq a1 a2 && beq b1 b2
| tbind A1 K1 t1, tbind A2 K2 t2 => A1 == A2 && K1 == K2 && beq t1 t2
| lam A1 t1, lam A2 t2 => A1 == A2 && beq t1 t2
| cast A a1 a2, cast B b1 b2 => A == B && beq a1 b1 && beq a2 b2
| mtch m1 n1 a1 b1 c1, mtch m2 n2 a2 b2 c2 =>
  if h : n1 == n2 && m1 == m2 then
    let a : Lilac.Fun.Vec Bool m1 := λ i => beq (a1 i) (a2 (by simp at h; rw [h.2] at i; exact i))
    let c : Lilac.Fun.Vec Bool n1 := λ i => beq (c1 i) (c2 (by simp at h; rw [h.1] at i; exact i))
    let p : Lilac.Fun.Vec Bool n1 := λ i =>
      let p1 : Pattern m1 := (b1 i).to
      let p2 : Pattern m2 := (b2 (by simp at h; rw[h.1] at i; exact i)).to
      Pattern.beq p1 p2
    Vec.foldl (·&&·) true a.to
    && Vec.foldl (·&&·) true c.to
    && Vec.foldl (·&&·) true p.to
  else false
| spctor (n := n1) v1 s1 A1 B1 ts1, .spctor (n := n2) v2 s2 A2 B2 ts2 =>
  if h : n1 == n2
  then
    let bs : Lilac.Fun.Vec Bool n1 := (λ i => beq (ts1 i) (ts2 (by simp at h; rw[h] at i; exact i)))
    v1 == v2 && s1 == s2 && A1.beq A2 && B1.beq B2 && Vec.foldl (·&&·) true bs.to
  else false
| _, _ => false

instance instBEq_Term : BEq Term where
  beq := Term.beq

theorem Term.rfl : {a : Term} -> (a == a) = true
| var _ | defn _ | ctor0 _ =>
  by simp +instances [instBEq_Term, Term.beq]
| ctor1 _ _ | tbind _ _ _ | lam _ _ =>
  by simp +instances [instBEq_Term, Term.beq]; apply Term.rfl
| ctor2 _ _ _ | cast _ _ _ =>
  by simp +instances [instBEq_Term, Term.beq]; apply And.intro; apply Term.rfl; apply Term.rfl
| mtch m n s p b =>
  by simp +instances [instBEq_Term, Term.beq]
     apply And.intro
     · apply And.intro
       · generalize zdef : Fun.Vec.to (λ i => (s i).beq (s i)) = z at *;
         replace zdef := refl_indexing zdef;
         rw[Vec.foldl_and_true]
         intro v v_in_vs
         replace v_in_vs := Vec.getElem_of_mem v_in_vs
         rcases v_in_vs with ⟨i, v_in_vs⟩
         replace zdef := zdef i; rw[v_in_vs] at zdef; simp [<-Vec.to_get_elem] at zdef; rw[<-zdef]
         apply Term.rfl
       · generalize zdef : Fun.Vec.to (λ i => (b i).beq  (b i)) = z at *;
         replace zdef := refl_indexing zdef;
         rw[Vec.foldl_and_true]
         intro v v_in_vs
         replace v_in_vs := Vec.getElem_of_mem v_in_vs
         rcases v_in_vs with ⟨i, v_in_vs⟩
         replace zdef := zdef i; rw[v_in_vs] at zdef; simp [<-Vec.to_get_elem] at zdef; rw[<-zdef]
         apply Term.rfl
     · generalize zdef : Fun.Vec.to (λ i => (p i).beq  (p i)) = z at *;
       replace zdef := refl_indexing zdef;
       rw[Vec.foldl_and_true]
       intro v v_in_vs
       replace v_in_vs := Vec.getElem_of_mem v_in_vs
       rcases v_in_vs with ⟨i, v_in_vs⟩
       replace zdef := zdef i; rw[v_in_vs] at zdef; simp [<-Vec.to_get_elem] at zdef; rw[<-zdef]
       apply Pattern.rfl
| spctor m1 m2 Ks1 Ks2 Ts =>
  by simp +instances [instBEq_Term, Term.beq]
     apply And.intro;
     · apply And.intro
       · simp +instances [instBEq_Ty]
         apply Vec.beq_refl (a := Ks1)
       · apply Vec.beq_refl (a := Ks2)
     · case _ i =>
       generalize zdef : Fun.Vec.to (λ i => (Ts i).beq  (Ts i)) = z at *;
       replace zdef := refl_indexing zdef;
       rw[Vec.foldl_and_true]
       intro v v_in_vs
       replace v_in_vs := Vec.getElem_of_mem v_in_vs
       rcases v_in_vs with ⟨i, v_in_vs⟩
       replace zdef := zdef i; rw[v_in_vs] at zdef; simp [<-Vec.to_get_elem] at zdef; rw[<-zdef]
       apply Term.rfl


instance instReflBEq_Term : ReflBEq Term where
  rfl := Term.rfl


private def Term.eq_of_beq : ∀ {a b : Term}, (a == b) = true → a = b
:= by
  intro a b h
  cases a <;> cases b
  all_goals (simp +instances [Term.beq, instBEq_Term] at *; repeat assumption)
  all_goals try (case _ =>
    rcases h with ⟨h1, h2⟩
    apply And.intro
    · apply h1
    · apply Term.eq_of_beq h2)

  all_goals try (case _ =>
    rcases h with ⟨⟨h1, h2⟩, h3⟩
    apply And.intro
    · apply h1
    · apply And.intro
      · apply Term.eq_of_beq h2
      · apply Term.eq_of_beq h3)

  case tbind.tbind =>
    rcases h with ⟨⟨h1, h2⟩, h3⟩
    apply And.intro
    · apply h1
    · apply And.intro
      · apply h2
      · apply Term.eq_of_beq h3

  case mtch.mtch m1 n1 ss1 ps1 b1 m2 n2 ss2 ps2 b2 =>
    rcases h with ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    subst h1; subst h2; simp at *;
    generalize z1def : Fun.Vec.to (λ i => (ss1 i).beq (ss2 i)) = z1 at *
    generalize z2def : Fun.Vec.to (λ i => (ps1 i).beq (ps2 i)) = z2 at *
    generalize z3def : Fun.Vec.to (λ i => (b1 i).beq (b2 i)) = z3 at *
    rw[Vec.foldl_and_true] at h3
    replace z1def := refl_indexing z1def; simp at *
    sorry

  case spctor.spctor =>
    rcases h with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    rcases h5 with ⟨h , h5⟩
    subst h; simp at *
    sorry


instance instLawfulBEq_Term : LawfulBEq Term where
  eq_of_beq := Term.eq_of_beq

end Core
