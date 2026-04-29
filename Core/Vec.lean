import Core.Util
import LeanSubst
import Lilac

open LeanSubst


namespace Lilac

def Fun.Vec.update (v : Fun.Vec A n) (a : A) (i : Fin n) : Fun.Vec A n
| k => if i == k then a else v i

def Fun.Vec.length (_ : Fun.Vec A n) : Nat := n

@[simp]
theorem Fun.Vec.update_eq : update v a i i = a := sorry

theorem Fun.Vec.update_neq : ∀ j ≠ i, v j = update v a i j := sorry

@[simp]
def Vec.fold (d : B) (f : A -> B -> B) : Vec A n -> B
| .nil => d
| .cons hd tl => f hd (Vec.fold d f tl)

@[simp]
def Vec.map (f : A -> B) : Vec A n -> Vec B n
| .nil => .nil
| .cons hd tl => .cons (f hd) (Vec.map f tl)

def Vec.enumerate : Vec A n -> Vec (Nat × A) n := go 0
where
  go {n : Nat} (i : Nat) : Vec A n -> Vec (Nat × A) n
  | .nil => .nil
  | .cons hd tl => .cons (i, hd) (go (i + 1) tl)

def Vec.drop : Vec T (n + 1) -> Vec T n
| .cons _ tl => tl

def Vec.to_list : Vec T n -> List T
| .nil => .nil
| .cons hd tl => .cons hd (Vec.to_list tl)

-- protected def Vec.reprPrec [Repr T] : {n : Nat} -> Vec T n -> Nat -> Std.Format
-- | 0, _, _ => ""
-- | 1, v, _ => repr (v 0)
-- | _ + 1, v, i =>
--   let ⟨h , t⟩ := v.uncons
--   (repr h) ++ ", " ++ (Vec.reprPrec t i)

-- instance [Repr T] : Repr (Vec n T) where
--   reprPrec v n := "v[" ++ Vec.reprPrec v n ++ "]"

@[simp]
theorem Vec.nil_singleton : (v1 v2 : Vec T 0) -> v1 = v2
| .nil, .nil => rfl

def Vec.get_elem : Vec α n -> Fin n -> α
| .cons hd tl, i => Fin.cases hd (Vec.get_elem tl) i

@[simp]
instance : GetElem (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := Vec.get_elem xs i

@[simp]
instance : GetElem? (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem? xs i := .some (Vec.get_elem xs i)

-- @[simp]
-- theorem get_cons_head {t : Vec T n} : (h::t)[0] = h := by simp [Vec.cons]

-- @[simp]
-- theorem get_cons_tail_succ {t : Vec T n} : (h::t) (Fin.succ i) = t i := by
--   simp [Vec.cons];

def Vec.length (_ : Vec A n) : Nat := n

theorem Vec.length_bound : (v : Vec A n) -> Vec.length v = n := by
  intro v
  unfold Vec.length
  induction n <;> (simp at *)

@[simp]
def Vec.sum : Vec Nat n -> Nat
| .nil => 0
| .cons hd tl => hd + Vec.sum tl

-- theorem length_coerce: ∀ n, Vec.length v = n -> (Vec.to_list v).length = n := by
-- apply v.induction <;> simp [Vec.length] at *


-- def Vec.seq_lemma (vs : Vec n (Option Q)) :
--   (Σ' (i : Fin n), ¬ (vs i).isSome) ⊕ ((i : Fin n) -> Σ' A, (vs i) = some A)
-- := by {
--     induction n
--     case _ =>
--       apply Sum.inr; intro i
--       apply Fin.elim0 i
--     case _ n ih =>
--       generalize zdef : uncons vs = z at *
--       rcases z with ⟨h, t⟩
--       have lem := Vec.uncons_iff.1 zdef
--       cases h
--       case none =>
--         apply Sum.inl; apply PSigma.mk 0
--         rw [lem]; simp
--       case some h =>
--         replace ih := ih t
--         cases ih
--         case _ ih =>
--           rcases ih with ⟨k, ih⟩
--           apply Sum.inl; apply PSigma.mk (Fin.succ k)
--           rw [lem]; simp at *; exact ih
--         case _ ih =>
--           apply Sum.inr; intro i
--           cases i using Fin.cases
--           case _ => rw [lem]; simp; apply PSigma.mk h; rfl
--           case _ i => rw [lem]; simp; apply ih i
--   }

@[simp]
def Vec.seq : Vec (Option T) n -> Option (Vec T n)
| .nil => some $ .nil
| .cons none tl => none
| .cons (some hd) tl => do
  let tl' <- Vec.seq tl
  return .cons hd tl'

theorem Vec.seq_sound {vs : Vec (Option Q) n} {vs' : Vec Q n} :
  vs.seq = some vs' ->
  ∀ i, (vs.get_elem i) = some (vs'.get_elem i) := by
intro h i
induction vs <;> simp [Vec.get_elem, Vec.seq] at *
case _ => subst h; cases i; omega
case _ v vs ih =>
  cases v <;> simp at *
  case _ v' =>
  rw[Option.bind_eq_some_iff] at h;
  rcases h with ⟨vs', h1, h2⟩
  cases h2;
  induction i using Fin.induction <;> simp [get_elem] at *
  case _ i h => apply ih h1 i

-- def Vec.elems_eq_to [BEq Q] {n : Nat} (e : Q) (vs : Vec n Q) : Bool :=
--   vs.fold true (λ c acc => c == e && acc)

-- theorem Vec.elems_eq_to_sound [BEq Q] [LawfulBEq Q] {e : Q} {vs : Vec n Q} :
--   vs.elems_eq_to e = true ->
--   ∀ i, (vs i) = e := by
-- apply vs.induction <;> simp [Vec.elems_eq_to] at *
-- case _ =>
--   intro n hd tl ih e h
--   subst hd; replace ih := ih h
--   intro i'
--   induction i' using Fin.induction <;> simp at *
--   case _ i _ => apply ih i


-- theorem quantifier_flip {Q Q' : Type} {v : Vec n Q} (f : Q -> Option Q') :
--   (∀ i, ∃ T, f (v i) = some T) ->
--   ∃ (T' : Vec n Q'), ∀ i, f (v i) = some (T' i) := by
--   intro h
--   generalize T'def : Vec.seq (f <$> v) = T' at *
--   cases T'
--   case none =>
--     exfalso
--     -- completeness of seq
--     unfold Vec.seq at T'def;
--     generalize slem : Vec.seq_lemma (f <$> v)= sl at *
--     cases sl <;> simp at *
--     case inl i =>
--       rcases i with ⟨i, h'⟩
--       -- unfold Vec.map at h'
--       replace h := h i
--       rcases h with ⟨T , h⟩
--       rw[h] at h'; simp at h'
--   case some T' =>
--   exists T'
--   · intro i;
--     replace h := h i
--     rcases h with ⟨q', h⟩
--     have lem := Vec.seq_sound T'def
--     replace lem := lem i; simp at lem; assumption


-- -- Returns the 1st element if all the elements are equal
def Vec.get_elem_if_eq [BEq Q][LawfulBEq Q] (vs : Vec Q n) : Option Q :=
match vs with
| .nil => none
| .cons x .nil => return x
| .cons x xs => do
  let e <- xs.get_elem_if_eq
  if e == x then return x else none

-- theorem Vec.get_elem_if_eq_sound[BEq Q] [LawfulBEq Q] {vs : Vec n Q} {t : Q} :
--   vs.get_elem_if_eq = some t ->
--   ∀ i, vs i = t := by
-- apply vs.induction
-- case _ => simp
-- case _ =>
--   intro n hd tl ih
--   simp [Vec.get_elem_if_eq];
--   intro h1 h2
--   subst t; intro i
--   induction i using Fin.induction <;> simp at *
--   case _ i h =>
--     have lem := Vec.elems_eq_to_sound h1
--     apply lem i


-- returns the first element that is not none
@[simp]
def Vec.any {n : Nat} : (vs : Vec (Option T) n) -> Option T
| .nil => none
| .cons (some x) xs => some x
| .cons _ xs => xs.any

-- Proof that Any actually matches the first element
theorem Vec.any_returns_first {t : T} {n : Nat} : (vs : Vec (Option T) n) ->
  vs.any = some t ->
  ∃ i, vs.get_elem i = some t ∧ ∀ j, j < i -> vs.get_elem j = none
| .nil, p => by simp at p
| .cons (some x) xs, p => ⟨0, ⟨p , by simp⟩⟩
| .cons none xs, p =>
  match xs.any_returns_first (t := t) p with
  | ⟨i', ⟨p1', p2'⟩⟩ => ⟨i'.succ, ⟨by simp[Vec.get_elem]; apply p1',
    by simp[Vec.get_elem];
       intro j; induction j using Fin.induction <;> simp at *
       case _ j ih => apply p2'⟩⟩

@[simp]
def Vec.zip {n} : (ps: Vec Q n) -> (cs : Vec Q' n) -> Vec (Q × Q') n
| .nil , .nil => .nil
| .cons p ps, .cons q qs => (p , q) :: ps.zip qs

theorem Vec.zip_sound {n} : (ps: Vec Q n) -> (cs : Vec Q' n) -> (i : Fin n) ->
  ((ps.zip cs).get_elem i) = (ps.get_elem i , cs.get_elem i)
| .nil, .nil, i => match i with
  | ⟨v , v_le_zero⟩ => by omega
| .cons p ps, .cons q qs, i => by
  induction i using Fin.induction <;> simp [Vec.get_elem] at *
  case _ i ih => apply Vec.zip_sound ps qs i


-- theorem Vect.map_cons {f : Q -> P} {v : Vect n Q} {v' : Vect (n + 1) P} {q : Q} :
--   v' = (λ i => f ((Vect.cons q v) i)) ->
--   v' = Vect.cons (f q) (λ i => (f (v i))) := by
-- intro h
-- revert v' v;
-- intro v
-- apply v.induction
-- case nil => simp
-- case cons =>
--   intro n hd tl ih1
--   intro v' ih2
--   sorry

end Lilac
