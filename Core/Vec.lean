import LeanSubst
import Lilac

open LeanSubst
open Lilac

@[simp]
theorem Vec.to_iso : Vec.to (Fun.Vec.to v) = v := sorry

@[simp]
theorem Fun.Vec.to_iso : Fun.Vec.to (Vec.to v) = v := sorry

def Fun.Vec.update (v : Fun.Vec A n) (a : A) (i : Fin n) : Fun.Vec A n
| k => if i == k then a else v i

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

def Sequ.append_vec : Vec α n -> Fun.Sequ α -> Fun.Sequ α
| #𝓋[], s => s
| .cons hd tl, s => hd :: (append_vec tl s)

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

instance : GetElem (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := Vec.get_elem xs i

instance : GetElem? (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem? xs i := .some (Vec.get_elem xs i)

@[simp]
theorem get_cons_head {t : Vec T n} : (h::t)[(0 : Fin (n + 1))] = h := by
  simp [getElem, Vec.get_elem]

@[simp]
theorem get_cons_tail_succ {t : Vec T n} {i : Fin n} : (h::t)[Fin.succ i] = t[i] := by
  simp [getElem, Vec.get_elem]

@[simp]
theorem Vec.to_index {v : Fun.Vec α _} : v.to[i] = v i := by
  induction v using Fun.Vec.induction
  case nil => apply Fin.elim0 i
  case cons hd tl ih =>
    simp [Fun.Vec.to_cons]
    cases i using Fin.cases
    case zero => simp [Fun.Vec.cons_zero]
    case succ i => simp [Fun.Vec.cons_succ, ih]

@[simp, grind =]
theorem Vec.index_into_map {v : Vec α n} {i : Fin n} : (Vec.map f v)[i] = f v[i] := by sorry

def Vec.length (_ : Vec A n) : Nat := n

theorem Vec.length_bound : (v : Vec A n) -> Vec.length v = n := by
  intro v
  unfold Vec.length
  induction n <;> (simp at *)

@[simp]
def Vec.sum : Vec Nat n -> Nat
| .nil => 0
| .cons hd tl => hd + Vec.sum tl


def Vec.rmap [i : RenMap S] (r : Ren) : Vec S n -> Vec S n
| .nil => .nil
| .cons x tl => (i.rmap r x) :: rmap r tl

instance [RenMap S] : RenMap (Vec S n) where
  rmap := Vec.rmap

def Vec.smap [SubstMap S T] (σ : Subst T) : Vec S n -> Vec S n
| .nil => .nil
| .cons x tl => x[σ:_] :: smap σ tl

instance [SubstMap S T] : SubstMap (Vec S n) T where
  smap := Vec.smap

@[simp, grind =]
theorem Vec.smap_nil [SubstMap S T] {σ : Subst T} : (@Vec.nil S)[σ:_] = #𝓋[] := by
  simp [SubstMap.smap, Vec.smap]

@[simp, grind =]
theorem Vec.smap_cons [SubstMap S T] {x} {tl : Vec S n} {σ : Subst T}
  : (x :: tl)[σ:_] = x[σ:_] :: tl[σ:_]
:= by
  simp [SubstMap.smap, Vec.smap]

instance [RenMap T] [SubstMap S T] [SubstMapId S T]
  : SubstMapId (Vec S n) T
where
  apply_id := by intro t; induction t <;> simp [*]

instance [RenMap S] [RenMap T] [SubstMap T T] [SubstMap S T] [SubstMapCompose S T]
  : SubstMapCompose (Vec S n) T
where
  apply_compose := by intro s σ τ; induction s <;> simp [*]

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

def Vec.seq : Vec (Option T) n -> Option (Vec T n)
| .nil => some $ .nil
| .cons none tl => none
| .cons (some hd) tl => do
  let tl' <- Vec.seq tl
  return .cons hd tl'

-- theorem Vec.seq_sound {vs : Vec n (Option Q)} {vs' : Vec n Q}:
--   vs.seq = some vs' ->
--   ∀ i, (vs i) = some (vs' i) := by
-- intro h i;
-- apply Vec.induction
--   (A := Option Q)
--   (motive := λ x v => ∀ vs' : Vec x Q, ∀ i, v.seq = some vs' -> v i = some (vs' i))
--   (nil := by intro h'; simp)
--   (cons := by
--     intro x hd tl ih vs' j; simp [seq];
--     generalize zdef : (Vec.cons hd tl).seq_lemma = z;
--     cases z <;> simp at *
--     case inr v =>
--     replace v := v j
--     intro h'
--     have jeq : j = j := by rfl
--     replace h' := congrFun h' j;
--     rcases v with ⟨A, v⟩
--     simp only [v] at h'; simp at h'; rw[<-h']; assumption
--     )
--   vs vs' i h

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
-- def Vec.get_elem_if_eq [BEq Q][LawfulBEq Q] (vs : Vec n Q) : Option Q :=
-- match n with
-- | 0 => none
-- | _ + 1 => match vs.uncons with
--   | ⟨h, vs'⟩ => if Vec.elems_eq_to h vs' then return h else none

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


-- -- returns the first element that is not none
-- def Vec.any {n : Nat} (vs : Vec n (Option T)) : Option T :=
--   match n with
--   | 0 => none
--   | _ + 1 => match vs.uncons with
--     | ⟨h, tl⟩ => if h.isSome then h else tl.any


-- -- Proof that Any actually matches the first element
-- theorem Vec.any_returns_first {t : T} : ∀ n, {vs : Vec n (Option T)} ->
--   vs.any = some t ->
--   ∃ i, vs i = some t ∧ ∀ j, j < i -> vs j = none := by
-- apply Vec.induction <;> simp [Vec.any]
-- case _ =>
--   intro n hd tl ih h
--   split at h
--   case _ => exists 0; simp; exact h
--   case _ =>
--     replace ih := ih h;
--     rcases ih with ⟨i, ih1, ih2⟩
--     exists Fin.succ i
--     apply And.intro
--     case _ => simp; exact ih1
--     case _ =>
--       intro j
--       induction j using Fin.induction <;> simp at *
--       case _ h => exact h
--       case _ j ih h =>
--         intro le; replace ih2 := ih2 _ le; exact ih2


-- def Vec.zip {n} (ps: Vec n Q) (cs : Vec n Q') : Vec n (Q × Q') := λ i => (ps i , cs i)

-- theorem Vec.zip_sound {n} {ps: Vec n Q} {cs : Vec n Q'} :
--   ∀ i, (ps.zip cs i) = (ps i , cs i) := by
-- intro i; simp [Vec.zip]
