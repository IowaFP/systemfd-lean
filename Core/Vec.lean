import LeanSubst
import Lilac

open LeanSubst


namespace Lilac

def Vec.beq [BEq α] : Vec α n -> Vec α n -> Bool
| .nil, .nil => true
| .cons x xs, .cons y ys => x == y && xs.beq ys

instance instBeq_Vec [BEq α] : BEq (Vec α n) where
  beq := Vec.beq


@[simp]
theorem Vec.to_iso : Vec.to (Fun.Vec.to v) = v
 := by
 apply v.induction <;> simp
 · intro n hd tl ih
   funext; case _ i =>
   induction i using Fin.induction
   case zero => rw[Fun.Vec.cons_zero]; unfold Fun.Vec.cons; rw[Fin.cases_zero]
   case succ ih1 => rw[Fun.Vec.cons_succ]; unfold Fun.Vec.cons; rw[Fin.cases_succ]; rw[ih]

@[simp]
theorem Fun.Vec.to_iso : Fun.Vec.to (Lilac.Vec.to v) = v
:= by
  induction v <;> simp at *
  case cons => assumption

def Fun.Vec.update (v : Fun.Vec A n) (a : A) (i : Fin n) : Fun.Vec A n
| k => if k == i then a else v k

def Fun.Vec.length (_ : Fun.Vec A n) : Nat := n

@[simp]
theorem Fun.Vec.update_eq : update v a i i = a := by
  unfold update; simp

theorem Fun.Vec.update_neq : ∀ j ≠ i, v j = update v a i j := by
  intro j i_ne_j
  unfold update; simp
  intro h; contradiction

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

@[simp]
theorem Vec.enumerate_nil : Vec.enumerate (A := A) #𝓋[] = #𝓋[] := by
  simp [Vec.enumerate, Vec.enumerate.go]

def Vec.drop : Vec T (n + 1) -> Vec T n
| .cons _ tl => tl

def Vec.to_list : Vec T n -> List T
| .nil => .nil
| .cons hd tl => .cons hd (Vec.to_list tl)

def Sequ.append_vec : Vec α n -> Fun.Sequ α -> Fun.Sequ α
| #𝓋[], s => s
| .cons hd tl, s => hd :: (append_vec tl s)

def Vec.eq [BEq α]: Vec α n -> Vec α m -> Bool
| #𝓋[], #𝓋[] => true
| .cons hd1 tl1, .cons hd2 tl2 => hd1 == hd2 && Vec.eq tl1 tl2
| _ , _=> false

theorem Vec.eq_len_sound [BEq α] {vs1 : Vec α n} {vs2 : Vec α m} : vs1.eq vs2 = true ->
  m = n := by
intro h
fun_induction Vec.eq <;> simp at *
simp_all

@[simp]
theorem Vec.nil_singleton : (v1 v2 : Vec T 0) -> v1 = v2
| .nil, .nil => rfl

def Vec.get_elem : Vec α n -> Fin n -> α
| .cons hd tl, i => Fin.cases hd (Vec.get_elem tl) i

instance instGetElem_Vec : GetElem (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := Vec.get_elem xs i

instance instGetElem_Vec? : GetElem? (Vec α n) (Fin n) α (λ _ _ => True) where
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

theorem Vec.enumerate_index.go : {v : Vec A n} -> {i : Fin n} -> (Vec.enumerate.go k v)[i] = (i.val + k, v[i])
| .nil, i => Fin.elim0 i
| .cons hd tl, i => by
  cases i using Fin.cases
  case zero => simp [enumerate.go]
  case succ i =>
    simp [enumerate.go]
    have lem := enumerate_index.go (k := k + 1) (v := tl) (i := i)
    rw [lem]; congr 1; omega

@[simp]
theorem Vec.enumerate_index {v : Vec A n} {i : Fin n} : (Vec.enumerate v)[i] = (i.val, v[i]) := by
  simp [enumerate]; rw [enumerate_index.go]; simp

@[simp, grind =]
theorem Vec.index_into_map {v : Vec α n} {i : Fin n} : (Vec.map f v)[i] = f v[i] := by
  fun_induction Vec.map
  case _ => apply Fin.elim0 i
  case _ hd tl ih =>
  induction i using Fin.induction <;> simp at *
  case _ h => apply ih

def Vec.length (_ : Vec A n) : Nat := n

theorem Vec.length_bound : (v : Vec A n) -> Vec.length v = n := by
  intro v
  unfold Vec.length
  induction n <;> (simp at *)

@[simp]
theorem Vec.to_list_length : {v : Vec A n} -> (Vec.to_list v).length = n
| .nil => by simp [Vec.to_list]
| .cons hd tl =>
  have lem := Vec.to_list_length (v := tl)
  by grind [Vec.to_list]

theorem Vec.eq_index_ext {v1 v2 : Vec A n} : (∀ (i : Fin n), v1[i] = v2[i]) -> v1 = v2 :=
  match n, v1, v2 with
  | 0, Vec.nil, Vec.nil => λ _ => Vec.nil_singleton .nil .nil
  | n + 1, .cons h1 t1 , .cons h2 t2 =>
    by intro h;
       have he := h 0; simp at he;
       subst he; simp;
       apply Vec.eq_index_ext
       intro i; apply h i.succ

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

@[simp]
theorem Vec.ren_index [SubstMap T T] {i : Fin n} {v : Vec T n} {σ : Subst T} : v[i][σ:_] = v[σ:_][i] :=
  match n, v with
  | 0, v => Fin.elim0 i
  | n + 1, .cons x xs => by
    induction i using Fin.induction <;> simp at *
    case _ i ih => apply Vec.ren_index

theorem Vec.to_get_elem (vs : Vec α n) : ∀i, vs.to i = vs.get_elem i := by sorry


def Vec.reprPrec [Repr T] : {n : Nat} -> Vec T n -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr (v.get_elem 0)
| _ + 1, .cons v t, i =>
  (repr v) ++ ", " ++ (Vec.reprPrec t i)


instance instRepr_Vec [Repr T] : Repr (Vec T n) where
  reprPrec v n := "#𝓋[" ++ Vec.reprPrec v n ++ "]"

@[simp]
def Vec.seq : Vec (Option T) n -> Option (Vec T n)
| .nil => some .nil
| .cons none tl => none
| .cons (some hd) tl => do
  let tl' <- Vec.seq tl
  return .cons hd tl'

theorem Vec.seq_sound_get_elem {vs : Vec (Option Q) n} {vs' : Vec Q n} :
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


theorem Vec.seq_sound1 {vs : Fun.Vec α n} {vs' : Vec β n} (f : α -> Option β) :
  (Fun.Vec.to (λ i => f (vs i))).seq = some vs' ->
  ∀ i : Fin n, f (vs i) = some (vs'.to i) := sorry

theorem Vec.map_seq_sound {vs : Vec α n} {vs' : Vec β n} (f : α -> Option β) :
  (Vec.map f vs).seq = some vs' ->
  ∀ i : Fin n, f (vs.to i) = some (vs'.to i) := sorry

theorem Vec.seq_sound2 {vs1 : Fun.Vec α n} {vs2 : Fun.Vec β n} {vs' : Vec γ n} (f : α -> β -> Option γ) :
  (Fun.Vec.to (λ i => f (vs1 i) (vs2 i))).seq = some vs' ->
  ∀ i : Fin n, f (vs1 i) (vs2 i) = some (vs'.to i) := by
intro h1 i
match n, vs1, vs2 with
| 0, vs1, vs2 => apply i.elim0
| n + 1, xs, ys =>
  induction i using Fin.induction
  sorry
  sorry

theorem Vec.units (vs : Vec Unit n) : ∀ i, (vs.to i) = () := by
 intro i
 induction vs
 apply i.elim0
 simp

@[simp]
def Vec.range (n : Nat) : Vec Nat n := go n 0
where
  go : (n : Nat) -> Nat -> Vec Nat n
  | 0, _ => .nil
  | n + 1, acc => .cons acc (go n (acc + 1))

#guard (Vec.range 3) == (#𝓋[0, 1, 2])

@[simp]
theorem Vec.range_zero : range 0 = .nil := by
  unfold range; unfold range.go; apply Vec.nil_singleton

@[simp]
def Vec.elems_eq_to [BEq Q] {n : Nat} (e : Q) (vs : Vec Q n) : Bool :=
  vs.fold true (λ c acc => c == e && acc)

theorem Vec.elems_eq_to_sound [BEq Q] [LawfulBEq Q] {e : Q} {vs : Vec Q n} :
  vs.elems_eq_to e = true ->
  ∀ i, (vs.get_elem i) = e := by
intro h
induction vs <;> simp at *
case _ n hd tl ih =>
  cases h.1; replace ih := ih h.2
  intro i'
  induction i' using Fin.induction <;> simp at *
  case _ => simp [get_elem, Fin.cases_zero]
  case _ => simp [get_elem, Fin.cases_succ]; apply ih


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


-- Returns the 1st element if all the elements are equal
@[simp]
def Vec.get_elem_if_eq [BEq Q][LawfulBEq Q] (vs : Vec Q n) : Option Q :=
match vs with
| .nil => none
| .cons x .nil => return x
| .cons x xs => do
  let e <- xs.get_elem_if_eq
  if e == x then return x else none

theorem Vec.get_elem_if_eq_sound [BEq Q] [LawfulBEq Q] {vs : Vec Q n} {t : Q} :
  vs.get_elem_if_eq = some t ->
  ∀ i, vs.get_elem i = t := by
intro h;
fun_induction Vec.get_elem_if_eq <;> simp at *
case _ => simp [get_elem, Fin.cases_zero]; assumption
case _ n x xs ih1 ih2 =>
  intro i
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h⟩
  simp at h; cases h.2.1; cases h.2.2; simp at h
  simp[get_elem]
  induction i using Fin.induction
  · simp[Fin.cases_zero]
  · simp[Fin.cases_succ]; apply ih1 h

-- Finds the first element that satisfies the predicate and its index
@[simp]
def Vec.find_aux {n : Nat} (p : T -> Bool) (vs : Vec T n) (k : Nat) : Option (T × Fin n) :=
  if h : k < n
  then
    let i := Fin.mk k h
    let e := (vs.get_elem i)
    if p e
       then some (e, i)
       else if h' : (k + 1) < n then Vec.find_aux p vs (k + 1) else none
  else none

-- Finds the first element that satisfies the predicate and its index
@[simp]
def Vec.find {n : Nat} (p : T -> Bool) (vs : Vec T n) : Option (T × Fin n) := Vec.find_aux p vs 0

def Vec.findIdx {n : Nat} (p : T -> Bool) (vs : Vec T n) : Option (Fin n) := do
  let ⟨_, i⟩ <- Vec.find_aux p vs 0
  return i

def Vec.find_aux_sound {n k: Nat} (p : T -> Bool) (vs : Vec T n) (ei : T × Fin n) :
  Vec.find_aux p vs k = some ei ->
  vs.get_elem ei.2 = ei.1
:= by
  intro h
  fun_induction find_aux
  case _ e _ => cases h; simp; unfold e; rfl
  case _ ih => apply ih h
  case _ => cases h
  case _ => cases h



theorem Vec.find_aux_returns_first_elem {n k: Nat} {h : k < n} (p : T -> Bool) (vs : Vec T n) (e : T) (i : Fin n) :
  Vec.find_aux p vs k = some ⟨e , i⟩ ->
  vs.get_elem i = e ∧
  (∀ j : Fin n, ⟨k, h⟩ ≤ j ∧ j < i -> p (vs.get_elem j) = false) := by
intro h1
constructor
· apply Vec.find_aux_sound p vs ⟨e, i⟩ h1
· intro j b
  rcases b with ⟨lb, up⟩
  fun_induction find_aux
  case _ l i e =>
    subst i; injection h1; case _ h1 =>
    injection h1; case _ q1 q2 =>
    subst q2; subst l
    -- contradiction as x ≤ j and j < x
    exfalso
    sorry
  case _ k k_le_n i l _ h' ih =>
    apply @ih h'
    apply h1
    sorry

  case _ => cases h1
  case _ => cases h1


theorem Vec.find_returns_first_elem {n : Nat} (p : T -> Bool) (vs : Vec T n) (ei : T × Fin n) :
  vs.find p = some ei ->
  vs.get_elem ei.2 = ei.1 ∧
  (∀ j : Fin n, j < ei.snd -> p (vs.get_elem j) = false)
:= by sorry
  -- intro h
  -- have lem := Vec.find_aux_returns_first_elem (k := 0) p vs ei h
  -- constructor
  -- · apply lem.1
  -- · intro j h;
  --   have lem2 := lem.2 j
  --   apply lem2
  --   constructor
  --   · simp
  --   · apply h

-- returns the first element that is not none
@[simp]
def Vec.any {n : Nat} : (vs : Vec (Option T) n) -> Option T
| .nil => none
| .cons (some x) xs => some x
| .cons _ xs => xs.any

#guard (Vec.find Option.isSome #𝓋[none, some 1, some 2]) == some (some 1, 1)

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

#guard (Vec.any #𝓋[none, some 2, some 3]) == some 2


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

theorem Vec.eq_sound [BEq α][LawfulBEq α] {v1 : Vec α n} {v2 : Vec α m} : (h : v1.eq v2) ->
  v1 = ((cast (by have lem := @Vec.eq_len_sound α n m _ v1 v2 h
                  rw[lem]) v2))
:= by
  intro h;
  have lem := Vec.eq_len_sound h
  subst m
  match n, v1, v2 with
  | 0, .nil, .nil => simp
  | n + 1, .cons x xs , .cons y ys =>
    unfold Vec.eq at h; simp at *;
    constructor
    apply h.1
    apply Vec.eq_sound h.2

-- failure indicates t was not in the vector
def Vec.remove [BEq T] (t : T) : {n : Nat} -> Vec T (n + 1) -> Option (Vec T n)
| 0, .cons x xs => if t == x then return xs else none
| _ + 1, .cons x xs =>
  if t == x then return xs
  else do let xs' <- xs.remove t
          return .cons x xs'

-- counts the occurence of t in the vector
def Vec.count [BEq T] (t : T) : Vec T n -> Nat
| .nil => 0
| .cons x xs => if t == x then 1 + xs.count t else xs.count t

theorem Vec.count_cons [BEq T] (t x : T) (vs : Vec T n) :
  Vec.count t (x :: vs) = if t == x then 1 + vs.count t else vs.count t := by
simp [Vec.count];


def Vec.remove_sound [BEq T][LawfulBEq T] (t : T) {vs : Vec T (n + 1)} {vs' : Vec T n}:
  vs.remove t = some vs' ->
  vs.count t = 1 + vs'.count t := by
intro h
fun_induction Vec.remove <;> simp [Vec.count] at *
case _ h2 => rw[h2]; simp; subst h; rfl
case _ h2 => rw[h2]; simp; subst h; rfl
case _ ih v' =>
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨vs', h3, h⟩; cases h
  split <;> simp at *
  contradiction
  replace ih := ih h3
  rw[Vec.count_cons]; split <;> simp at *
  contradiction
  assumption


theorem Vec.get_elem_indexing {vs : Vec T n} {i : Fin n} : vs.to i = vs.get_elem i := by
sorry




def append {α : Type _} {n : Nat} (v : Vec α n) : {m : Nat} -> Vec α m -> Vec α (m + n)
| 0, .nil => by simp; apply v
| m + 1, .cons x xs => by
  let tl := append v xs
  let vs := x :: tl
  have lem : m + 1 + n = m + n + 1 := by omega
  rw[lem]; clear lem
  apply vs

def paste (b : String) : Vec (Vec String m) n -> Vec (Vec String (m + 1)) n
| .nil => .nil
| .cons x xs => .cons (.cons b x) (paste b xs)

def combine (base : Vec (Vec String k) m) : {n : Nat} -> Vec String (n + 1) -> ((p : Nat) × Vec (Vec String (k + 1)) p) -- p = m + n
| 0, .cons x .nil => ⟨m, paste x base⟩
| _ + 1, .cons x xs =>
  let ⟨p , vs⟩ := combine base xs
  let vs' := paste x base
  let ys := append vs' vs
  ⟨p + m, ys⟩


-- def enumerate_aux : (Vec ((n : Nat) × Vec String n) (m + 1)) -> ((p : Nat) × Vec (Vec String k) p) -> ((p : Nat) × Vec (Vec String (k + 1)) p)
-- | .cons ⟨n , x⟩ _, ⟨m, acc⟩ =>
--    ⟨n + m, combine acc x⟩
-- | .cons x xs, ⟨p, acc⟩ =>
--   combine acc x.2
--   sorry


end Lilac
