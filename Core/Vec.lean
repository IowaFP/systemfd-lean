import LeanSubst
import Lilac.Vect

open LeanSubst
open Vect

def Vect.drop (v : (Vect (n + 1) Q)) : Vect n Q := v.uncons.2


protected def Vect.reprPrec [Repr T] : {n : Nat} -> Vect n T -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr (v 0)
| _ + 1, v, i =>
  let ⟨h , t⟩ := v.uncons
  (repr h) ++ ", " ++ (Vect.reprPrec t i)

protected def Vect.reprPrec' (repr : T -> Std.Format) : {n : Nat} -> Vect n T -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr (v 0)
| _ + 1, v, i =>
  let ⟨h, t⟩ := uncons v
  (repr h) ++ ", " ++ (Vect.reprPrec' repr t i)


instance [Repr T] : Repr (Vect n T) where
  reprPrec v n := "v[" ++ Vect.reprPrec v n ++ "]"


@[simp]
theorem Vect.nil_singleton (v1 v2 : Vect 0 T) : v1 = v2 := by
  funext; case _ i =>
  cases i; case _ i p => cases p

-- @[simp]
-- theorem Vect.uncons_cons_cancel : uncons (h::t) = ⟨h, t⟩ := by
--   simp [uncons];

-- @[simp]
-- theorem Vect.head_drop_cancel : ((v 0) :: (drop v)) = v := by
--   funext; case _ i =>
--   cases i; case _ i p =>
--   cases i <;> simp [cons, drop]

@[simp]
instance : GetElem (Vect n α) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := xs i

@[simp]
instance : GetElem? (Vect n α) (Fin n) α (λ _ _ => True) where
  getElem? xs i := .some (xs i)

@[simp]
theorem get_cons_head {t : Vect T n} : (h::t) 0 = h := by simp [Vect.cons]

@[simp]
theorem get_cons_tail_succ {t : Vect T n} : (h::t) (Fin.succ i) = t i := by
  simp [Vect.cons];

-- @[simp]
-- theorem get1_0 : v[a] 0 = a := by simp

-- @[simp]
-- theorem get2_0 : v[a, b] 0 = a := by simp

-- @[simp]
-- theorem get2_1 : v[a, b] 1 = b := by simp [Vect.cons]

def Vect.map (f : A -> B) (v : Vect n A) : Vect n B := λ i => f (v i)

-- @[simp]
-- def Vect.map2 (v1 : Vect A n) (v2 : Vect B n) (f : A -> B -> C)  : Vect C n := λ i => f (v1 i) (v2 i)

-- @[simp]
-- theorem Vect.map_nil : Vect.map f v[] = v[] := by
--   funext; case _ x => apply Fin.elim0 x

-- @[simp]
-- theorem Vect.map_cons : Vect.map f (h::t) = (f h)::Vect.map f t := by
--   funext; case _ i =>
--   cases i using Fin.cases <;> simp [Vect.map]

-- @[simp]
-- theorem Vect.eta0 (t : Vect T 0) : t = v[] := by apply Vect.nil_singleton

-- @[simp]
-- theorem Vect.eta1 (t : Vect T 1) : v[t 0] = t := by
--   funext; case _ i =>
--   cases i using Fin.cases1; simp

-- @[simp]
-- theorem Vect.eta2 (t : Vect T 2) : v[t 0, t 1] = t := by
--   funext; case _ i =>
--   cases i using Fin.cases2 <;> simp

-- @[simp]
-- theorem Vect.inv1 {a b : Vect T 1} : a = b <-> a 0 = b 0 := by
--   apply Iff.intro; intro h; subst h; rfl
--   intro h; funext; case _ i =>
--   cases i using Fin.cases1; exact h

-- @[simp]
-- theorem Vect.inv2 {a b : Vect T 2} : a = b <-> a 0 = b 0 ∧ a 1 = b 1 := by
--   apply Iff.intro; intro h; subst h; simp
--   intro h; funext; case _ i =>
--   cases i using Fin.cases2 <;> simp [*]

-- def Vect.update (i : Fin n) (t : T) (ts : Vect T n) : Vect T n
-- | x => if i = x then t else ts x

-- @[simp]
-- theorem Vect.update_eq : update i t ts i = t := by simp [update]

-- theorem Vect.update_neq : ∀ j ≠ i, update i t ts j = ts j := by
--   simp [update]; intro j h1 h2
--   exfalso; apply h1; rw [h2]

-- theorem Vect.update_stable i t {ts ts' : Vect T n} :
--   (∀ j ≠ i, ts j = ts' j) ->
--   ∀ j ≠ i, ts j = update i t ts' j
-- := by
--   intro h1 j h2; simp [update, *]
--   intro h3; exfalso; apply h2; rw [h3]

theorem Vect.eta {v : Vect (n + 1) T} : v = (((v.head : T):: (v.tail : Vect n T)) : Vect (n + 1) T)  := by
  -- apply Vect.induction (A := T)
  --   (motive := λ n Q x => ∀ n', (p : n = n' + 1) ->
  --       by rw[p] at x; apply
  --       x = (((x.head : T) :: (x.tail : Vect n T))))


  sorry



def Vect.length (_ : Vect n A) : Nat := n

theorem Vect.length_bound : (v : Vect n A) -> v.length == n := by
  intro v
  unfold Vect.length
  induction n <;> (simp at *)

-- def Vect.fold2 (acc : A -> B -> C -> C) (d : C) : {n1 n2 : Nat} -> (n1 = n2) -> Vect A n1 -> Vect B n2 -> C
-- | 0, 0, rfl, _, _ => d
-- | _ + 1, _ + 1, h, va, vb =>
--   let (h1, tl1) := uncons va
--   let (h2, tl2) := uncons vb
--   acc h1 h2 (fold2 acc d (by cases h; rfl) tl1 tl2)

@[simp]
def Vect.sum : {n : Nat} -> Vect n Nat -> Nat
| 0, _ => 0
| _ + 1, ts => ts 0 + ts.drop.sum

-- @[simp]
-- def Vect.beq (beq : T -> T -> Bool) : {n1 n2 : Nat} -> (n1 = n2) -> Vect T n1 -> Vect T n2 -> Bool
-- | 0, 0, rfl, _, _ => true
-- | _ + 1, _ + 1, h, v1, v2 =>
--   let (h1, t1) := Vect.uncons v1
--   let (h2, t2) := Vect.uncons v2
--   beq h1 h2 && Vect.beq beq (by cases h; rfl) t1 t2

-- instance instBEq_Vect [BEq T] : BEq (Vect T n) where
--   beq := Vect.beq BEq.beq rfl

-- def Vect.rfl [BEq T] [ReflBEq T] : ∀ {v : Vect T n}, (v == v) = true := by
-- intro v
-- match n, v with
-- | 0, v => simp [instBEq_Vect] at *
-- | n + 1, v =>
--     simp [instBEq_Vect] at *
--     let (x, v') := v.uncons
--     simp at *; apply @Vect.rfl _ n _ _ v'

-- instance instReflBEq_Vect [BEq T] [ReflBEq T] : ReflBEq (Vect T n) where
--   rfl := Vect.rfl



-- @[simp]
-- theorem Vect.subst_cons {t : Vect S n} {σ : Subst T}
--   : ((h::t) i)[σ:T] = (h[σ:_]::map (·[σ:_]) t) i
-- := by
--   induction i using Fin.induction <;> simp at *
--   case _ i ih =>
--     cases n; apply Fin.elim0 i
--     case _ n =>
--     cases i using Fin.cases <;> simp [Vect.map] at *

def Vect.indexOf [BEq Q] (c : Q) {n : Nat} (v :  Vect n Q) : Option (Fin n) :=
match n with
| 0 => none
| n + 1 =>
    let (found, i, _) := Vect.fold (false, 0, 0) (λ x (found, found_idx, i) =>
      if not found
        then if x == c
                then (true, i, i + 1)
                else (found, found_idx, i + 1)
        else (found, found_idx, i + 1)
    )  v
    if found then return Fin.ofNat (n + 1) (n - i) else none

def Vect.indexOf_aux [BEq Q][LawfulBEq Q] (c : Q) (n : Nat) : Nat -> (Vect n Q) -> Option Nat := λ i v =>
match n, v with
| 0, _ => none
| n + 1, v' =>
    match v'.uncons with
    | ⟨x, v'⟩ => if x == c
      then i
      else (Vect.indexOf_aux c n (i + 1) v')

def Vect.indexOf' [BEq Q][LawfulBEq Q] (c : Q) (v : Vect n Q) : Option (Fin n) :=
match n with
| 0 => none
| n + 1 => (Vect.indexOf_aux c (n + 1) 0 v).map (Fin.ofNat (n + 1))


#guard Vect.indexOf "x" (["x", "y", "p"] : Vect 3 String) == some 0
#guard Vect.indexOf "y" (["x", "y", "p"] : Vect 3 String) == some 1
#guard Vect.indexOf "p" (["x", "y", "p"] : Vect 3 String) == some 2
#guard Vect.indexOf "z" (["x", "y", "p"] : Vect 3 String) == none

#guard Vect.indexOf' "x" (["x", "y", "p"] : Vect 3 String) == some 0
#guard Vect.indexOf' "y" (["x", "y", "p"] : Vect 3 String) == some 1
#guard Vect.indexOf' "p" (["x", "y", "p"] : Vect 3 String) == some 2
#guard Vect.indexOf' "z" (["x", "y", "p"] : Vect 3 String) == none

def Vect.HasUniqueElems [BEq Q] (v : Vect n Q) := ∀ i j, i ≠ j -> (v i) ≠ (v j)


theorem Vect.indexOf_correct [BEq Q] {v : Vect n Q} :
  v.indexOf x = some i ->
  (v i) = x := by
intro h
induction n <;> simp at *
case _ =>  cases i; simp [indexOf] at h
case _ n ih => sorry

theorem Vect.indexOf'_le [BEq Q] [LawfulBEq Q] {v : Vect n Q} :
  v.indexOf' x = some i ->
  i < n := by
intro h
induction n <;> simp at *
case _ => cases i; simp [indexOf'] at h

theorem Vect.indexOf'_aux_le [BEq Q] [LawfulBEq Q] {v : Vect n Q} :
  v.indexOf_aux x n 0 = some i ->
  i < n := by
intro j
induction n generalizing i
case _ => unfold Vect.indexOf_aux at j; cases j
case _ ih =>
  unfold Vect.indexOf_aux at j;
  split at j; simp at j;
  sorry



theorem Vect.indexOf'_correct [BEq Q] [LawfulBEq Q] {v : Vect n Q} :
  v.indexOf' x = some i ->
  v i = x := by
intro j; induction n
case _ => simp [indexOf'] at j
case _ n ih => sorry
  -- have lem := Vect.indexOf'_le j
  -- simp [indexOf', indexOf_aux] at *; rcases j with ⟨n, j1, j2⟩
  -- have ih' := ih (i := i + 1) (v := v.uncons.snd)
  -- split at j1
  -- case _ n _ _ =>
  --   simp [uncons] at *; subst j1;
  --   rw[Fin.ofNat_zero] at j2; subst j2; assumption
  -- case _ n _ _ => sorry




def Vect.seq_lemma (vs : Vect n (Option Q)) :
  (Σ' (i : Fin n), (vs i).isSome = false) ⊕ ((i : Fin n) -> Σ' A, (vs i) = some A)
:= by {
    induction n
    case _ =>
      apply Sum.inr; intro i
      apply Fin.elim0 i
    case _ n ih =>
      generalize zdef : uncons vs = z at *
      rcases z with ⟨h, t⟩
      have lem := Vect.uncons_iff.1 zdef
      cases h
      case none =>
        apply Sum.inl; apply PSigma.mk 0
        rw [lem]; simp
      case some h =>
        replace ih := ih t
        cases ih
        case _ ih =>
          rcases ih with ⟨k, ih⟩
          apply Sum.inl; apply PSigma.mk (Fin.succ k)
          rw [lem]; simp at *; exact ih
        case _ ih =>
          apply Sum.inr; intro i
          cases i using Fin.cases
          case _ => rw [lem]; simp; apply PSigma.mk h; rfl
          case _ i => rw [lem]; simp; apply ih i
  }

def Vect.seq (vs : Vect n (Option Q)) : Option (Vect n Q) :=
  match seq_lemma vs with
  | .inl h => none
  | .inr h => some (λ i => Option.get (vs i) (by {
    replace h := h i
    rcases h with ⟨t, e⟩
    rw [e]; simp
  }))

theorem Vect.seq_sound {vs : Vect n (Option Q)} {vs' : Vect n Q}:
  vs.seq = some vs' ->
  ∀ i, (vs i) = some (vs' i) := by
intro h i
-- simp [Vect.seq, Vect.seq_lemma] at h
match n with
| 0 => simp at *; cases i; omega
| n + 1 =>
  apply @Fin.inductionOn n i
  case _ =>
    simp [Vect.seq, Vect.seq_lemma] at h; split at h <;> simp at *
    case _ x h' heq =>
      cases x
      case _ =>
        sorry
      case _ => sorry
  case _ =>
    intro j h; simp at *
    simp [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE] at *;

    sorry



-- Returns the 1st element if all the elements are equal
def Vect.get_elem_if_eq [BEq Q] (vs : Vect n Q) : Option Q :=
match n with
| 0 => none
| _ + 1 =>  match vs.uncons with
  | ⟨h, vs'⟩ => do
    if vs'.fold true (λ c acc => c == h && acc)
    then return h else none

theorem Vect.get_elem_if_eq_sound [BEq Q] {vs : Vect n Q} {t : Q} :
  vs.get_elem_if_eq = some t ->
  ∀ i, vs i = t := by
intro h i
induction n <;> simp [Vect.get_elem_if_eq, Vect.uncons] at *
case _ n ih => sorry
  -- replace ih := @ih vs.drop
  -- split at ih <;> simp at *
  -- sorry
  -- revert i; rcases h with ⟨h1, h2⟩; sorry



def Vect.elems_eq_to [BEq Q] (e : Q) : {n : Nat} -> (vs : Vect n Q) -> Bool
| 0, _ => true
| _ + 1, vs =>
  match vs.uncons with
  | ⟨h, vs'⟩ =>
    if h == e then vs'.elems_eq_to e else false

theorem Vect.elems_eq_to_sound [BEq Q] {e : Q} {vs : Vect n Q} :
  vs.elems_eq_to e = true ->
  ∀ i, (vs i) = e := by sorry

theorem vec_size_1: Vect (0 + 1) Q = Vect 1 Q := by simp

-- theorem Vect.uncons_injective [BEq Q] : Function.Injective (α := Vect (n + 1) Q) (β := Q × Vect n Q) Vect.uncons := by
-- intro v1 v2; induction n
-- sorry
-- sorry
