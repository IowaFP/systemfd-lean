import LeanSubst

open LeanSubst

def Fin.cases1
  {motive : Fin 1 -> Prop}
  (h : motive 0)
  (v : Fin 1) : motive v
:= by
  induction v using Fin.induction; simp [*]
  case _ i _ => apply Fin.elim0 i

def Fin.cases2
  {motive : Fin 2 -> Prop}
  (h1 : motive 0) (h2 : motive 1)
  (v : Fin 2) : motive v
:= by
  induction v using Fin.induction; simp [*]
  case _ i h =>
    induction i using Fin.induction; simp [*]
    case _ i h => apply Fin.elim0 i

def Vec (T : Sort u) (n : Nat) := Fin n -> T

def Vec.nil : Vec T 0 := λ x => nomatch x

def Vec.cons (t : T) (xs : Vec T n) : Vec T (n + 1)
| n => if h : n = 0 then t else xs (Fin.pred n h)

infixr:55 "::" => Vec.cons

def Vec.drop : Vec T (n + 1) -> Vec T n
| v => λ i => v (Fin.succ i)

def Vec.uncons :  Vec T (n + 1) -> T × Vec T n
| v => (v 0, drop v)


protected def Vec.reprPrec [Repr T] : {n : Nat} -> Vec T n -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr (v 0)
| _ + 1, v, i =>
  let (h, t) := uncons v
  (repr h) ++ ", " ++ (Vec.reprPrec t i)

protected def Vec.reprPrec' (repr : T -> Std.Format) : {n : Nat} -> Vec T n -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr (v 0)
| _ + 1, v, i =>
  let (h, t) := uncons v
  (repr h) ++ ", " ++ (Vec.reprPrec' repr t i)


instance [Repr T] : Repr (Vec T n) where
  reprPrec v n := "v[" ++ Vec.reprPrec v n ++ "]"

syntax "v[" withoutPosition(term,*,?) "]"  : term

-- Adapted from Lean Prelude
macro_rules
| `(v[ $elems,* ]) => do
  let rec expandVecList (i : Nat) (result : Lean.TSyntax `term) : Lean.MacroM Lean.Syntax := do
    match i with
    | 0 => pure result
    | i + 1 => expandVecList i (<- ``(Vec.cons `$(⟨elems.getElems.get!Internal i⟩) $result))
  let size := elems.getElems.size
  expandVecList size (<- ``(Vec.nil))

-- Adapted from Lean Prelude
@[app_unexpander Vec.nil]
meta def unexpandVecNil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(v[])

-- Adapted from Lean Prelude
@[app_unexpander Vec.cons]
meta def unexpandVecCons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `(v[])      => `(v[$x])
  | `(v[$xs,*]) => `(v[$x, $xs,*])
  | `(⋯)       => `(v[$x, $tail]) -- Unexpands to `[x, y, z, ⋯]` for `⋯ : List α`
  | _          => throw ()
| _ => throw ()

@[simp]
theorem Vec.nil_singleton (v1 v2 : Vec T 0) : v1 = v2 := by
  funext; case _ i =>
  cases i; case _ i p => cases p

@[simp]
theorem Vec.uncons_cons_cancel : uncons (h::t) = (h, t) := by
  simp [uncons, drop]; case _ n =>
  apply And.intro _ _
  case _ =>
    cases n <;> simp [cons]
  case _ =>
    funext; case _ i =>
    cases i; case _ i p =>
    cases i <;> simp [cons, Fin.pred]

@[simp]
theorem Vec.head_drop_cancel : v 0 :: drop v = v := by
  funext; case _ i =>
  cases i; case _ i p =>
  cases i <;> simp [cons, drop]

theorem Vec.cons_iff_uncons {t : Vec T n} : v = h::t <-> uncons v = (h, t) := by
  apply Iff.intro
  case _ => intro e; subst e; simp
  case _ =>
    intro e; simp [uncons] at e
    cases e; case _ e1 e2 =>
    subst e1; subst e2; simp


def Vec.induction
  {motive : {n : Nat} -> Vec T n -> Sort u}
  (nc : motive Vec.nil)
  (cc : ∀ {n t} {v : Vec T n}, motive v -> motive (t::v))
  (v : Vec T n)
  : motive v
:= by
  induction n
  case _ => rw [nil_singleton v]; exact nc
  case _ n ih =>
    generalize zdef : uncons v = z at *
    rcases z with ⟨h, t⟩
    have lem := cons_iff_uncons.2 zdef
    rw [lem]; apply cc (ih t)


-- theorem Vec.induction1
--   {motive : Vec T 1 -> Prop}
--   (h : ∀ {t : T}, motive v[t])

@[simp]
instance : GetElem (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := xs i

@[simp]
instance : GetElem? (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem? xs i := .some (xs i)

@[simp]
theorem get_cons_head {t : Vec T n} : (h::t) 0 = h := by simp [Vec.cons]

@[simp]
theorem get_cons_tail_succ {t : Vec T n} : (h::t) (Fin.succ i) = t i := by
  simp [Vec.cons]; intro h; cases h

@[simp]
theorem get1_0 : v[a] 0 = a := by simp

@[simp]
theorem get2_0 : v[a, b] 0 = a := by simp

@[simp]
theorem get2_1 : v[a, b] 1 = b := by simp [Vec.cons]

def Vec.map (f : A -> B) (v : Vec A n) : Vec B n := λ i => f (v i)

@[simp]
def Vec.map2 (v1 : Vec A n) (v2 : Vec B n) (f : A -> B -> C)  : Vec C n := λ i => f (v1 i) (v2 i)

@[simp]
theorem Vec.map_nil : Vec.map f v[] = v[] := by
  funext; case _ x => apply Fin.elim0 x

@[simp]
theorem Vec.map_cons : Vec.map f (h::t) = (f h)::Vec.map f t := by
  funext; case _ i =>
  cases i using Fin.cases <;> simp [Vec.map]

@[simp]
theorem Vec.eta0 (t : Vec T 0) : t = v[] := by apply Vec.nil_singleton

@[simp]
theorem Vec.eta1 (t : Vec T 1) : v[t 0] = t := by
  funext; case _ i =>
  cases i using Fin.cases1; simp

@[simp]
theorem Vec.eta2 (t : Vec T 2) : v[t 0, t 1] = t := by
  funext; case _ i =>
  cases i using Fin.cases2 <;> simp

@[simp]
theorem Vec.inv1 {a b : Vec T 1} : a = b <-> a 0 = b 0 := by
  apply Iff.intro; intro h; subst h; rfl
  intro h; funext; case _ i =>
  cases i using Fin.cases1; exact h

@[simp]
theorem Vec.inv2 {a b : Vec T 2} : a = b <-> a 0 = b 0 ∧ a 1 = b 1 := by
  apply Iff.intro; intro h; subst h; simp
  intro h; funext; case _ i =>
  cases i using Fin.cases2 <;> simp [*]

def Vec.update (i : Fin n) (t : T) (ts : Vec T n) : Vec T n
| x => if i = x then t else ts x

@[simp]
theorem Vec.update_eq : update i t ts i = t := by simp [update]

theorem Vec.update_neq : ∀ j ≠ i, update i t ts j = ts j := by
  simp [update]; intro j h1 h2
  exfalso; apply h1; rw [h2]

theorem Vec.update_stable i t {ts ts' : Vec T n} :
  (∀ j ≠ i, ts j = ts' j) ->
  ∀ j ≠ i, ts j = update i t ts' j
:= by
  intro h1 j h2; simp [update, *]
  intro h3; exfalso; apply h2; rw [h3]

-- def Vec.fold (acc : A -> B -> B) (d : B) : Vec A n -> B :=
--   Vec.induction (motive := λ _ => B) d (@fun _ hd _ ih => acc hd ih)

def Vec.fold (acc : A -> B -> B) (d : B) : {n : Nat} -> Vec A n -> B
| 0, _ => d
| _ + 1, vs =>
  let (h, tl) := uncons vs
  acc h (fold acc d tl)


@[simp]
theorem Vec.fold_nil : fold acc d Vec.nil = d := by simp [fold]

@[simp]
theorem Vec.fold_cons : fold acc d (hd :: tl) = acc hd (fold acc d tl) := by simp [fold]

def Vec.length (_ : Vec A n) : Nat := n

theorem Vec.length_bound : (v : Vec A n) -> v.length == n := by
  intro v
  unfold Vec.length
  induction n <;> (simp at *)

def Vec.fold2 (acc : A -> B -> C -> C) (d : C) : {n1 n2 : Nat} -> (n1 = n2) -> Vec A n1 -> Vec B n2 -> C
| 0, 0, rfl, _, _ => d
| _ + 1, _ + 1, h, va, vb =>
  let (h1, tl1) := uncons va
  let (h2, tl2) := uncons vb
  acc h1 h2 (fold2 acc d (by cases h; rfl) tl1 tl2)

@[simp]
def Vec.sum : {n : Nat} -> Vec Nat n -> Nat
| 0, _ => 0
| _ + 1, ts => ts 0 + ts.drop.sum

@[simp]
def Vec.beq (beq : T -> T -> Bool) : {n1 n2 : Nat} -> (n1 = n2) -> Vec T n1 -> Vec T n2 -> Bool
| 0, 0, rfl, _, _ => true
| _ + 1, _ + 1, h, v1, v2 =>
  let (h1, t1) := Vec.uncons v1
  let (h2, t2) := Vec.uncons v2
  beq h1 h2 && Vec.beq beq (by cases h; rfl) t1 t2

instance instBEq_Vec [BEq T] : BEq (Vec T n) where
  beq := Vec.beq BEq.beq rfl

def Vec.rfl [BEq T] [ReflBEq T] : ∀ {v : Vec T n}, (v == v) = true := by
intro v
match n, v with
| 0, v => simp [instBEq_Vec] at *
| n + 1, v =>
    simp [instBEq_Vec] at *
    let (x, v') := v.uncons
    simp at *; apply @Vec.rfl _ n _ _ v'

instance instReflBEq_Vec [BEq T] [ReflBEq T] : ReflBEq (Vec T n) where
  rfl := Vec.rfl


variable {S T : Type} [RenMap T] [SubstMap S T]

@[simp]
theorem Vec.subst_cons {t : Vec S n} {σ : Subst T}
  : ((h::t) i)[σ:T] = (h[σ:_]::map (·[σ:_]) t) i
:= by
  induction i using Fin.induction <;> simp at *
  case _ i ih =>
    cases n; apply Fin.elim0 i
    case _ n =>
    cases i using Fin.cases <;> simp [Vec.map] at *

omit [RenMap T] [SubstMap S T] in
def Vec.indexOf [BEq Q] (c : Q) {n : Nat} (v :  Vec Q n) : Option (Fin n) :=
match n with
| 0 => none
| n + 1 =>
    let (found, i, _) := Vec.fold (λ x (found, found_idx, i) =>
      if not found
        then if x == c
                then (true, i, i + 1)
                else (found, found_idx, i + 1)
        else (found, found_idx, i + 1)
    ) (false, 0, 0) v
    if found then return Fin.ofNat (n + 1) (n - i) else none

def Vec.indexOf_aux [BEq Q][LawfulBEq Q] (c : Q) (n : Nat) : Nat -> (Vec Q n) -> Option Nat := λ i v =>
match n, v with
| 0, _ => none
| n + 1, v' =>
    match v'.uncons with
    | (x, v') => if x == c
      then i
      else (Vec.indexOf_aux c n (i + 1) v')

def Vec.indexOf' [BEq Q][LawfulBEq Q] (c : Q) (v : Vec Q n) : Option (Fin n) :=
match n with
| 0 => none
| n + 1 => (Vec.indexOf_aux c (n + 1) 0 v).map (Fin.ofNat (n + 1))


#guard Vec.indexOf "x" v["x", "y", "p"] == some 0
#guard Vec.indexOf "y" v["x", "y", "p"] == some 1
#guard Vec.indexOf "p" v["x", "y", "p"] == some 2
#guard Vec.indexOf "z" v["x", "y", "p"] == none

#guard Vec.indexOf' "x" v["x", "y", "p"] == some 0
#guard Vec.indexOf' "y" v["x", "y", "p"] == some 1
#guard Vec.indexOf' "p" v["x", "y", "p"] == some 2
#guard Vec.indexOf' "z" v["x", "y", "p"] == none

def Vec.HasUniqueElems [BEq Q] (v : Vec Q n) := ∀ i j, i ≠ j -> (v i) ≠ (v j)


theorem Vec.indexOf_correct [BEq Q] {v : Vec Q n} :
  v.indexOf x = some i ->
  (v i) = x := by
intro h
induction n <;> simp at *
case _ =>  cases i; simp [indexOf] at h
case _ n ih =>
  match v.uncons with
  | (_, v') =>
    sorry

theorem Vec.indexOf'_le [BEq Q] [LawfulBEq Q] {v : Vec Q n} :
  v.indexOf' x = some i ->
  i < n := by
intro h
induction n <;> simp at *
case _ => cases i; simp [indexOf'] at h

theorem Vec.indexOf'_aux_le [BEq Q] [LawfulBEq Q] {v : Vec Q n} :
  v.indexOf_aux x n 0 = some i ->
  i < n := by
intro j
induction n generalizing i
case _ => unfold Vec.indexOf_aux at j; cases j
case _ ih =>
  unfold Vec.indexOf_aux at j;
  split at j; simp at j;
  sorry



theorem Vec.indexOf'_correct [BEq Q] [LawfulBEq Q] {v : Vec Q n} :
  v.indexOf' x = some i ->
  v i = x := by
intro j; induction n
case _ => simp [indexOf'] at j
case _ n ih => sorry
  -- have lem := Vec.indexOf'_le j
  -- simp [indexOf', indexOf_aux] at *; rcases j with ⟨n, j1, j2⟩
  -- have ih' := ih (i := i + 1) (v := v.uncons.snd)
  -- split at j1
  -- case _ n _ _ =>
  --   simp [uncons] at *; subst j1;
  --   rw[Fin.ofNat_zero] at j2; subst j2; assumption
  -- case _ n _ _ => sorry




def Vec.seq_lemma (vs : Vec (Option Q) n) :
  (Σ' (i : Fin n), (vs i).isSome = false) ⊕ ((i : Fin n) -> Σ' A, (vs i) = some A)
:= by {
    induction n
    case _ =>
      apply Sum.inr; intro i
      apply Fin.elim0 i
    case _ n ih =>
      generalize zdef : uncons vs = z at *
      rcases z with ⟨h, t⟩
      have lem := cons_iff_uncons.2 zdef
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

def Vec.seq (vs : Vec (Option Q) n) : Option (Vec Q n) :=
  match seq_lemma vs with
  | .inl h => none
  | .inr h => some (λ i => Option.get (vs i) (by {
    replace h := h i
    rcases h with ⟨t, e⟩
    rw [e]; simp
  }))

theorem Vec.seq_sound {vs : Vec (Option Q) n} {vs' : Vec Q n}:
  vs.seq = some vs' ->
  ∀ i, (vs i) = some (vs' i) := by
intro h i
-- simp [Vec.seq, Vec.seq_lemma] at h
match n with
| 0 => simp at *; cases i; omega
| n + 1 =>
  apply @Fin.inductionOn n i
  case _ =>
    simp [Vec.seq, Vec.seq_lemma] at h; split at h <;> simp at *
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
def Vec.get_elem_if_eq [BEq Q] (vs : Vec Q n) : Option Q :=
match n with
| 0 => none
| _ + 1 =>  match vs.uncons with
  | (h, vs') => do
    if vs'.fold (λ c acc => c == h && acc) true
    then return h else none

theorem Vec.get_elem_if_eq_sound [BEq Q] {vs : Vec Q n} {t : Q} :
  vs.get_elem_if_eq = some t ->
  ∀ i, vs i = t := by
intro h i
induction n <;> simp [Vec.get_elem_if_eq, Vec.uncons] at *
case _ n ih =>
  replace ih := @ih vs.drop
  split at ih <;> simp at *
  sorry
  revert i; rcases h with ⟨h1, h2⟩; sorry



def Vec.elems_eq_to [BEq Q] (e : Q) : {n : Nat} -> (vs : Vec Q n) -> Bool
| 0, _ => true
| _ + 1, vs =>
  match vs.uncons with
  | (h, vs') =>
    if h == e then vs'.elems_eq_to e else false

theorem Vec.elems_eq_to_sound [BEq Q] {e : Q} {vs : Vec Q n} :
  vs.elems_eq_to e = true ->
  ∀ i, (vs i) = e := by sorry

theorem vec_size_1 [BEq Q]: Vec Q (0 + 1) = Vec Q 1 := by simp

theorem Vec.uncons_injective [BEq Q] : Function.Injective (α := Vec Q (n + 1)) (β := Q × Vec Q n) Vec.uncons := by
intro v1 v2; induction n
sorry
sorry
