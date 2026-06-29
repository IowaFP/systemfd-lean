
import Lilac.Vec.Encoding

namespace Lilac

inductive Vec (α : Sort u) : Nat -> Sort (imax u 1) where
| nil : Vec α 0
| cons {n} : α -> Vec α n -> Vec α (n + 1)

notation "#()" => Vec.nil
infixr:67 (name := vec_cons) " :: " => Vec.cons

protected def Vec.repr {α n} [Repr α] (v : Vec α n) (p : Nat) : Std.Format :=
  "#(" ++ go v p ++ ")"
where
  go {α n} [Repr α] : Vec α n -> Nat -> Std.Format
  | #(), _ => ""
  | x::#(), p => repr x
  | x::xs, p => repr x ++ "," ++ go xs p

instance {n} {α : Type u} [Repr α] : Repr (Vec α n) where
  reprPrec := Vec.repr

-- Syntax adapted from Lean Prelude
----------------------------------------------------------------------------------------------------

syntax (name := «term#(_,)») "#(" withoutPosition(term,*,?) ")" : term
-- ⟨elems.getElems[i]!⟩
open Lean in
macro_rules
  | `(#( $elems,* )) => do
    let rec expand_vec_lit (i : Nat) (skip : Bool) (result : TSyntax `term) : MacroM Syntax := do
      match i, skip with
      | 0,     _     => pure result
      | i + 1, true  => expand_vec_lit i false result
      | i + 1, false => expand_vec_lit i true  (<- ``(Vec.cons $(⟨elems.elemsAndSeps[i]!⟩) $result))
    let size := elems.elemsAndSeps.size
    if size < 64 then
      expand_vec_lit size (size % 2 == 0) (<- ``(Vec.nil))
    else
      `(%[ $elems,* | Vec.nil ])

@[app_unexpander Vec.nil]
meta def Vec.unexpand_nil : Lean.PrettyPrinter.Unexpander
| `($(_)) => `(#())

@[app_unexpander Vec.cons]
meta def Vec.unexpand_cons : Lean.PrettyPrinter.Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `([])      => `(#($x))
  | `([$xs,*]) => `(#($x, $xs,*))
  | `(⋯)       => `(#($x, $tail))
  | _          => throw ()
| _ => throw ()

----------------------------------------------------------------------------------------------------

@[coe]
def Fun.Vec.to {α n} (v : Lilac.Fun.Vec α n) : Lilac.Vec α n :=
  @induction α (λ n _ => Lilac.Vec α n) Lilac.Vec.nil (λ hd _ tl => Lilac.Vec.cons hd tl) _ v

@[simp]
instance {α n} : Coe (Lilac.Fun.Vec α n) (Lilac.Vec α n) where
  coe := Fun.Vec.to

@[simp]
def Vec.to {α n} : Vec α n -> Fun.Vec α n
| #() => .nil
| x::xs => .cons x xs.to

@[simp]
def Vec.list {α n} : Vec α n -> List α
| #() => []
| x::xs => x::xs.list

def Vec.has_dec_eq {α n} [DecidableEq α] : (a b : Vec α n) -> Decidable (a = b) := sorry

instance {α n} [DecidableEq α] : DecidableEq (Vec α n) := Vec.has_dec_eq

@[reducible, simp]
def Vec.length {α n} (_ : Vec α n) : Nat := n

@[simp]
def Vec.head {α} : ∀ {n : Nat} [NeZero n], Vec α n -> α
| 0, i, #() => i.out rfl |> False.elim
| _, _, x::_ => x

@[simp]
def Vec.tail {α} : ∀ {n : Nat} [NeZero n], Vec α n -> Vec α (n - 1)
| 0, i, #() => i.out rfl |> False.elim
| _, _, _::xs => xs

def Vec.get {α n} : Vec α n -> Fin n -> α
| x::xs, i => Fin.cases x xs.get i

instance {α n} : GetElem (Vec α n) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := Vec.get xs i

def Vec.set {α n} : Vec α n -> Fin n -> α -> Vec α n
| x::xs, i, a => Fin.cases (a::xs) (λ i => x::(xs.set i a)) i

@[simp]
def Vec.foldl {α : Type u} {β : Type v} {n} (f : α -> β -> α) (init : α) : Vec β n -> α
| #() => init
| x::xs => foldl f (f init x) xs

@[simp]
def Vec.foldr {α : Type u} {β : Type v} {n} (f : α -> β -> β) (init : β) : Vec α n -> β
| #() => init
| x::xs => f x (foldr f init xs)

@[simp]
def Vec.concat {α n} : Vec α n -> α -> Vec α (n + 1)
| #(), a => a::#()
| x::xs, a => x::(concat xs a)

/--
We intentionally flip the addition order to avoid `cast`ing and obtain better simplification
-/
def Vec.append {α n m} : Vec α n -> Vec α m -> Vec α (m + n)
| #(), ys => ys
| x::xs, ys => x::(xs.append ys)

instance {α : Type u} {n m : Nat} : HAppend (Vec α n) (Vec α m) (Vec α (m + n)) where
  hAppend := Vec.append

@[simp]
def Vec.flatten {α n m} : Vec (Vec α n) m -> Vec α (n * m)
| #() => #()
| x::xs => x ++ xs.flatten |> cast (by grind)

@[simp]
def Vec.map {α : Type u} {β : Type b} {n} (f : α -> β) : Vec α n -> Vec β n
| #() => #()
| x::xs => (f x)::(xs.map f)

instance {n} : Functor (λ α => Vec α n) where
  map := Vec.map

@[simp]
def Vec.beq {α n m} [BEq α] : Vec α n -> Vec α m -> Bool
| #(), #() => true
| x::xs, y::ys => x == y && beq xs ys
| _, _ => false

instance {α n} [BEq α] : BEq (Vec α n) := ⟨Vec.beq⟩

@[simp]
def Vec.replicate {α} : (n : Nat) -> (a : α) -> Vec α n
| 0, _ => #()
| n + 1, a => a::replicate n a

@[simp, reducible]
instance {α} : Inhabited (Vec α 0) where
  default := #()

@[simp, reducible]
instance {α n} [Inhabited α] : Inhabited (Vec α n) where
  default := Vec.replicate n default

@[simp]
def Vec.reverse {α n} : Vec α n -> Vec α n
| #() => #()
| x::xs => concat xs.reverse x

def Vec.contains {α n} [BEq α] (a : α) : Vec α n -> Bool
| #() => false
| x::xs => x == a || contains a xs

def Vec.take {α m} : (n : Nat) -> (h : n ≤ m) -> Vec α m -> Vec α n
| _, h, #() => (#() : Vec α 0) |> cast (by cases h; simp)
| 0, h, v => #()
| n + 1, h, x::xs => x::xs.take n (by grind)

def Vec.drop {α m} : (n : Nat) -> (h : n ≤ m) -> Vec α m -> Vec α (m - n)
| _, h, #() => (#() : Vec α 0) |> cast (by cases h; simp)
| 0, h, v => v
| n + 1, h, x::xs => xs.drop n (by grind) |> cast (by grind)

def Vec.any {α n} : Vec α n -> (p : α -> Bool) -> Bool
| #(), _ => false
| x::xs, p => p x || xs.any p

def Vec.all {α n} : Vec α n -> (p : α -> Bool) -> Bool
| #(), _ => true
| x::xs, p => p x && xs.any p

@[simp]
def Vec.zipWith {α : Type u} {β : Type v} {γ : Type w} {n} (f : α -> β -> γ)
  : Vec α n -> Vec β n -> Vec γ n
| #(), #() => #()
| x::xs, y::ys => f x y::zipWith f xs ys

def Vec.zip {α : Type u} {β : Type v} {n} (v1 : Vec α n) (v2 : Vec β n) : Vec (α × β) n :=
  zipWith (· , ·) v1 v2

def Vec.unzip {α : Type u} {β : Type v} {n} : Vec (α × β) n -> (Vec α n) × (Vec β n)
| #() => (#(), #())
| (a, b)::xs =>
  let (as, bs) := xs.unzip
  (a::as, b::bs)

@[simp]
def Vec.range : (n : Nat) -> (k : Nat := 0) -> Vec Nat n
| 0, _ => #()
| n + 1, k => k::(range n (k + 1))

@[simp]
def Vec.zipIdx {α n} : Vec α n -> (k : Nat := 0) -> Vec (α × Nat) n
| #(), _ => #()
| x::xs, k => (x, k)::xs.zipIdx (k + 1)

@[simp]
def Vec.find? {α n} (p : α -> Bool) : Vec α n -> Option α
| #() => none
| x::xs => if p x then x else xs.find? p

def Vec.findIdx? {α n} (p : α -> Bool) : Vec α n -> Option (Fin n)
| #() => none
| x::xs => go (x::xs) 0
where
  go : {n : Nat} -> Vec α n -> Nat -> Option (Fin n)
  | _, #(), _ => none
  | n + 1, x::xs, i => if p x then Fin.ofNat (n + 1) i else Fin.succ <$> go xs i

def Vec.erase {α} [BEq α] : {n : Nat} -> Vec α n -> α -> (m : Nat) × Vec α m ×' (n ≤ m + 1)
| 0, #(), _ => ⟨0, #(), by grind⟩
| n + 1, x::xs, a =>
  match x == a with
  | true => ⟨n, xs, by grind⟩
  | false =>
    let ⟨m, xs', h⟩ := erase xs a
    ⟨m + 1, x::xs', by grind⟩

@[simp]
def Vec.count {α n} [BEq α] (a : α) : Vec α n -> Nat
| #() => 0
| x::xs => xs.count a + (if x == a then 1 else 0)

@[simp]
def Vec.traverse {m α β n} [Applicative m] (f : α -> m β) : Vec α n -> m (Vec β n)
| #() => pure #()
| x::xs => cons <$> f x <*> traverse f xs

def Vec.sequence {m α n} [Applicative m] : Vec (m α) n -> m (Vec α n) := traverse id

@[simp]
def Vec.sum {n} : Vec Nat n -> Nat
| #() => 0
| x::xs => xs.sum + x

inductive Vec.Mem {α} (x : α) : {n : Nat} -> Vec α n -> Prop where
| head {xs} : Mem x (x::xs)
| tail (y : α) {xs} : Mem x xs -> Mem x (y::xs)

instance {α n} : Membership α (Vec α n) where
  mem v x := Vec.Mem x v

end Lilac
