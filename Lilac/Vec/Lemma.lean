import Lilac.Vec.Basic

namespace Lilac

/-!
  # Vec Lemmas
  TODO: Header
-/

/-! ## Fun.Vec.to -/

@[simp]
theorem Fun.Vec.to_nil {α} : to (nil : Vec α 0) = .nil := rfl

@[simp]
theorem Vec.to_nil {α} : (Vec.to (#() : Vec α 0)) = (.nil : Fun.Vec α 0) := rfl

@[simp]
theorem Fun.Vec.to_cons {α n hd} {tl : Vec α n} : to (cons hd tl) = .cons hd tl.to := rfl

@[simp]
theorem Fun.Vec.to_iso {α n} {v : Fun.Vec α n} : v.to.to = v := by
  induction v using Fun.Vec.induction
  case nil => rfl
  case cons ih => simp [ih]

/-! ## to -/

@[simp]
theorem Vec.to_iso {α n} : {v : Vec α n} -> v.to.to = v
| #() => rfl
| x::xs => by simp [to_iso]

/-! ## append -/

@[simp]
theorem Vec.append_nil_left {α n} {v : Vec α n} : (#() : Vec α 0) ++ v = v := rfl

@[simp]
theorem Vec.append_cons {α n1 n2 x} {v1 : Vec α n1} {v2 : Vec α n2} : (x::v1) ++ v2 = x::(v1 ++ v2) := rfl

@[simp, grind =]
theorem Vec.append_nil_right {α n} : {v : Vec α n} → v ++ (#() : Vec α 0) ≍ v
| #() => by simp
| x::xs => by simp ; grind [@append_nil_right _ _ xs]

@[simp, grind =]
theorem Vec.append_assoc {α n1 n2 n3}
  : {v1 : Vec α n1} → {v2 : Vec α n2} → {v3 : Vec α n3} → (v1 ++ v2) ++ v3 ≍ v1 ++ (v2 ++ v3)
| #(), _, _ => by simp
| _, #(), _ => by simp ; grind
| _, _, #() => by grind
| x::xs, ys, zs => by simp ; grind [@append_assoc _ _ _ _ xs ys zs]

/-! ## list -/

@[simp]
theorem Vec.list_tail {n α} : [NeZero n] → {v : Vec α n} → v.tail.list = v.list.tail
| _, #() => by simp ; norm_cast
| _, _::_ => rfl

@[simp]
theorem Vec.list_set {α a} : {n : Nat} → {i : Fin n} → {v : Vec α n} → (v.set i a).list = v.list.set i a
| 0, i, #() => by grind
| n + 1, i, (x::xs) => Fin.cases (by simp [set]) (fun i' ↦ by simp [set, list_set]) i

@[simp]
theorem Vec.list_concat {α n x} : {v : Vec α n} → (v.concat x).list = v.list.concat x
| #() => rfl
| x::xs => by simp [list_concat]

@[simp]
theorem Vec.list_append {α n m} : {v1 : Vec α n} → {v2 : Vec α m} → (v1 ++ v2).list = v1.list ++ v2.list
| #(), v => rfl
| v, #() => by simp ; grind
| x::xs, v => by simp [list_append]

@[simp]
theorem Vec.list_flatten {α n m} : {v : Vec (Vec α n) m} → v.flatten.list = (list <$> v.list).flatten
| #() => rfl
| x::xs => by simp [flatten, list, Functor.map, list_flatten]

@[simp]
theorem Vec.list_map {α β n} {f : α -> β} : {v : Vec α n} → (v.map f).list = v.list.map f
| #() => rfl
| x::xs => by simp [map, list_map]

@[simp]
theorem Vec.list_replicate {x : Nat} : {n : Nat} → (replicate n x).list = List.replicate n x
| 0 => rfl
| n + 1 => by simp [replicate, List.replicate, list_replicate]

@[simp]
theorem Vec.list_reverse {α n} : {v : Vec α n} → v.reverse.list = v.list.reverse
| #() => rfl
| x::xs => by simp [reverse, list_reverse]

@[simp]
theorem Vec.list_take {α} : {n k : Nat} → {h : k ≤ n} → {v : Vec α n} → (v.take k h).list = v.list.take k
| 0, k, h, #() => by grind [take, list]
| n + 1, 0, h, x::xs => rfl
| n + 1, k + 1, h, x::xs => by simp [take, list_take]

@[simp]
theorem Vec.list_cast {α : Type u} : {m n : Nat} → {h : m = n} → {v : Vec α m} → (cast ((by grind) : Vec α m = Vec α n) v).list = v.list
| 0, n, h, #() => by grind
| m + 1, n, h, x::xs => by grind

@[simp]
theorem Vec.list_drop {α : Type u} : {m n : Nat} -> {v : Vec α m} -> {h : n ≤ m} -> (v.drop n h).list = v.list.drop n
| _, 0, v, _ => by cases v <;> simp [drop, List.drop]
| m + 1, n + 1, x::xs, h => by simp [list, drop, ← @list_drop _ _ n xs (by omega)]

@[simp]
theorem Vec.list_zipWith {α β γ n} {f : α -> β -> γ}
  : {v1 : Vec α n} → {v2 : Vec β n} → (zipWith f v1 v2).list = List.zipWith f v1.list v2.list
| #(), #() => rfl
| x::xs, y::ys => by simp [zipWith, list_zipWith]

@[simp]
theorem Vec.list_zip {α β n} : {v1 : Vec α n} → {v2 : Vec β n} → (zip v1 v2).list = List.zip v1.list v2.list
| #(), #() => rfl
| x::xs, y::ys => by simp [zip, ← list_zip]

@[simp]
theorem Vec.list_zipIdx {α n k} : {v : Vec α n} → (v.zipIdx k).list = v.list.zipIdx k
| #() => rfl
| x::xs => by simp [zipIdx, list_zipIdx]

@[simp]
theorem Vec.list_range {k} : (n : Nat) → (range n k).list = List.range' k n 1
| 0 => by simp
| n + 1 => by simp [range, list_range, List.range']

@[grind .]
theorem Vec.list_of_at_least_one_nonempty {α n} : {v : Vec α (n + 1)} → v.list ≠ []
| x::xs => by simp

/-! ## length
Vec carries its own length, hence why length is marked reducible.
This also means that most operations on length are trivial and the simplifier will reject them.
-/

theorem Vec.length_to {α n} {v : Fun.Vec α n} : v.to.length = n := rfl

@[simp]
theorem Vec.length_tail {α n} [NeZero n] {v : Vec α n} : v.tail.length = n - 1 := rfl

theorem Vec.length_set {α n i x} {v : Vec α n} : (v.set i x).length = n := rfl

@[simp]
theorem Vec.length_concat {α n x} {v : Vec α n} : (v.concat x).length = n + 1 := rfl

@[simp]
theorem Vec.length_append {α n m} {v1 : Vec α n} {v2 : Vec α m} : (v1 ++ v2).length = n + m := by grind

@[simp]
theorem Vec.length_flatten {α n m} {v : Vec (Vec α n) m} : v.flatten.length = n * m := rfl

theorem Vec.length_map {α β n} {f : α -> β} {v : Vec α n} : (v.map f).length = n := rfl

theorem Vec.length_reverse {α n} {v : Vec α n} : v.reverse.length = n := rfl

theorem Vec.length_take {α m n h} {v : Vec α m} : (v.take n h).length = n := rfl

@[simp]
theorem Vec.length_drop {α m n h} {v : Vec α m} : (v.drop n h).length = m - n := rfl

theorem Vec.length_zipWith {α β γ n} {f : α -> β -> γ} {v1 : Vec α n} {v2 : Vec β n} : (zipWith f v1 v2).length = n := rfl

theorem Vec.length_zip {α β n} {v1 : Vec α n} {v2 : Vec β n} : (zip v1 v2).length = n := rfl

theorem Vec.length_range {n k} : (range n k).length = n := rfl

theorem Vec.length_zipIdx {α n k} {v : Vec α n} : (v.zipIdx k).length = n := rfl

/-! ## get -/

@[simp]
theorem Vec.get_cons_zero {α n x} {xs : Vec α n} : (x::xs)[(0 : Fin (n + 1))] = x := by simp [getElem, get]

@[simp]
theorem Vec.get_cons_succ {α n x} {xs : Vec α n} {i : Fin n} : (x::xs)[Fin.succ i] = xs[i] := by simp [getElem, get]

@[grind =]
theorem Vec.get_set_neq {α} : {n : Nat} → {i j : Fin n} → (h : i ≠ j) → {a : α} → {v : Vec α n} → (v.set i a)[j] = v[j]
| 0, _, _, _, _, #() => by omega
| n + 1, ⟨i + 1, _⟩, ⟨0, _⟩, h, a, x::xs => rfl
| n + 1, ⟨0, _⟩, ⟨j + 1, _⟩, h, a, x::xs => rfl
| n + 1, ⟨i + 1, _⟩, ⟨j + 1, _⟩, h, a, x::xs => by
  have ih := @get_set_neq _ n ⟨i, by omega⟩ ⟨j, by omega⟩ (by grind) a xs
  simp_all [set, getElem, get]

@[simp]
theorem Vec.get_set_eq {α a} : {n : Nat} → {i : Fin n} → {v : Vec α n} → (v.set i a)[i] = a
| n + 1, ⟨0, _⟩, x::xs => by simp [set, getElem, get]
| n + 1, ⟨i + 1, _⟩, x::xs => by
  have ih := @get_set_eq _ a n ⟨i, by omega⟩ xs
  simp_all [set, getElem, get]

@[grind =]
theorem Vec.get_concat_castLT {α a}
  : {n : Nat} → {i : Fin (n + 1)} → (h : i ≠ n) → {v : Vec α n} → (v.concat a)[i] = v[i.castLT ((by omega) : i < n)]
| 0, _, _, #() => by grind
| n + 1, ⟨0, _⟩, h, x::xs => rfl
| n + 1, ⟨i + 1, _⟩, h, x::xs => by
  have ih := @get_concat_castLT _ a n ⟨i, by omega⟩ (by grind) xs
  norm_cast

@[grind =]
theorem Vec.get_concat_castSucc {α a n} : {i : Fin n} → {v : Vec α n} → (v.concat a)[i.castSucc] = v[i]
| i, #() => by grind
| i , x::xs => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [get_concat_castSucc]

@[grind =]
theorem Vec.get_append_lt {α}
  : {n m : Nat} → {v1 : Vec α n} → {v2 : Vec α m} → {i : Fin (m + n)} → (h : i < n) → (v1 ++ v2)[i] = v1[i.castLT h]
| 0, _, #(), _, i, h => by grind
| n + 1, m, x::xs, ys, ⟨0, _⟩, h => by simp [get, getElem, Fin.castLT]
| n + 1, m, x::xs, ys, ⟨i + 1, _⟩, h => by
  have ih := @get_append_lt _ n m xs ys ⟨i, by omega⟩ (by grind)
  simp_all [getElem, get]

theorem Vec.get_append_ge {α}
  : {n m : Nat} → {v1 : Vec α n} → {v2 : Vec α m} → {i : Fin (m + n)} → (h : i ≥ n) → (v1 ++ v2)[i] = v2[Fin.subNat n (i.cast (by omega) : Fin (m + n)) h]
| 0, _, #(), _, i, h => by simp
| n + 1, m, x::xs, ys, ⟨0, _⟩, h => by grind [get, getElem, Fin.subNat]
| n + 1, m, x::xs, ys, ⟨i + 1, _⟩, h => by
  have ih := @get_append_ge _ n m xs ys ⟨i, by omega⟩ (by grind)
  simp_all [Fin.subNat, getElem, get]

@[simp]
theorem Vec.get_map {α β} {f : α -> β} : {n : Nat} → {v : Vec α n} → {i : Fin n} → (v.map f)[i] = f v[i]
| n + 1, x::xs, i => by
  cases i using Fin.cases
  case zero => simp [getElem, get]
  case succ i' => simp [@get_map _ _ f n xs i']

@[simp]
theorem Vec.get_replicate {α} {x : α} : {n : Nat} → {i : Fin n} → (replicate n x)[i] = x
| n + 1, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [get_replicate]

@[simp]
theorem Vec.get_cons_last {α n x} : {xs : Vec α (n + 1)} → (x::xs)[Fin.last (n + 1)] = xs[Fin.last n]
| x'::xs => by simp [Fin.last, getElem, get]

@[simp]
theorem Vec.get_concat_last {α} {n : Nat} {a : α} : {xs : Vec α n} → (xs.concat a)[Fin.last n] = a
| #() => rfl
| x::xs => by simp [concat, get_concat_last]

@[simp]
theorem Vec.get_rev_cons {α} {x : α} : {n : Nat} → {xs : Vec α n} → {i : Fin n} → (x::xs)[i.castSucc.rev] = xs[i.rev]
| _, #(), i => by grind
| n + 1, x'::xs, i => by
  cases i using Fin.reverseInduction
  case last => simp [Fin.rev] ; rfl
  case cast i' _ => simp [Fin.rev_castSucc]

@[simp]
theorem Vec.get_reverse {α} : {n : Nat} → {v : Vec α n} → {i : Fin n} → v.reverse[i] = v[i.rev]
| 1, x::#(), 0 => rfl
| n + 1 + 1, x::xs, i => by
  induction i using Fin.reverseInduction
  case last => simp [reverse]
  case cast i' => simp [get_concat_castSucc, get_reverse]

@[simp]
theorem Vec.get_zipWith {α β γ n} {f : α -> β -> γ}
  : {v1 : Vec α n} → {v2 : Vec β n} → {i : Fin n} → (zipWith f v1 v2)[i] = f v1[i] v2[i]
| x::xs, y::ys, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [zipWith, get_zipWith]

@[simp]
theorem Vec.get_zip {α β n} : {v1 : Vec α n} → {v2 : Vec β n} → {i : Fin n} → (zip v1 v2)[i] = (v1[i], v2[i])
| x::xs, y::ys, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [zip]

@[simp]
theorem Vec.get_range : {k n : Nat} → {i : Fin n} → (range n k)[i] = i + k
| 0, n + 1, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [range, get_range]
| k + 1, n + 1, i => by
  cases i using Fin.cases
  case zero => simp
  case succ i' => simp [range, get_range] ; omega

@[simp]
theorem Vec.get_zipIdx {α} : {k n : Nat} → {v : Vec α n} → {i : Fin n} → (v.zipIdx k)[i] = (v[i], i + k)
| 0, n + 1, x::xs, i => by
  cases i using Fin.cases
  case zero => rfl
  case succ i' => simp [zipIdx, get_zipIdx]
| k + 1, n + 1, x::xs, i => by
  cases i using Fin.cases
  case zero => simp
  case succ i' => simp [get_zipIdx] ; omega

/-! ## head -/

@[grind =]
theorem Vec.head_zeroth_index_agree {α} : {n : Nat} → [NeZero n] → {v : Vec α n} → v.head = v[Fin.ofNat n 0]
| _ + 1, _, _::_ => rfl

@[simp]
theorem Vec.head_set_zero {α x} : {n : Nat} → [NeZero n] → {v : Vec α n} → (v.set 0 x).head = x
| _ + 1, _, _::_ => rfl

@[simp]
theorem Vec.head_set_succ {α a} : {n : Nat} → {i : Fin n} → [NeZero n] → [NeZero i] → {v : Vec α n} → (v.set i a).head = v.head
| _ + 1, ⟨_ + 1, _⟩, _, _, _::_ => rfl

@[simp]
theorem Vec.head_concat {α a} : {n : Nat} → [NeZero n] → {v : Vec α n} → (v.concat a).head = v.head
| _ + 1, _, _::_ => rfl

@[simp]
theorem Vec.head_append {α} : {n m : Nat} → [NeZero n] → {v1 : Vec α n} → (v2 : Vec α m) → (v1 ++ v2).head = v1.head
| _ + 1, _, _, _::_, _ => rfl

@[simp]
theorem Vec.head_flatten {α} : {n m : Nat} → [NeZero n] → [NeZero m] → {v : Vec (Vec α n) m} → v.flatten.head = v.head.head
| _ + 1, _ + 1, _, _, (_::_)::_ => rfl

@[simp]
theorem Vec.head_map {α β} {f : α -> β} : {n : Nat} → [NeZero n] → {v : Vec α n} → (v.map f).head = f v.head
| _ + 1, _, _::_ => rfl

@[simp]
theorem Vec.head_replicate {α} {x : α} : {n : Nat} → [NeZero n] → (replicate n x).head = x
| _ + 1, _ => rfl

@[simp]
theorem Vec.head_zipWith {α β γ} {f : α -> β -> γ} : {n : Nat} → [NeZero n] → {v1 : Vec α n} → {v2 : Vec β n} → (zipWith f v1 v2).head = f v1.head v2.head
| _ + 1, _, _::_, _::_ => rfl

@[simp]
theorem Vec.head_zip {α β} : {n : Nat} → [NeZero n] → {v1 : Vec α n} → {v2 : Vec β n} → (zip v1 v2).head = (v1.head, v2.head)
| _ + 1, _, _::_, _::_ => rfl

@[simp]
theorem Vec.head_range : {n k : Nat} → [NeZero n] → (range n k).head = k
| _ + 1, _, _ => rfl

@[simp]
theorem Vec.head_zipIdx {α} : {n k : Nat} → [NeZero n] → {v : Vec α n} → (v.zipIdx k).head = (v.head, k)
| _ + 1, _, _, _::_ => rfl

/-! ## tail -/

@[simp]
theorem Vec.tail_append {α} : {n m : Nat} → [NeZero n] → {v1 : Vec α n} → {v2 : Vec α m} → (v1 ++ v2).tail ≍ v1.tail ++ v2
| n + 1, m, _, x::xs, ys => by simp only [HAppend.hAppend, append] ; rw [tail, tail] ; simp

-- TODO

/-! ## set -/

-- TODO

/-! ## foldl -/

@[simp]
theorem Vec.foldl_assoc {α n} {op : α -> α -> α} [ha : Std.Associative op] {v : Vec α n} {a b : α}
  : v.foldl op (op a b) = op a (v.foldl op b)
:= sorry

-- TODO

/-! ## foldr -/

-- TODO

/-! ## concat -/

-- TODO

/-! ## flatten -/

-- TODO

/-! ## map
Why don't we use `Functor` / `LawfulFunctor`?
Because Lean's type inference is not capable of figuring out the right functor `f` when
using `Functor.map`.
Try it yourself: implement `Functor (Vec · n)` and notice how `(· + 2) <$> #(1, 2)` fails.
Solutions:
1. Try to fix Lean's type inference algorithm, unclear if Lean developers will be receptive
2. Use `Vec.map` directly (not horrible, `v.map f` is good ergonomics)
3. Define our own `IndexedFunctor` type that will resolve the index correctly:
```lean
class IndexedFunctor (I : Type u) (F : Type v -> I -> Type w) where
  imap {α β i} (f : α -> β) : F α i -> F β i

instance : IndexedFunctor Nat Vec where
  imap := Vec.map

#eval IndexedFunctor.imap (· + 2) #(1, 2)
```
**For now we choose 2**
-/

@[simp, grind =]
theorem Vec.map_id {α n} : {v : Vec α n} → v.map id = v
| #() => rfl
| x::xs => by simp [map_id]

@[simp, grind =]
theorem Vec.map_id_lambda {α n} : {v : Vec α n} → v.map (λ x => x) = v := map_id

@[simp, grind =]
theorem Vec.map_tail {α β n} {f : α -> β} : [NeZero n] → {v : Vec α n} → v.tail.map f = (v.map f).tail
| _, #() => by simp ; norm_cast
| _, x::xs => rfl

@[simp, grind =]
theorem Vec.map_set {α β x} {f : α -> β} : {n : Nat} → {i : Fin n} → {v : Vec α n} → (v.set i x).map f = (v.map f).set i (f x)
| n + 1, i, x::xs => by
  cases i using Fin.cases
  case zero => simp [map, set]
  case succ i' => simp [map, set, map_set]

@[simp, grind =]
theorem Vec.map_concat {α β n x} {f : α -> β} : {v : Vec α n} → (v.concat x).map f = (v.map f).concat (f x)
| #() => by simp
| x::xs => by simp [map, concat, map_concat]

@[simp, grind =]
theorem Vec.map_append {α β n m} {f : α -> β} : {v1 : Vec α n} → {v2 : Vec α m} → (v1 ++ v2).map f = v1.map f ++ v2.map f
| #(), _ => rfl
| _, #() => by grind [map]
| x::xs, y::ys => by simp [map_append]

@[simp, grind =]
theorem Vec.map_flatten {α β n m} {f : α -> β} : {v : Vec (Vec α n) m} → v.flatten.map f = (v.map (map f)).flatten
| #() => rfl
| x::xs => by simp [map, flatten, ← map_flatten]

@[simp, grind =]
theorem Vec.map_map {α β γ n} {f : α -> β} {h : β -> γ} : {v : Vec α n} → (v.map f).map h = v.map (h ∘ f)
| #() => rfl
| x::xs => by simp [map, map_map]

@[simp, grind =]
theorem Vec.map_replicate {α β} {a : α} {f : α -> β} : {n : Nat} →  (replicate n a).map f = replicate n (f a)
| 0 => rfl
| n + 1 => by simp [map_replicate]

@[simp, grind =]
theorem Vec.map_reverse {α β n} {f : α -> β} : {v : Vec α n} → v.reverse.map f = (v.map f).reverse
| #() => rfl
| x::xs => by simp [map_concat, map_reverse]

@[simp, grind =]
theorem Vec.map_take {α β} {f : α -> β}
  : {m : Nat} → {n : Fin m} → {h : n ≤ m} → {v : Vec α m} → (v.take n h).map f = (v.map f).take n h
| m + 1, n, h, x::xs => by
  cases n using Fin.cases
  case zero => rfl
  case succ n' => simp [map, take, map_take]

@[simp, grind =]
theorem Vec.map_cast {α β} {f : α → β} : {m n : Nat} → {h : m = n} → {v : Vec α m}
  → map f (cast (by grind : Vec α m = Vec α n) v) = cast (by grind : Vec β m = Vec β n) (map f v) := by grind

@[simp, grind =]
theorem Vec.map_drop {α β} {f : α -> β}
  : {m : Nat} → {n : Fin m} → {h : n ≤ m} → {v : Vec α m} → (v.drop n h).map f = (v.map f).drop n h
| m + 1, n, h, x::xs => by
  cases n using Fin.cases
  case zero => rfl
  case succ n' => simp [map, drop, map_drop]

/-! ## beq -/

theorem Vec.beq_refl {α n} [BEq α] [ReflBEq α] : ∀ {a : Vec α n}, (a == a) = true
| #() => rfl
| x::xs => by simp [BEq.beq] ; exact @beq_refl _ _ _ _ xs

instance {α n} [BEq α] [ReflBEq α] : ReflBEq (Vec α n) where
  rfl := Vec.beq_refl

theorem Vec.beq_lawful {α n} [BEq α] [LawfulBEq α] : {v1 v2 : Vec α n} → (beq v1 v2) = true → v1 = v2
| #(), #(), h => rfl
| x::xs, y::ys, h => by simp at h ; simp [h, @beq_lawful _ _ _ _ xs ys h.2]

instance {α n} [BEq α] [LawfulBEq α] : LawfulBEq (Vec α n) where
  eq_of_beq := Vec.beq_lawful

@[grind =]
theorem Vec.beq_head_tail {α} [BEq α] : {n : Nat} → [NeZero n] → {v1 v2 : Vec α n} → v1.head == v2.head ∧ v1.tail == v2.tail ↔ v1 == v2
| n + 1, _, x::xs, y::ys => by simp_all [BEq.beq]

-- TODO: there is some funext automation thing that should be used here
@[grind <-]
theorem Vec.beq_get {α} [BEq α] : {n : Nat} → {v1 v2 : Vec α n} → (h : ∀ (i : Fin n), v1[i] == v2[i]) → v1 == v2
| 0, #(), #(), _ => rfl
| n + 1, x::xs, y::ys, h => by
  have h' : x == y ∧ ∀ (i : Fin n), xs[i] == ys[i] := ⟨ h 0 , fun i ↦ h i.succ ⟩
  simp [BEq.beq]
  exact ⟨ h'.1, @beq_get α _ n xs ys h'.2 ⟩

/-! ## replicate -/

-- TODO

/-! ## reverse -/

-- TODO

/-! ## contains -/

-- TODO

/-! ## take -/

-- TODO

/-! ## drop -/

-- TODO

/-! ## any -/

theorem Vec.any_append_left {α p} : {n m : Nat} → {v1 : Vec α n} → {v2 : Vec α m} → v1.any p → (v1 ++ v2).any p
| 0, m, #(), ys, h => False.elim (by simp [any] at h)
| 1, m, x::#(), ys, h => by simp_all [any]
| n + 2, m, x::xs, ys, h => by
  simp_all [any]
  cases h
  case inl h' => exact Or.inl h'
  case inr h' => exact Or.inr $ any_append_left (v1 := xs) (v2 := ys) (p := p) h'

theorem Vec.any_append_right {α p} : {n m : Nat} → {v1 : Vec α n} → {v2 : Vec α m} → v2.any p → (v1 ++ v2).any p
| n, 0, xs, #(), h => False.elim (by simp [any] at h)
| 0, 1, #(), y::#(), h => by simp_all
| n + 1, 1, x::xs, y::#(), h => by simp_all [any, any_append_right]
| 0, m + 2, #(), y::ys, h => by simp_all
| n + 1, m + 2, x::xs, y::ys, h => by simp_all [any, any_append_right]

theorem Vec.any_append_iff {α p} : {n m : Nat} → {v1 : Vec α n} → {v2 : Vec α m} → (v1.any p ∨ v2.any p) ↔ (v1 ++ v2).any p
| 0, m, #(), ys => by simp_all [any]
| 1, m, x::#(), ys => by simp_all [any]
| n + 2, m, x::xs, ys => by
  have ih := any_append_iff (v1 := xs) (v2 := ys) (p := p)
  simp [any, ← ih]
  grind

theorem Vec.any_list {α p} {n : Nat} : {v : Vec α n} → v.any p ↔ v.list.any p
| #() => by simp [any]
| x::xs => by simp [any, any_list]

set_option linter.unusedVariables false in
theorem Vec.any_get {α p} : {n : Nat} → {v : Vec α n} → {h : v.any p} → ∃ i : Fin n, p (v[i])
| 0, #(), _ => False.elim (by simp_all [any])
| n + 1, x::xs, h => by
  simp [any] at h
  cases h
  case inl h' => exact ⟨ 0, h' ⟩
  case inr h' =>
    have ⟨ i, ih ⟩ := any_get (v := xs) (h := h')
    exact ⟨ i.succ, ih ⟩

set_option linter.unusedVariables false in
theorem Vec.any_tail {α p} : {n : Nat} → [NeZero n] → {v : Vec α n} → {h : v.any p} → {not_head : ¬ p v.head} → v.tail.any p
| n + 1, _, x::xs, h, not_head => by simp_all [any]

set_option linter.unusedVariables false in
theorem Vec.any_set {α p} : {a : α} → {n : Nat} → {v : Vec α n} → {i : Fin n} → {h : p a} → (v.set i a).any p
| a, n + 1, x::xs, i, h => by
  cases i using Fin.cases
  case zero => grind [set, any]
  case succ i' => simp [set, any] ; exact Or.inr $ any_set (v := xs) (i := i') (a := a) (h := h)

-- TODO

/-! ## all -/

-- TODO

/-! ## zipWith -/

-- TODO

/-! ## zip -/

-- TODO

/-! ## unzip -/

-- TODO

/-! ## range -/

-- TODO

/-! ## zipIdx -/

-- TODO

/-! ## find? -/

-- TODO

/-! ## findIdx? -/

theorem Vec.findIdx?_eq_some_iff_getElem {α n i} {v : Vec α n} {p : α -> Bool} :
  findIdx? p v = some i <-> p v[i] ∧ ∀ (j : Fin n) (hji : j < i), ¬ p v[j] = true
:= sorry

-- TODO

/-! ## erase -/

-- TODO

/-! ## count -/

-- TODO

/-! ## traverse -/

theorem Vec.traverse_eq_pure_iff_getElem {m α β n v2} [i : Applicative m] {f : α -> m β} :
  {v1 : Vec α n} ->
  v1.traverse f = pure v2 ->
  ∀ i : Fin n, f v1[i] = pure (v2[i]) := sorry

-- TODO

/-! ## sequence -/

@[simp, grind =]
theorem Vec.sequence_map {m α β n} [Applicative m] {f : α -> m β} :
  {v : Vec α n} -> (v.map f).sequence = v.traverse f
| .nil => by simp [Vec.sequence]
| .cons x xs =>
  have ih := Vec.sequence_map (f := f) (v := xs)
  by simp [Vec.sequence] at *; congr; rw [ih]


-- TODO

/-! ## sum -/

-- TODO

/-! ## Mem -/

-- TODO

end Lilac
