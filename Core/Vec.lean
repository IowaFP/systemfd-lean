import LeanSubst
import Lilac

open LeanSubst

namespace Lilac

-- do not remove
@[simp]
theorem Vec.length_list : {v : Vec α n} -> v.list.length = n
| #() => by simp [list]
| .cons x xs => by simp [list, length_list (v := xs)]

-- do not remove
@[grind =]
theorem Vec.get_to {v : Fun.Vec α n} : v.to[i] = v i := by
  induction v using Fun.Vec.induction
  case _ => exfalso; apply Fin.elim0 i
  case cons hd tl ih =>
    cases i using Fin.cases
    case _ => simp; unfold Fun.Vec.cons; simp
    case _ i => simp [ih]; simp [Fun.Vec.cons]

theorem Vec.to_get_elem (vs : Vec α n) : ∀i, vs.to i = vs[i] := by
  intro i; induction vs <;> simp at *
  apply i.elim0
  case _ ih =>
  induction i using Fin.induction <;> simp at *
  rw[Fun.Vec.cons_zero]
  apply ih

theorem Fun.Vec.to_get_elem (vs : Vec α n) : ∀i, vs i = (Vec.to vs)[i] := by
  intro i; induction vs using Vec.induction
  apply i.elim0
  case _ ih =>
  induction i using Fin.induction <;> simp at *
  rw[Fun.Vec.cons_zero]
  case _ i _ =>
  rw[Fun.Vec.cons_succ]
  apply ih i


def Vec.rmap [RenMap S T] (r : Ren T) : Vec S n -> Vec S n
| .nil => .nil
| .cons x tl => x⟨r⟩ :: rmap r tl

instance [RenMap S T] : RenMap (Vec S n) T where
  rmap := Vec.rmap

@[simp, grind =]
theorem Vec.index_into_map {v : Vec α n} {i : Fin n} : (Vec.map f v)[i] = f v[i] := by
  fun_induction Vec.map
  case _ => apply Fin.elim0 i
  case _ hd tl ih =>
  induction i using Fin.induction <;> simp at *

@[simp, grind =]
theorem Vec.rmap_nil [RenMap S T] {r : Ren T} : (@Vec.nil S)⟨r⟩ = #() := by
  simp [RenMap.rmap, Vec.rmap]

@[simp, grind =]
theorem Vec.rmap_cons [RenMap S T] {x} {tl : Vec S n} {r : Ren T}
  : (x :: tl)⟨r⟩ = x⟨r⟩ :: tl⟨r⟩
:= by
  simp [RenMap.rmap, Vec.rmap]

instance [RenMap S T] [RenMapId S T] : RenMapId (Vec S n) T where
  apply_id := by intro s; induction s <;> simp [*]

instance [RenMap S T] [RenMapCompose S T] : RenMapCompose (Vec S n) T where
  apply_compose := by intro s; induction s <;> simp [*]

def Vec.smap [SubstMap S T] (σ : Subst T) : Vec S n -> Vec S n
| .nil => .nil
| .cons x tl => x[σ] :: smap σ tl

instance [SubstMap S T] : SubstMap (Vec S n) T where
  smap := Vec.smap

@[simp, grind =]
theorem Vec.smap_nil [SubstMap S T] {σ : Subst T} : (@Vec.nil S)[σ] = #() := by
  simp [SubstMap.smap, Vec.smap]

@[simp, grind =]
theorem Vec.smap_cons [SubstMap S T] {x} {tl : Vec S n} {σ : Subst T}
  : (x :: tl)[σ] = x[σ] :: tl[σ]
:= by
  simp [SubstMap.smap, Vec.smap]

instance [RenMap S T] [SubstMap S T] [SubstMapId S T]
  : SubstMapId (Vec S n) T
where
  apply_id := by intro t; induction t <;> simp [*]

instance [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T] : SubstMapRenComposeLeft (Vec S n) T where
  apply_ren_compose_left := sorry

instance [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T] : SubstMapRenComposeRight (Vec S n) T where
  apply_ren_compose_right := sorry

instance [SubstMap S T] [SubstMap T T] : SubstMapCompose (Vec S n) T where
  apply_compose := sorry

@[grind =]
theorem Vec.rmap_promote [RenMap S T] {v : Vec S n} {r : Ren T} : Vec.map (·⟨r⟩) v = v⟨r⟩ := by
  induction v <;> simp [*]

@[grind =]
theorem Vec.smap_promote [SubstMap S T] {v : Vec S n} {σ : Subst T} : Vec.map (·[σ]) v = v[σ] := by
  induction v <;> simp [*]

@[grind =]
theorem Vec.to_rmap [RenMap S T] {r : Ren T} {v : Fun.Vec S m}
  : (v.to)⟨r⟩ = Fun.Vec.to (fun i => (v i)⟨r⟩)
:= sorry

@[grind =]
theorem Vec.to_smap [SubstMap S T] {σ : Subst T} {v : Fun.Vec S m}
  : (v.to)[σ] = Fun.Vec.to (fun i => (v i)[σ])
:= sorry

@[simp]
theorem Vec.smap_index [SubstMap S T] {i : Fin n} {v : Vec S n} {σ : Subst T} : v[i][σ] = v[σ][i] :=
  match n, v with
  | 0, v => Fin.elim0 i
  | n + 1, .cons x xs => by
    induction i using Fin.induction <;> simp at *
    case _ i ih => apply Vec.smap_index

@[simp]
theorem Vec.rmap_index [RenMap S T] {i : Fin n} {v : Vec S n} {r : Ren T} : v[i]⟨r⟩ = v⟨r⟩[i] :=
  match n, v with
  | 0, v => Fin.elim0 i
  | n + 1, .cons x xs => by
    induction i using Fin.induction <;> simp at *
    case _ i ih => apply Vec.rmap_index

theorem Vec.get_subst [SubstMap S T] {i : Fin n} {v : Vec S n} {σ : Subst T} : v[i][σ] = v[σ][i] := sorry


def Vec.reprPrec [Repr T] : {n : Nat} -> Vec T n -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr v[Fin.ofNat 1 0]
| _ + 1, .cons v t, i =>
  (repr v) ++ ", " ++ (Vec.reprPrec t i)


instance instRepr_Vec [Repr T] : Repr (Vec T n) where
  reprPrec v n := "#(" ++ Vec.reprPrec v n ++ ")"

theorem Vec.units (vs : Vec Unit n) : ∀ i : Fin n, (vs[i]) = () := by
 intro i
 induction vs
 apply i.elim0
 simp


def Vec.foldl_and [BEq α][LawfulBEq α] {tl : Vec α n} :
  Vec.foldl (fun acc c => c == e && acc) false tl = true -> False
:= by
intro h
induction tl <;> simp at *
case _ ih => rw[ih] at h; cases h


def Vec.elems_eq_to [BEq Q] {n : Nat} (e : Q) (vs : Vec Q n) : Bool :=
  vs.foldl (λ acc c => c == e && acc) true

theorem Vec.elems_eq_to_sound [BEq Q] [LawfulBEq Q] {e : Q} {vs : Vec Q n} :
  vs.elems_eq_to e = true ->
  ∀ i : Fin n, vs[i] = e := by
intro h
induction vs <;> simp [Vec.elems_eq_to] at *
case _ n hd tl ih =>
  generalize zdef : (hd == e) = z at *
  cases z <;> simp at *
  · exfalso; apply Vec.foldl_and h
  · intro i
    induction i using Fin.induction <;> simp at *
    apply zdef
    case _ i _ => apply ih h i


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
  ∀ i : Fin n, vs[i] = t := by
intro h;
fun_induction Vec.get_elem_if_eq <;> simp at *
case _ => assumption
case _ n x xs ih1 ih2 =>
  intro i
  rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h⟩
  simp at h; cases h.2.1; cases h.2.2; simp at h
  induction i using Fin.induction
  · simp
  · simp; apply ih1 h

-- TODO: change this to Vec.findIdx? once Lilac is fixed
def Vec.findIdx! {α n} (p : α -> Bool) : Vec α n -> Option (Fin n)
| #() => none
| .cons x xs => go p (x::xs) 0
where
  go (p : α -> Bool) : {n : Nat} -> Vec α n -> Nat -> Option (Fin n)
  | _, #(), _ => none
  | n + 1, .cons x xs, i => if p x then Fin.ofNat (n + 1) i else Fin.succ <$> go p xs i


#guard Vec.findIdx! (· == 3) #(3, 1, 2) == some 0
#guard Vec.findIdx! (· == 4) #(0, 4, 2) == some 1
#guard Vec.findIdx! (· == 5) #(0, 1, 5) == some 2

theorem Vec.findIdx!_go_sound {vs : Vec α n} {p : α -> Bool}:
  Vec.findIdx!.go p vs k = some i ->
  k ≤ i := by
intro h
fun_induction findIdx!.go
cases h
simp at h; sorry
sorry


theorem Vec.findIdx_sound {p : T -> Bool} {vs : Vec T n} : Vec.findIdx! p vs = some i ->
   p vs[i] = true
:= by
  intro h
  induction vs <;> simp [findIdx!] at *
  case _ ih =>
    induction i using Fin.induction <;> simp [findIdx!.go] at *
    sorry
    sorry



theorem Vec.unzip_eta_get_elem {vs : Vec (α × β) n} : ∀ i : Fin n, vs[i] = (vs.unzip.1[i], vs.unzip.2[i])
:= by
intro i
induction vs
apply i.elim0
induction i using Fin.induction <;> simp [Vec.unzip]
case _ ih1 i ih2 => apply ih1

theorem Vec.eq_sound_lem [BEq α][LawfulBEq α] {v1 v2 : Vec α n} : (h : v1.beq v2) -> v1 = v2 := by
  intro h;
  match n, v1, v2 with
  | 0, .nil, .nil => simp
  | n + 1, .cons x xs , .cons y ys =>
    unfold Vec.beq at h; simp at *;
    constructor
    apply h.1
    apply Vec.eq_sound_lem h.2


@[simp]
def Vec.paste (b : String) : Vec (Vec String m) n -> Vec (Vec String (m + 1)) n
| .nil => .nil
| .cons x xs => .cons (b :: x) (paste b xs)

theorem Vec.paste_soundness {rm : Vec (Vec String m) n} {rm' : Vec (Vec String (m + 1)) n} :
  Vec.paste b rm = rm' ->
  ∀ i : Fin n, rm'[i] = b :: (rm[i])
:= by
intro h i
fun_induction Vec.paste
apply i.elim0
case _ ih =>
  subst h;
  induction i using Fin.induction <;> simp at *
  case _ ih => apply ih

@[simp]
def Vec.combine (base : (m : Nat) × Vec (Vec String k) m) :
    ((n : Nat) × Vec String n) -> ((p : Nat) × Vec (Vec String (k + 1)) p)
| ⟨0, .nil⟩ => ⟨0, .nil⟩
| ⟨(n + 1), (.cons x xs)⟩ =>
  let ⟨p , vs⟩ := combine base ⟨n, xs⟩
  -- let vs' := paste x base.snd
  ⟨p + base.fst, (paste x base.snd).append vs⟩

theorem Vec.combine_size {base : (m : Nat) × Vec (Vec String k) m} {x : ((n : Nat) × Vec String n)} :
  combine base x = ⟨p, ys⟩ ->
  p = x.fst * base.fst := by
intro h
fun_induction Vec.combine generalizing ys p <;> simp at *
apply Eq.symm h.1
case _ vs _ h ih =>
  rcases h with ⟨h1, h2⟩
  subst h1; replace h2 := eq_of_heq h2; subst h2
  replace ih := ih h
  subst ih; rw[Nat.right_distrib]; simp

theorem Vec.append_indexing_left {vs : Vec α n}{vs' : Vec α m} (i : Fin n) :
  ∃ j : Fin (m + n), vs[i] = (vs.append vs')[j]
:= by
  induction vs <;> simp at *
  apply i.elim0
  case _ i ih =>
  induction i using Fin.induction <;> simp at *
  case _ => exists 0
  case _ i _ =>
    replace ih := ih i;
    rcases ih with ⟨j, ih⟩
    exists j.succ

theorem Vec.append_indexing_right {vs : Vec α n}{vs' : Vec α m} (i : Fin m) :
  ∃ j : Fin (m + n), vs'[i] = (vs.append vs')[j]
:= by
  induction vs <;> simp at *
  exists i
  case _ ih =>
    rcases ih with ⟨j, ih⟩
    exists j.succ

theorem Vec.combine_soundness :
  Vec.combine rm1 cs = rm2 ->
  ∀ (i : Fin cs.1) (i' : Fin rm1.1), ∃ j : Fin rm2.1, cs.2[i] :: rm1.2[i'] = rm2.2[j] := by
intro h i i'
fun_induction Vec.combine generalizing rm2 <;> simp at i
case _ => apply i.elim0
case _ n x vs _ vs' ch ih =>
  subst h; simp at *;
  induction i using Fin.induction
  · case _ =>
    simp
    have lem := Vec.combine_size ch; subst lem; simp at *
    rw[ch] at ih; simp at ih
    generalize p_def : paste x rm1.snd = p at *
    have lem := Vec.paste_soundness p_def; rw[<-p_def] at lem; replace lem := lem i'
    subst p; rw[<-lem]; apply Vec.append_indexing_left i'
  case _ i _ =>
    simp; replace ih := ih i;
    rcases ih with ⟨j, ih⟩
    generalize zdef : combine rm1 ⟨n, vs⟩ = z at *
    have lem := Vec.combine_size zdef; simp at lem; subst ch; simp at *; subst lem; simp at j
    rw[ih]
    apply Vec.append_indexing_right (vs := paste x rm1.snd) j

@[simp]
def Vec.populate_aux (base : (m : Nat) × Vec (Vec String k) m) :
  Vec ((n : Nat) × Vec String n) ℓ -> ((p : Nat) × Vec (Vec String (k + ℓ)) p)
| .nil => base
| .cons x xs =>
  Vec.combine (populate_aux base xs) x


@[simp]
def Vec.prod : Vec Nat n -> Nat
| .nil => 1
| .cons x xs => x * Vec.prod xs


theorem Vec.populate_aux_size (ps : Vec ((n : Nat) × Vec String n) ℓ) :
  populate_aux (k := k) ⟨bℓ, bs⟩ ps = vs ->
  vs.fst = (Vec.prod (ps.map (·.1))) * bℓ := by
intro h
induction ps generalizing bs bℓ <;> simp at *
cases h; simp
case _ ps pss ih =>
  generalize z_def : populate_aux ⟨bℓ, bs⟩ pss = z at h
  have lem := combine_size h
  rw[Nat.mul_assoc]
  rw[lem]; congr
  have ih := @ih bℓ bs
  rw[z_def] at ih; apply ih;

@[simp]
def Vec.populate (ps : Vec ((n : Nat) × Vec String n) ℓ) : ((p : Nat) × Vec (Vec String (0 + ℓ)) p)
:= populate_aux (k := 0) ⟨1, #(#())⟩ ps

theorem Vec.populate_size (ps : Vec ((n : Nat) × Vec String n) ℓ) :
  populate ps = vs ->
  vs.fst = (Vec.prod (ps.map (·.1)))
:= by
intro h
unfold populate at h
generalize z_def : populate_aux ⟨1, #(#())⟩ ps = z at *
have lem := Vec.populate_aux_size _ z_def
subst h; rw[Nat.mul_one] at lem; assumption



theorem Vec.map_seq_sound {vs : Vec α n} {vs' : Vec β n} (f : α -> Option β) :
  (Vec.map f vs).sequence = some vs' ->
  ∀ i : Fin n, f (vs[i]) = some (vs'[i])
:= by
intro h i
generalize zdef : map f vs = z at *
sorry
-- fun_induction Vec.sequence
-- · apply i.elim0
-- · cases h
-- · case _ ih1 =>
--   simp at h
--   rw[Option.bind_eq_some_iff] at h; rcases h with ⟨_, h1, h⟩
--   induction i using Fin.induction
--   · cases vs'; case _ v' vs' =>
--     cases vs; case _ v vs =>
--     simp; simp at h; rcases h with ⟨e1, e2⟩
--     subst e1; subst e2; simp at zdef; apply zdef.1
--   · case _ ih2 =>
--     cases vs'; case _ v' vs' =>
--     cases vs; case _ v vs =>
--     simp; simp at h; rcases h with ⟨e1, e2⟩
--     subst e1; subst e2
--     simp at zdef;
--     apply ih1;
--     apply zdef.2
--     apply h1

theorem Vec.seq_sound1 {vs : Fun.Vec α n} {vs' : Vec β n} (f : α -> Option β) :
  (Fun.Vec.to (λ i => f (vs i))).sequence = some vs' ->
  ∀ i : Fin n, f (vs i) = some (vs'.to i)
:= by sorry
-- generalize zdef : Fun.Vec.to (λ i => f (vs i)) = z at *
-- have lem : Fun.Vec.to (λ i => f (vs i)) = (Vec.map f vs.to) := by
--   induction vs using Fun.Vec.induction
--   simp; cases vs'; cases z; apply zdef
--   case _ v vs ih =>
--   cases vs'; case _ v' vs' =>
--   cases z; case _ hd tl =>
--   simp at *; rw[zdef]; simp
--   replace ih := @ih vs'; sorry
-- intro h i

-- sorry


theorem Vec.seq_sound2 {vs1 : Fun.Vec α n} {vs2 : Fun.Vec β n} {vs' : Vec γ n} (f : α -> β -> Option γ) :
  (Fun.Vec.to (λ i => f (vs1 i) (vs2 i))).sequence = some vs' ->
  ∀ i : Fin n, f (vs1 i) (vs2 i) = some (vs'.to i) := by sorry
-- intro h1 i
-- match n, vs1, vs2 with
-- | 0, vs1, vs2 => apply i.elim0
-- | n + 1, xs, ys =>
--   induction i using Fin.induction
--   sorry
--   sorry

theorem Vec.seq_sound3
  {vs1 : Fun.Vec α n} {vs2 : Fun.Vec β n} {vs3 : Fun.Vec γ n}
  {vs' : Vec δ n} (f : α -> β -> γ -> Option δ) :
  (Fun.Vec.to (λ i => f (vs1 i) (vs2 i) (vs3 i))).sequence = some vs' ->
  ∀ i : Fin n, f (vs1 i) (vs2 i) (vs3 i) = some (vs'.to i) := by sorry


-- checks if all the elements are unique
def Vec.unique_elems [BEq α][LawfulBEq α] : Vec α n -> Bool
| .nil => true
| .cons x xs =>
  let vs' := Vec.map (· != x) xs
  Vec.elems_eq_to true vs' && Vec.unique_elems xs


#guard Vec.unique_elems #(1, 2, 3) == true
#guard Vec.unique_elems #(1, 1, 2) == false

theorem Vec.unique_elems_sound [BEq α][LawfulBEq α] {vs : Vec α n} :
  vs.unique_elems = true ->
  (∀ i j : Fin n, i ≠ j -> (vs[i] ≠ vs[j])) := by
intro h i j e
induction vs
apply i.elim0
case _ ih =>
  simp [unique_elems] at h
  rcases h with ⟨h1, h2⟩
  replace h1 := Vec.elems_eq_to_sound h1
  intro h
  cases i using Fin.cases
  case _ =>
    cases j using Fin.cases
    apply e; rfl
    case _ i =>
    simp at e; simp at h;
    replace h1 := h1 i
    simp at h1; apply h1 (Eq.symm h)
  case _ i =>
    replace ih := ih h2
    simp at h
    cases j using Fin.cases
    · simp at *;
      apply h1 i h
    · case _ j =>
      simp at *;
      apply ih i j e h

#guard Vec.foldl Option.or (some 1) #(none, some 2) = some 1
#guard Vec.foldl Option.or (none : Option Nat) (#(none, none)) = none
#guard Vec.foldl Option.or none #(some 1, none) = some 1

theorem Vec.fold_or_val_eq : foldl Option.or (some v1) as = some v2 -> v1 = v2
:= by
  intro h
  induction as <;> simp at *
  apply h
  case _ ih => apply ih h

theorem Vec.fold_or {cs : Vec _ n}: Vec.foldl Option.or d cs = e ->
  d = e ∨ ∃ i : Fin n, cs[i] = e
:= by
intro h
induction cs
· simp at h; apply Or.inl h
· case _ a as ih =>
  simp at h
  cases a <;> simp at *
  case _ =>
    replace ih := ih h
    cases ih
    case _ ih => apply Or.inl ih
    case _ ih =>
      rcases ih with ⟨i, ih⟩; apply Or.inr; exists i.succ
  case _ =>
    cases d <;> simp at *
    cases e
    · apply Or.inl rfl
    · apply Or.inr; exists 0; simp; apply Vec.fold_or_val_eq h
    replace ih := ih h
    cases ih
    case _ ih => apply Or.inl ih
    case _ ih =>
      rcases ih with ⟨i, ih⟩; apply Or.inr; exists i.succ


def Vec.from_list : List α -> (n : Nat) × Vec α n
| .nil => ⟨0, .nil⟩
| .cons x xs =>
  let ⟨n, v⟩ := from_list xs
  ⟨n + 1, x :: v⟩

theorem Vec.from_list_to {l : List α} : (Vec.from_list l).2.list = l := by
induction l <;> simp [from_list] at *
case _ ih => apply ih

theorem Vec.to_from_list {vs : Vec α n} : Vec.from_list (vs.list) = ⟨n, vs⟩ := by
induction vs <;> simp [from_list] at *
case _ ih => rw[ih]; simp


end Lilac
