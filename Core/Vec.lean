import LeanSubst
import Lilac

open LeanSubst

namespace Lilac

theorem Vec.ext_get {α} : ∀ {n} {v1 v2 : Vec α n} (_ : ∀ (i : Fin n), v1[i] = v2[i]), v1 = v2
| 0, .nil, .nil, h => rfl
| n + 1, .cons x xs, .cons y ys, h =>
  have h0 := h 0
  have h := λ (i:Fin _) => h i.succ
  have ih := ext_get (v1 := xs) (v2 := ys) h
  by simp at h0; simp [*]

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

@[simp]
theorem Vec.get_Fin_ofNat_succ {xs : Vec α (n + 1)} (h : i + 1 < n + 2) : (x :: xs)[Fin.ofNat (n + 2) (i + 1)] = xs[Fin.ofNat (n + 1) i] := by
  unfold Fin.ofNat
  have lem1 : (i + 1) % (n + 2) = i + 1 := by rw [Nat.mod_eq_of_lt h]
  have lem2 : i % (n + 1) = i := by rw [Nat.mod_eq_of_lt]; grind
  simp [lem1, lem2]
  simp [getElem, Vec.get]

theorem Vec.get_list_to_get : {n:Nat} -> {v : Vec α (n + 1)} -> (h : i < n + 1) -> v.list[i]'(by simp [h]) = v[Fin.ofNat (n + 1) i]
| n, .cons x xs, h =>
  match i with
  | 0 => by simp
  | i + 1 =>
    match n with
    | 0 => by simp at h
    | n + 1 =>
      have lem1 : i < n + 1 := by grind
      have lem2 := get_list_to_get (v := xs) lem1
      by rw [Vec.get_Fin_ofNat_succ h]; simp [lem2]

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

private def apply_ren_compose_left_aux [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T]
  : ∀ {s : Vec S n} {r : Ren T} {τ : Subst T}, s⟨r⟩[τ] = s[r ∘ τ] := λ {s} =>
match s with
| #() => by simp
| .cons x xs => by simp; apply apply_ren_compose_left_aux

instance [RenMap S T] [SubstMap S T] [SubstMapRenComposeLeft S T] : SubstMapRenComposeLeft (Vec S n) T where
  apply_ren_compose_left := apply_ren_compose_left_aux

private def apply_ren_compose_right_aux [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T]
  : ∀ {s : Vec S n} {r : Ren T} {σ : Subst T}, s[σ]⟨r⟩ = s[σ ∘ r] := λ {s} =>
match s with
| #() => by simp
| .cons x xs => by simp; apply apply_ren_compose_right_aux

instance [RenMap S T] [RenMap T T] [SubstMap S T] [SubstMapRenComposeRight S T] : SubstMapRenComposeRight (Vec S n) T where
  apply_ren_compose_right := apply_ren_compose_right_aux

private def apply_compose_aux [SubstMap S T] [SubstMap T T] [SubstMapCompose S T]:
  ∀ {s : Vec S n} {σ τ : Subst T}, s[σ][τ] = s[σ ∘ τ] := λ {s} =>
  match s with
  | #() => by rfl
  | .cons x xs => by simp; apply apply_compose_aux

instance [SubstMap S T] [SubstMap T T] [SubstMapCompose S T] : SubstMapCompose (Vec S n) T where
  apply_compose := apply_compose_aux

instance [RenMap S T] [SubstMap S T] [SubstMapStable S T] : SubstMapStable (Vec S n) T where
  apply_stable := by
    intro r σ h; funext; case _ v =>
    induction v <;> simp [*]
    case _ ih => rw [Subst.apply_stable h]

@[grind =]
theorem Vec.rmap_promote [RenMap S T] {v : Vec S n} {r : Ren T} : Vec.map (·⟨r⟩) v = v⟨r⟩ := by
  induction v <;> simp [*]

@[grind =]
theorem Vec.smap_promote [SubstMap S T] {v : Vec S n} {σ : Subst T} : Vec.map (·[σ]) v = v[σ] := by
  induction v <;> simp [*]

@[grind =]
theorem Vec.to_rmap [RenMap S T] {r : Ren T} {v : Fun.Vec S m}
  : (v.to)⟨r⟩ = Fun.Vec.to (fun i => (v i)⟨r⟩)
:= by
  apply v.induction
  · simp; rfl
  · simp; intro n hd tl ih;
    rw[ih]; simp [Fun.Vec.cons]; rfl

@[grind =]
theorem Vec.to_smap [SubstMap S T] {σ : Subst T} {v : Fun.Vec S m}
  : (v.to)[σ] = Fun.Vec.to (fun i => (v i)[σ])
:= by
  apply v.induction
  · simp; rfl
  · simp; intro n hd tl ih;
    rw[ih]; simp [Fun.Vec.cons]; rfl

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

@[simp, grind =]
theorem Vec.get_subst [SubstMap S T] {i : Fin n} {v : Vec S n} {σ : Subst T} : v[i][σ] = v[σ][i]
  := by simp


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
  Vec.foldl (fun acc c => acc && c == e) false tl = true -> False
:= by
intro h
induction tl <;> simp at *
case _ ih => rw[ih] at h; cases h

def Vec.elems_eq_to [BEq Q] {n : Nat} (e : Q) (vs : Vec Q n) : Bool :=
  vs.foldl (λ acc c => acc && c == e) true

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
def Vec.get_elem_if_eq [BEq Q] [LawfulBEq Q] (vs : Vec Q n) : Option Q :=
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

theorem Vec.findIdx_sound {p : T -> Bool} {vs : Vec T n}
  : Vec.findIdx? p vs = some i -> p vs[i] = true
:= by
  intro h
  replace h := findIdx?_eq_some_iff_getElem.1 h
  apply h.1

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

@[simp]
theorem Vec.traverse_nil [Applicative F] {f : α -> F β} : Vec.traverse f (#()) = (pure #() : F (Vec β 0)) := rfl

@[simp]
theorem Vec.traverse_cons [Applicative F] {xs : Vec α n} (f : α -> F β):
  Vec.traverse f (Vec.cons x xs) = (Vec.cons · ·) <$> f x <*> traverse f xs
  := by simp

theorem Vec.map_seq_sound {vs : Vec α n} {vs' : Vec β n} (f : α -> Option β) :
  (Vec.map f vs).sequence = some vs' ->
  ∀ i : Fin n, f (vs[i]) = some (vs'[i])
:= by
  intro h
  simp at h; apply traverse_eq_pure_iff_getElem h

theorem Vec.seq_sound1 {vs : Fun.Vec α n} {vs' : Vec β n} (f : α -> Option β) :
  (Fun.Vec.to (λ i => f (vs i))).sequence = some vs' ->
  ∀ i : Fin n, f (vs i) = some (vs'.to i)
:= by
  intro h
  generalize zdef : Fun.Vec.to (λ i => f (vs i)) = z at *
  have lem := Vec.map_seq_sound (vs := z) (vs' := vs') (f := λ x => x) (h |> cast (by simp))
  simp at lem; rw [<-zdef] at lem
  simp [Vec.to_get_elem]; intro i
  replace lem := lem i
  rw [<-Fun.Vec.to_get_elem (vs := fun i => f (vs i))] at lem
  apply lem

theorem Vec.seq_sound2 {vs1 : Fun.Vec α n} {vs2 : Fun.Vec β n} {vs' : Vec γ n} (f : α -> β -> Option γ) :
  (Fun.Vec.to (λ i => f (vs1 i) (vs2 i))).sequence = some vs' ->
  ∀ i : Fin n, f (vs1 i) (vs2 i) = some (vs'.to i)
 := by
   intro h
   generalize zdef : Fun.Vec.to (λ i => f (vs1 i) (vs2 i)) = z at *
   have lem := Vec.map_seq_sound (vs := z) (vs' := vs') (f := λ x => x) (h |> cast (by simp))
   simp at lem; rw[<-zdef] at lem;
   simp [Vec.to_get_elem]; intro i
   replace lem := lem i
   rw [<-Fun.Vec.to_get_elem (vs := fun i => f (vs1 i) (vs2 i))] at lem
   apply lem


 theorem Vec.seq_sound3
  {vs1 : Fun.Vec α n} {vs2 : Fun.Vec β n} {vs3 : Fun.Vec γ n}
  {vs' : Vec δ n} (f : α -> β -> γ -> Option δ) :
  (Fun.Vec.to (λ i => f (vs1 i) (vs2 i) (vs3 i))).sequence = some vs' ->
  ∀ i : Fin n, f (vs1 i) (vs2 i) (vs3 i) = some (vs'.to i)
 := by
   intro h
   generalize zdef : Fun.Vec.to (λ i => f (vs1 i) (vs2 i) (vs3 i)) = z at *
   have lem := Vec.map_seq_sound (vs := z) (vs' := vs') (f := λ x => x) (h |> cast (by simp))
   simp at lem; rw[<-zdef] at lem;
   simp [Vec.to_get_elem]; intro i
   replace lem := lem i
   rw [<-Fun.Vec.to_get_elem (vs := fun i => f (vs1 i) (vs2 i) (vs3 i))] at lem
   apply lem



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
    cases d <;> simp at *
    replace ih := ih h
    cases ih
    case _ ih => apply Or.inl ih
    case _ ih =>
      rcases ih with ⟨i, ih⟩; apply Or.inr; exists i.succ
    grind
  case _ =>
    cases d <;> simp at *
    cases e
    · apply Or.inl rfl
    · apply Or.inr; exists 0; simp; apply Vec.fold_or_val_eq h
    grind

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

theorem Vec.from_list_length {l : List α} :
  (Vec.from_list l) = ⟨n, vs⟩ ->
  l.length = n := by
intro h
fun_induction Vec.from_list generalizing n <;> simp at *
apply h.1
case _ h2 ih =>
  replace ih := ih h2; subst ih; apply h.1

@[simp, grind =]
theorem Vec.from_list_nil : Vec.from_list ([] : List β) = ⟨0, .nil⟩ := by simp [Vec.from_list]

@[simp]
theorem Vec.from_list_cons {x : α} {vs : Vec α k} :
  Vec.from_list (x :: xs) = ⟨k, vs⟩ ->
  ∃ n vs', Vec.from_list xs = ⟨n, vs'⟩ ∧ ∃ (h : k = n + 1), vs = cast (by rw[h]) (x :: vs')
 := by
intro h
unfold from_list at h;
split at h
case _ n vs' h =>
simp at h; rcases h with ⟨e1, e2⟩
exists n; exists vs'
apply And.intro
apply h
exists (Eq.symm e1)
grind

theorem Vec.from_list_indexing {l : List α} {vs : Vec α n} {i : Nat} :
  Vec.from_list l = ⟨n, vs⟩ ->
  l[i]? = some c ->
  ∃ i : Fin n, vs[i] = c := by
intro h1 h2
rw[List.getElem?_eq_some_iff] at h2;
rcases h2 with ⟨e, h2⟩
have lem := Vec.from_list_length h1
fun_induction from_list generalizing n i <;> simp at *
cases e
case _ l ls _ _ h ih =>
  subst lem; rcases h1 with ⟨e, h1⟩; simp at e; subst e; simp at h1;
  subst h1;
  induction i <;> simp at *
  subst h2; exists 0
  case _ n ih2 =>
    simp at e;
    replace ih := ih (i := n) h e h2 rfl
    rcases ih with ⟨i, ih⟩
    exists i.succ

theorem Vec.from_list_indexing2 {l : List α} {vs : Vec α n} :
  (h : Vec.from_list l = ⟨n, vs⟩) ->
  ∀ i: Fin n, vs[i] = l[i]'(by have lem := Vec.from_list_length h; grind)
:= by
  intro h i
  fun_induction Vec.from_list generalizing n <;> simp at *
  · unfold from_list at h; cases h; apply i.elim0
  case _ h1 ih =>
    replace h := Vec.from_list_cons h
    rcases h with ⟨n1, vs1, h1, h2, ⟨e, h3⟩⟩
    replace ih := ih h1
    subst h2; simp at *;
    induction i using Fin.induction <;> simp at *
    case _ i _ => apply ih i

private theorem fin_shift_lemma {a2 a1 : α} {as1 as2 : Vec α n}:
  (∀ (i : Fin (n + 1)), (a1 :: as1)[i] = (a2 :: as2)[i]) ->
  ∀ (i : Fin n), as1[i] = as2[i] := by intro h i; apply h i.succ

theorem Vec.refl_indexing {v1 v2 : Vec α n} : v1 = v2 <-> ∀ (i: Fin n), v1[i] = v2[i]
:= by
apply Iff.intro
· intro h i; cases h; simp;
· intro h;
  induction v1
  cases v2; rfl
  case _ n _ as ih =>
    cases v2;
    congr;
    apply h 0
    apply ih (fin_shift_lemma (n := n) h)



theorem Vec.getElem_of_mem {α : Type u_1} {a : α} {l : Vec α n} (h : a ∈ l) :  ∃ (i : Fin n), l[i] = a
 := by
induction h
case head => exists 0
case tail ih => rcases ih with ⟨i, ih⟩; exists (i.succ)

theorem Vec.ne_of_not_mem_cons {α : Type u_1} {a b : α} {vs : Vec α n} :
  ¬(a ∈ b :: vs) -> (a ≠ b) := mt (λ x => by rw [x]; apply Mem.head)

theorem Vec.not_mem_of_not_mem_cons {α : Type u_1} {a b : α} {vs : Vec α n} :
  ¬a ∈ b :: vs -> ¬a ∈ vs := mt (λ x => Mem.tail b x)

def Vec.foldl_and_true {vs : Vec Bool n} :
  vs.foldl (·&&·) true = true <-> ∀ v ∈ vs, v = true
:= by
apply Iff.intro
· intro h v v_in_vs
  generalize fdef : (·&&·) = f at *
  generalize idef : true = init at *
  fun_induction foldl <;> simp at *
  case _ => cases v_in_vs
  case _ hd tl ih =>
    subst idef; rw[<-fdef] at h; simp at h;
    cases v_in_vs
    cases v;
    · have lem := Vec.foldl_and (e := true) (tl := tl); simp at lem; rw[h] at lem;
      cases lem;
    · simp
    case _ v_in_tl =>
    replace ih := ih v_in_tl; rw[<-fdef] at ih; simp at ih;
    cases hd
    · have lem := Vec.foldl_and (e := true) (tl := tl); simp at lem; rw[h] at lem;
      cases lem
    · simp at ih; apply ih h
· intro h
  induction vs <;> simp at *
  case _ v vs ih =>
    have h1 := Vec.not_mem_of_not_mem_cons h
    have h2 := Vec.ne_of_not_mem_cons h
    simp at h2; subst v
    apply ih h1

theorem Vec.getElem_mem : ∀ {vs : Vec α n} {i : Fin n}, vs[i] ∈ vs
| .nil, i => i.elim0
| .cons x xs, 0 => Mem.head
| .cons x xs, i => by
  induction i using Fin.induction
  simp; apply Mem.head
  simp; apply Mem.tail; apply Vec.getElem_mem


theorem Vec.true_elems {vs : Vec Bool n} {p : Fin n -> Bool}:
  (∀ (i : Fin n), p i = vs.to i) ->
  (¬false ∈ vs) ->
  (∀ (i : Fin n), p i = true)
:= by
  intro h1 h i
  replace h1 := h1 i
  have lem : ∀ v ∈ vs, v = true := by simp [h]
  replace lem := lem (vs.to i);
  rw[h1]; apply lem
  rw[Vec.to_get_elem]
  apply Vec.getElem_mem

theorem Vec.to_eq {α : Type u_1} {vs1 vs2 : Fun.Vec α n} : vs1.to = vs2.to -> vs1 = vs2
:= by
  intro h
  funext; case _ i =>
  rw[Fun.Vec.to_get_elem (vs := vs1), Fun.Vec.to_get_elem (vs := vs2)]
  rw[h]

end Lilac
