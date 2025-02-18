
import SystemFD.Substitution

variable {T : Type} [Repr T] [Inhabited T] [SubstitutionType T] [SubstitutionTypeLaws T]

inductive Frame T where
| empty : Frame T
| kind : T -> Frame T
| type : T -> Frame T
| datatype : T -> Frame T
| ctor : T -> Frame T
| opent : T -> Frame T
| openm : T -> Frame T
| insttype : T -> Frame T
| inst : Nat -> T -> Frame T
| term : T -> T -> Frame T

namespace Frame
  def apply : Frame T -> Subst T -> Frame T
  | empty, _ => empty
  | kind t, σ => kind ([σ]t)
  | type t, σ => type ([σ]t)
  | datatype t, σ => datatype ([σ]t)
  | ctor t, σ => ctor ([σ]t)
  | opent t, σ => opent ([σ]t)
  | openm t, σ => openm ([σ]t)
  | insttype t, σ => insttype ([σ]t)
  | inst n t, σ => inst n ([σ]t)
  | term ty t, σ => term ([σ]ty) ([σ]t)

  omit [Repr T] [Inhabited T] in
  @[simp]
  theorem apply_I {A : Frame T} : A.apply I = A := by
  unfold Frame.apply; cases A <;> simp

  omit [Repr T] [Inhabited T] in
  theorem apply_compose {A : Frame T} : (A.apply σ).apply τ = A.apply (τ ⊙ σ) := by
  unfold apply; cases A <;> simp

  def is_openm (f : Frame T) : Bool :=
    match f with
    | .openm _ => true
    | _ => false

  def is_ctor (f : Frame T) : Bool :=
    match f with
    | .ctor _ => true
    | _ => false

  def is_datatype (f : Frame T) : Bool :=
    match f with
    | .datatype _ => true
    | _ => false

  def is_insttype (f : Frame T) : Bool :=
    match f with
    | .insttype _ => true
    | _ => false

  def is_opent (f : Frame T) : Bool :=
    match f with
    | .opent _ => true
    | _ => false

  def is_stable : Frame T -> Bool
  | .type _ => false
  | .kind _ => false
  | .openm _ => false
  | .term _ _ => false
  | .empty => false
  | _ => true

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_ctor_implies_is_stable : is_ctor f -> is_stable f := by
  intro h; unfold is_ctor at h
  split at h <;> simp at *; unfold is_stable; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_datatype_implies_is_stable : is_datatype f -> is_stable f := by
  intro h; unfold is_datatype at h
  split at h <;> simp at *; unfold is_stable; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_insttype_implies_is_stable : is_insttype f -> is_stable f := by
  intro h; unfold is_insttype at h
  split at h <;> simp at *; unfold is_stable; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_opent_implies_is_stable : is_opent f -> is_stable f := by
  intro h; unfold is_opent at h
  split at h <;> simp at *; unfold is_stable; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_stable_stable {f : Frame T} : is_stable (apply f σ) = is_stable f := by
  cases f <;> unfold is_stable <;> unfold apply <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_ctor_stable {f : Frame T} : is_ctor (apply f σ) = is_ctor f := by
  cases f <;> unfold is_ctor <;> unfold apply <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_datatype_stable {f : Frame T} : is_datatype (apply f σ) = is_datatype f := by
  cases f <;> unfold is_datatype <;> unfold apply <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_insttype_stable {f : Frame T} : is_insttype (apply f σ) = is_insttype f := by
  cases f <;> unfold is_insttype <;> unfold apply <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_opent_stable {f : Frame T} : is_opent (apply f σ) = is_opent f := by
  cases f <;> unfold is_opent <;> unfold apply <;> simp

  def get_type : Frame T -> Option T
  | empty => .none
  | kind t => .some t
  | type t => .some t
  | datatype t => .some t
  | ctor t => .some t
  | opent t => .some t
  | openm t => .some t
  | insttype t => .some t
  | inst _ _ => .none
  | term t _ => .some t

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  @[simp]
  theorem get_type_apply_commute {f : Frame T}
    : (apply f σ).get_type = Option.map ([σ]·) f.get_type
  := by
  unfold Frame.apply; unfold Frame.get_type
  cases f <;> simp

  @[simp]
  def beq [BEq T] : Frame T -> Frame T -> Bool
  | empty, empty => true
  | kind x, kind y => x == y
  | type x, type y => x == y
  | datatype x, datatype y => x == y
  | ctor x, ctor y => x == y
  | opent x, opent y => x == y
  | openm x, openm y => x == y
  | insttype x, insttype y => x == y
  | inst x1 x2, inst y1 y2 => x1 == y1 && x2 == y2
  | term x1 x2, term y1 y2 => x1 == y1 && x2 == y2
  | _, _ => false

  omit [Repr T] [Inhabited T] [SubstitutionType T] in
  theorem eq_of_beq [BEq T] [LawfulBEq T] {a b : Frame T} : beq a b = true -> a = b := by
  intro h; cases a <;> cases b <;> simp at * <;> simp [*]

  protected def reprPrec [reprT : Repr T] (a : Frame T) (p : Nat) : Std.Format :=
    match a with
    | empty => "empty"
    | kind t => "kind " ++ reprT.reprPrec t p
    | type t => "type " ++ reprT.reprPrec t p
    | datatype t => "datatype " ++ reprT.reprPrec t p
    | ctor t => "ctor " ++ reprT.reprPrec t p
    | opent t => "opent " ++ reprT.reprPrec t p
    | openm t => "openm " ++ reprT.reprPrec t p
    | insttype t => "insttype " ++ reprT.reprPrec t p
    | inst x t => "inst " ++ x.repr ++ " := " ++ reprT.reprPrec t p
    | term A t => "term " ++ reprT.reprPrec A p ++ " : " ++ reprT.reprPrec t p
end Frame

instance instRepr_Ctx [Repr T] : Repr (Frame T) where
  reprPrec := Frame.reprPrec

@[simp]
instance instBEq_Frame {T : Type} [BEq T] : BEq (Frame T) where
  beq := Frame.beq

instance instLawfulBEq_Frame {T : Type} [BEq T] [LawfulBEq T] : LawfulBEq (Frame T) where
  eq_of_beq := Frame.eq_of_beq
  rfl := by intro a; cases a <;> simp

def Ctx (T : Type) := List (Frame T)

namespace Ctx
  def apply : Ctx T -> Subst T -> Ctx T
  | [], _ => []
  | .cons hd tl, σ => .cons (hd.apply σ) (apply tl σ)

  omit [Repr T] [Inhabited T] in
  @[simp]
  theorem apply_I {A : Ctx T} : A.apply I = A := by
  unfold Ctx.apply; induction A <;> simp
  case _ ih => unfold Ctx.apply; rw [ih]

  omit [Repr T] [Inhabited T] in
  theorem apply_compose {A : Ctx T} : (A.apply σ).apply τ = A.apply (τ ⊙ σ) := by
  induction A generalizing σ τ <;> unfold Ctx.apply <;> unfold Ctx.apply <;> simp
  case _ hd tl ih =>
    rw [Frame.apply_compose]
    unfold Ctx.apply at ih; rw [ih]
end Ctx

@[simp]
instance instBEq_Ctx {T : Type} [BEq T] : BEq (Ctx T) where
  beq := List.beq

@[simp]
instance instAppend_Ctx : {T : Type} -> Append (Ctx T) where
  append := List.append

@[simp]
instance instHAppend_List_Ctx : {T : Type} -> HAppend (List (Frame T)) (Ctx T) (Ctx T) where
  hAppend := List.append

@[simp]
instance instHAppend_Ctx_List : {T : Type} -> HAppend (Ctx T) (List (Frame T)) (Ctx T) where
  hAppend := List.append


@[simp]
def nth : Ctx T -> Nat -> Frame T
| [], _ => .empty
| .cons f _, 0 => f
| .cons _ t, n + 1 => nth t n

@[simp]
def dnth : Ctx T -> Nat -> Frame T
| [], _ => .empty
| .cons f _, 0 => Frame.apply f S
| .cons _ t, n + 1 => Frame.apply (dnth t n) S

infix:1000 "@" => nth
infix:1000 "d@" => dnth

namespace Ctx
  @[simp]
  def is_openm (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_openm
  @[simp]
  def is_ctor (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_ctor
  @[simp]
  def is_datatype (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_datatype
  @[simp]
  def is_insttype (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_insttype
  @[simp]
  def is_opent (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_opent
  @[simp]
  def is_stable (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_stable
end Ctx

@[simp]
def instance_indices : Ctx T -> Nat -> Nat -> List Nat
| .cons (.inst x _) _, n, 0 => if x == 0 then [n] else []
| .cons (.inst x _) tl, n, y + 1 =>
   if x == y + 1
   then n::instance_indices tl (n + 1) y
   else instance_indices tl (n + 1) y
| .cons _ tl, n, y + 1 => instance_indices tl (n + 1) y
| [], _, _ => []
| _, _, 0 => []


@[simp]
def instance_indices' : Ctx T -> Nat -> Nat -> List Nat -> List Nat
| .nil , _,  _ , acc => acc
| .cons (.inst x _) Γ, n, opm , acc =>
        (if opm == x + n + 1
        then instance_indices' Γ (n+1) opm (n::acc)
        else instance_indices' Γ (n+1) opm acc)
| .cons _ Γ, n, opm , acc => instance_indices' Γ (n + 1) opm acc

@[simp]
def get_instances : Ctx T -> List Nat -> List T
| _, [] => []
| Γ, .cons i t =>
  match Γ d@ i with
  | .inst _ b => b :: get_instances Γ t
  | _ => get_instances Γ t


@[simp]
def instantiate_instances : Ctx T -> List Nat -> Nat -> T -> List T
| _, [], _, _ => []
| Γ, .cons n tl, x, s =>
  match Γ d@ n with
  | .inst _ t => s β[x; t]::instantiate_instances Γ tl x s
  | _ => instantiate_instances Γ tl x s
