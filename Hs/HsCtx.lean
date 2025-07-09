
import SystemFD.Substitution
import Aesop

variable {T : Type} [Repr T] [Inhabited T] [SubstitutionType T] [SubstitutionTypeLaws T]

inductive HsFrame T where
| empty : HsFrame T
| kind : T -> HsFrame T
| type : T -> HsFrame T
| datatypeDecl :
  T -> -- kind of the datatype
  List T -> -- types of the n constructors
  HsFrame T
| classDecl :
  T -> -- kind of the class eg. `ReaderT : ★ → (★ → ★) → ★ → ★`
  List T -> -- superclasses eg. (Monad m)
  List (List Nat × Nat) -> -- the list of functional dependencies. eg. ( m ~> r )
  List T -> -- types of the n open methods
  HsFrame T
| inst :
  T -> -- the class that we are instantiating eg. `Num Int`
  List T -> -- the expression bodies for the open methods
  HsFrame T
| term : T -> T -> HsFrame T

protected def HsFrame.repr [r : Repr T]: (a : HsFrame T) -> (p : Nat) -> Std.Format
| .empty, _ =>
  "empty"
| .kind t, p =>
  "kind " ++ r.reprPrec t p
| .type t, p =>
  "type " ++ r.reprPrec t p
| .term A t, p =>
  Std.Format.nest 5 <| "term " ++ r.reprPrec t p ++ Std.Format.line ++ " : " ++ r.reprPrec A p
| .datatypeDecl t ts, p =>
  Std.Format.nest 10 <| "datatype " ++ r.reprPrec t p ++ Std.Format.line ++ List.repr ts p
| .classDecl t scs fds oms, p =>
  Std.Format.nest 10 <| "classDecl " ++ r.reprPrec t p
      ++ (if scs.isEmpty then Std.Format.nil
         else Std.Format.line ++ " | " ++ List.repr scs p)
      ++ (if fds.isEmpty then Std.Format.nil
         else Std.Format.line ++ " | "
              ++ List.foldl (λ acc t =>
                     acc ++ (Std.Format.text ", ") ++ (t.1.repr p)
                     ++ (Std.Format.text " -> ") ++ t.2.repr) Std.Format.nil fds)
      ++ (if oms.isEmpty then Std.Format.nil
         else Std.Format.line ++ List.repr oms p)
| .inst n ts, p =>
  Std.Format.nest 10 <| "instDecl" ++ r.reprPrec n p ++ Std.Format.line
     ++ List.repr ts p

instance HsFrame_repr : Repr (HsFrame T) where
  reprPrec a p := HsFrame.repr a p

namespace Subst

  def list_lift : Subst T -> List T -> List T := λ σ xs =>
  (List.foldl (λ (σ', xs') x =>  (^σ', ([σ']x :: xs'))) (σ, xs) xs).2

  def lift_k : Nat -> Subst T -> Subst T
  | 0, σ => σ
  | n + 1, σ => lift_k n ^σ

end Subst


namespace HsFrame
  def apply : HsFrame T -> Subst T -> HsFrame T
  | empty, _ => empty
  | kind t, σ => kind ([σ]t)
  | type t, σ => type ([σ]t)
  | datatypeDecl t ctors, σ =>
    datatypeDecl ([σ]t) (Subst.list_lift σ ctors)
  | classDecl t scs fds oms, σ =>
    classDecl ([σ]t) (List.map ([σ]·) scs) fds (Subst.list_lift σ oms) -- TODO FIXME
  | inst v oms, σ => inst ([σ]v) (Subst.list_lift σ oms)
  | term ty t, σ => term ([σ]ty) ([σ]t)

  def get_type : HsFrame T -> Option T
  | .kind t => .some t
  | .type t => .some t
  | .datatypeDecl t _ => .some t
  | .classDecl t _ _ _ => .some t
  | .term T _ => .some T
  | _ => .none

--   omit [Repr T] [Inhabited T] in
--   @[simp]
--   theorem apply_I {A : HsFrame T} : A.apply I = A := by
--   unfold HsFrame.apply; cases A <;> simp

--   omit [Repr T] [Inhabited T] in
--   theorem apply_compose {A : HsFrame T} : (A.apply σ).apply τ = A.apply (τ ⊙ σ) := by
--   unfold apply <;> cases A <;> simp

  -- def is_empty (f : HsFrame T) : Bool :=
  --   match f with
  --   | .empty => true
  --   | _ => false
  @[simp]
  def is_classDecl (f : HsFrame T) : Bool :=
    match f with
    | .classDecl _ _ _ _ => true
    | _ => false

  -- def is_term (f : HsFrame T) : Bool :=
  --   match f with
  --   | .term _ _ => true
  --   | _ => false

  def is_datatypeDecl (f : HsFrame T) : Bool :=
    match f with
    | datatypeDecl _ _ => true
    | _ => false

  -- def is_inst (f : HsFrame T) : Bool :=
  --   match f with
  --   | .inst _ _ => true
  --   | _ => false


  def is_type (f : HsFrame T) : Bool :=
    match f with
    | .type _ => true
    | _ => false


  def is_kind (f : HsFrame T) : Bool :=
    match f with
    | .kind _ => true
    | _ => false

  -- def is_stable : HsFrame T -> Bool
  -- | .type _ => false
  -- | .kind _ => false
  -- | .term _ _ => false
  -- | .empty => false
  -- | _ => true

  -- def is_stable_red : HsFrame T -> Bool
  -- | .type _ => false
  -- | .term _ _ => false
  -- | .empty => false
  -- | _ => true

  -- def is_lam_bound : HsFrame T -> Bool
  -- | .type _ => true
  -- | _ => false


  -- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  -- theorem is_type_apply {σ : Subst T} : is_type f = is_type (apply f σ) := by
  -- unfold apply; unfold is_type; cases f <;> simp

  -- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  -- theorem is_kind_apply {σ : Subst T} : is_kind f = is_kind (apply f σ) := by
  -- unfold apply; unfold is_kind; cases f <;> simp

  -- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  -- theorem is_datatype_apply {σ : Subst T} : is_datatypeDecl f = is_datatypeDecl (apply f σ) := by
  -- unfold apply; unfold is_datatypeDecl; cases f <;> simp

  -- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  -- theorem is_ctor_apply {σ : Subst T} : is_classDecl f = is_classDecl (apply f σ) := by
  -- unfold apply; unfold is_classDecl; cases f <;> simp

  -- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  -- theorem is_stable_apply {σ : Subst T} : is_stable f = is_stable (apply f σ) := by
  -- unfold apply; unfold is_stable; cases f <;> simp

  -- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  -- theorem is_stable_implies_is_stable_red : is_stable f -> is_stable_red f := by
  -- intro h; unfold is_stable at h
  -- split at h <;> simp at *; unfold is_stable_red; simp

  -- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  -- theorem is_term_implies_not_is_stable_red : is_term f -> ¬ is_stable_red f := by
  -- intro h; unfold is_term at h
  -- split at h <;> simp at *; unfold is_stable_red; simp

  -- @[simp]
  -- def beq [BEq T] : HsFrame T -> HsFrame T -> Bool
  -- | empty, empty => true
  -- | kind x, kind y => x == y
  -- | type x, type y => x == y
  -- | datatypeDecl x, datatypeDecl y => x == y
  -- | classDecl x, classDecl y => x == y
  -- | inst x1 x2, inst y1 y2 => x1 == y1 && x2 == y2
  -- | term x1 x2, term y1 y2 => x1 == y1 && x2 == y2
  -- | _, _ => false

  -- omit [Repr T] [Inhabited T] [SubstitutionType T] in
  -- theorem eq_of_beq [BEq T] [LawfulBEq T] {a b : HsFrame T} : beq a b = true -> a = b := by
  -- intro h; cases a <;> cases b <;> simp at * <;> simp [*]

  -- protected def reprPrec [reprT : Repr T] (a : HsFrame T) (p : Nat) : Std.Format :=
  --   match a with
  --   | empty => "empty"
  --   | kind t => "kind " ++ reprT.reprPrec t p
  --   | type t => "type " ++ reprT.reprPrec t p
  --   | datatypeDecl t => "datatype " ++ reprT.reprPrec t p
  --   | classDecl t => "ctor " ++ reprT.reprPrec t p
  --   | inst x t => "inst " ++ reprT.reprPrec x p ++ " := " ++ reprT.reprPrec t p
  --   | term A t => "term " ++ reprT.reprPrec A p ++ " : " ++ reprT.reprPrec t p
end HsFrame

-- instance instRepr_HsCtx [Repr T] : Repr (HsFrame T) where
--   reprPrec := HsFrame.reprPrec

-- @[simp]
-- instance instBEq_HsFrame {T : Type} [BEq T] : BEq (HsFrame T) where
--   beq := HsFrame.beq

-- instance instLawfulBEq_HsFrame {T : Type} [BEq T] [LawfulBEq T] : LawfulBEq (HsFrame T) where
--   eq_of_beq := HsFrame.eq_of_beq
--   rfl := by intro a; cases a <;> simp

def HsCtx (T : Type) := List (HsFrame T)

instance instHsCtx_Append : Append (HsCtx T) where
    append := λ a b => List.append a b -- ideally we may want to shift the indices in a?


-- namespace HsCtx
--   @[aesop safe]
--   def apply : HsCtx T -> Subst T -> HsCtx T
--   | [], _ => []
--   | .cons hd tl, σ => .cons (hd.apply σ) (apply tl σ)

--   omit [Repr T] [Inhabited T] in
--   @[simp]
--   theorem apply_I {A : HsCtx T} : A.apply I = A := by
--   unfold HsCtx.apply; induction A <;> simp
--   case _ ih => unfold HsCtx.apply; rw [ih]

--   omit [Repr T] [Inhabited T] in
--   theorem apply_compose {A : HsCtx T} : (A.apply σ).apply τ = A.apply (τ ⊙ σ) := by
--   induction A generalizing σ τ <;> unfold HsCtx.apply <;> unfold HsCtx.apply <;> simp
--   case _ hd tl ih =>
--     rw [HsFrame.apply_compose]
--     unfold HsCtx.apply at ih; rw [ih]
-- end HsCtx

-- @[simp]
-- instance instBEq_HsCtx {T : Type} [BEq T] : BEq (HsCtx T) where
--   beq := List.beq

-- @[simp]
-- instance instAppend_HsCtx : {T : Type} -> Append (HsCtx T) where
--   append := List.append

-- @[simp]
-- instance instHAppend_List_HsCtx : {T : Type} -> HAppend (List (HsFrame T)) (HsCtx T) (HsCtx T) where
--   hAppend := List.append

-- @[simp]
-- instance instHAppend_HsCtx_List : {T : Type} -> HAppend (HsCtx T) (List (HsFrame T)) (HsCtx T) where
--   hAppend := List.append


@[simp]
def hs_nth : HsCtx T -> Nat -> HsFrame T
| [], _ => .empty
| .cons f _, 0 => f
| .cons _ t, n + 1 => hs_nth t n

@[simp]
def hs_dnth : HsCtx T -> Nat -> HsFrame T
| [], _ => .empty
| .cons f _, 0 => HsFrame.apply f S
-- | .cons (.type _) n + 1 => .some t
-- | .datatypeDecl t _ => .some t
-- | .classDecl t _ _ _ => .some t
-- | .term T _ => .some T


| .cons _ t, n + 1 => HsFrame.apply (hs_dnth t n) S

infix:1000 "@̈" => hs_nth
infix:1000 "d@̈" => hs_dnth

namespace HsCtx
  @[simp]
  def is_type (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_type
  @[simp]
  def is_pred (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_type
  @[simp]
  def is_kind (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_kind
  @[simp]
  def is_datatypeDecl (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_datatypeDecl
  @[simp]
  def is_classDecl (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_classDecl
--   @[simp]
--   def is_stable (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_stable
--   @[simp]
--   def is_stable_red (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_stable_red
--   @[simp]
--   def is_lam_bound (Γ : HsCtx T) (n : Nat) : Bool := (Γ d@̈ n).is_lam_bound
end HsCtx

-- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
-- theorem hs_kind_indexing_exists {Γ : HsCtx T} :
--   (Γ d@̈ n).is_kind = true ->
--   ∃ t, Γ d@̈ n = .kind t := by
-- intros h; unfold HsFrame.is_kind at h; split at h;
-- case _ a h' => apply Exists.intro a; assumption
-- case _ => cases h

-- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
-- theorem hs_type_indexing_exists {Γ : HsCtx T} :
--   (Γ d@̈ n).is_type = true ->
--   ∃ t, Γ d@̈ n = .type t := by
-- intros h; unfold HsFrame.is_type at h; split at h;
-- case _ a h' => apply Exists.intro a; assumption
-- case _ => cases h


-- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
-- theorem hs_term_indexing_exists {Γ : HsCtx T} :
--   (Γ d@̈ n).is_term = true ->
--   ∃ A t, Γ d@̈ n = .term A t := by
-- intros h; unfold HsFrame.is_term at h; split at h;
-- case _ a T h' => exists a; exists T
-- case _ => cases h


-- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
-- theorem hs_datatype_indexing_exists {Γ : HsCtx T} :
--   (Γ d@̈ n).is_datatypeDecl = true ->
--   ∃ t, Γ d@̈ n = datatype t := by
-- intros h; unfold HsFrame.is_datatypeDecl at h; split at h;
-- case _ a h' => apply Exists.intro a; assumption
-- case _ => cases h

-- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
-- theorem hs_class_indexing_exists {Γ : HsCtx T} :
--   (Γ d@̈ n).is_classDecl = true ->
--   ∃ t, Γ d@̈ n = .classDecl t := by
-- intros h; unfold HsFrame.is_classDecl at h; split at h;
-- case _ a h' => apply Exists.intro a; assumption
-- case _ => cases h

-- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
-- theorem hs_indexing_uniqueness_datatype {Γ : HsCtx T} :
--   (Γ d@̈ t).is_datatypeDecl ->
--   (Γ d@̈ t).is_classDecl -> False := by
-- intro h1 h2;
-- replace h1 := hs_datatype_indexing_exists h1;
-- cases h1; case _ h1 =>
-- rw [h1]at h2; unfold HsFrame.is_classDecl at h2; simp at h2

-- omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
-- theorem hs_indexing_uniqueness_opent {Γ : HsCtx T} :
--   (Γ d@̈ t).is_classDecl ->
--   (Γ d@̈ t).is_datatypeDecl -> False := by
-- intro h1 h2;
-- replace h1 := hs_class_indexing_exists h1;
-- cases h1; case _ h1 =>
-- rw [h1]at h2; unfold HsFrame.is_datatypeDecl at h2; simp at h2
