
import SystemFD.Substitution
-- import Aesop

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
| inst : T -> T -> Frame T
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
  | inst v t, σ => inst ([σ]v) ([σ]t)
  | term ty t, σ => term ([σ]ty) ([σ]t)

  omit [Repr T] [Inhabited T] in
  @[simp]
  theorem apply_I {A : Frame T} : A.apply I = A := by
  unfold Frame.apply; cases A <;> simp

  omit [Repr T] [Inhabited T] in
  theorem apply_compose {A : Frame T} : (A.apply σ).apply τ = A.apply (τ ⊙ σ) := by
  unfold apply <;> cases A <;> simp

  def is_empty (f : Frame T) : Bool :=
    match f with
    | .empty => true
    | _ => false

  def is_openm (f : Frame T) : Bool :=
    match f with
    | .openm _ => true
    | _ => false

 def is_term (f : Frame T) : Bool :=
    match f with
    | .term _ _ => true
    | _ => false

  def is_ctor (f : Frame T) : Bool :=
    match f with
    | .ctor _ => true
    | _ => false

  -- @[aesop safe]
  def is_datatype (f : Frame T) : Bool :=
    match f with
    | .datatype _ => true
    | _ => false

  def is_insttype (f : Frame T) : Bool :=
    match f with
    | .insttype _ => true
    | _ => false

  def is_inst (f : Frame T) : Bool :=
    match f with
    | .inst _ _ => true
    | _ => false

  def is_opent (f : Frame T) : Bool :=
    match f with
    | .opent _ => true
    | _ => false

  def is_type (f : Frame T) : Bool :=
    match f with
    | .type _ => true
    | _ => false

  -- @[aesop safe]
  def is_kind (f : Frame T) : Bool :=
    match f with
    | .kind _ => true
    | _ => false

  def is_stable : Frame T -> Bool
  | .type _ => false
  | .kind _ => false
  | .openm _ => false
  | .term _ _ => false
  | .empty => false
  | _ => true

  def is_stable_red : Frame T -> Bool
  | .type _ => false
  | .openm _ => false
  | .term _ _ => false
  | .empty => false
  | _ => true

  def is_lam_bound : Frame T -> Bool
  | .type _ => true
  | _ => false

  def is_term_var : Frame T -> Bool := λ x => x.is_type || x.is_term || x.is_ctor

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_type_apply {σ : Subst T} : is_type f = is_type (apply f σ) := by
  unfold apply; unfold is_type; cases f <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_kind_apply {σ : Subst T} : is_kind f = is_kind (apply f σ) := by
  unfold apply; unfold is_kind; cases f <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_datatype_apply {σ : Subst T} : is_datatype f = is_datatype (apply f σ) := by
  unfold apply; unfold is_datatype; cases f <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_ctor_apply {σ : Subst T} : is_ctor f = is_ctor (apply f σ) := by
  unfold apply; unfold is_ctor; cases f <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_stable_apply {σ : Subst T} : is_stable f = is_stable (apply f σ) := by
  unfold apply; unfold is_stable; cases f <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_insttype_apply {σ : Subst T} : is_insttype f = is_insttype (apply f σ) := by
  unfold apply; unfold is_insttype; cases f <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_openm_apply {σ : Subst T} : is_openm f = is_openm (apply f σ) := by
  unfold apply; unfold is_openm; cases f <;> simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_openm_destruct : is_openm f -> ∃ T, f = .openm T := by
  intro h; unfold is_openm at h
  split at h <;> simp at *

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_stable_implies_is_stable_red : is_stable f -> is_stable_red f := by
  intro h; unfold is_stable at h
  split at h <;> simp at *; unfold is_stable_red; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_openm_implies_not_is_stable_red : is_openm f -> ¬ is_stable_red f := by
  intro h; unfold is_openm at h
  split at h <;> simp at *; unfold is_stable_red; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_term_implies_not_is_stable_red : is_term f -> ¬ is_stable_red f := by
  intro h; unfold is_term at h
  split at h <;> simp at *; unfold is_stable_red; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_ctor_implies_is_stable : is_ctor f -> is_stable f := by
  intro h; unfold is_ctor at h
  split at h <;> simp at *; unfold is_stable; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_ctor_implies_is_stable_red : is_ctor f -> is_stable_red f := by
  intro h; unfold is_ctor at h
  split at h <;> simp at *; unfold is_stable_red; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_datatype_implies_is_stable : is_datatype f -> is_stable f := by
  intro h; unfold is_datatype at h
  split at h <;> simp at *; unfold is_stable; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_datatype_implies_is_stable_red : is_datatype f -> is_stable_red f := by
  intro h; unfold is_datatype at h
  split at h <;> simp at *; unfold is_stable_red; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_insttype_implies_is_stable : is_insttype f -> is_stable f := by
  intro h; unfold is_insttype at h
  split at h <;> simp at *; unfold is_stable; simp

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem is_insttype_implies_is_stable_red : is_insttype f -> is_stable_red f := by
  intro h; unfold is_insttype at h
  split at h <;> simp at *; unfold is_stable_red; simp


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

  -- @[aesop safe]
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

  omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T] in
  theorem get_type_apply_eq_destruct {f : Frame T}
    : some A = (f.apply σ).get_type -> ∃ A', A = [σ]A' ∧ some A' = f.get_type
  := by
  intro h; unfold Frame.apply at h; unfold Frame.get_type at h
  cases f <;> simp at h
  case term _ B t => exists B
  all_goals (case _ A => exists A)

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
    | empty => ".empty"
    | kind t => ".kind " ++ Std.Format.paren (reprT.reprPrec t 0)
    | type t => ".type " ++ Std.Format.paren (reprT.reprPrec t 0)
    | datatype t => ".datatype " ++ Std.Format.paren (reprT.reprPrec t 0)
    | ctor t => ".ctor " ++ Std.Format.paren (reprT.reprPrec t 0)
    | opent t => ".opent " ++ Std.Format.paren (reprT.reprPrec t 0)
    | openm t => ".openm " ++ Std.Format.paren (reprT.reprPrec t 0)
    | insttype t => ".insttype " ++ Std.Format.paren (reprT.reprPrec t 0)
    | inst x t =>
      Std.Format.nest 5 <| ".inst " ++ reprT.reprPrec x p ++ " := "
      ++ Std.Format.line ++ Std.Format.paren (reprT.reprPrec t 0)
    | term A t =>
      Std.Format.nest 5 <| ".term "
      ++ Std.Format.line ++ Std.Format.paren (reprT.reprPrec A 0)
      ++ " : " ++ Std.Format.paren (reprT.reprPrec t 0)
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

instance inst_ReprCtx [Repr T] : Repr (Ctx T) where
  reprPrec t p := List.repr t p

namespace Ctx
  @[simp]
  def add : Ctx T -> Frame T -> Ctx T
  | Γ, f => f :: Γ

  -- @[aesop safe]
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
  def is_term (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_term
  @[simp]
  def is_ctor (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_ctor
  @[simp]
  def is_datatype (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_datatype
  @[simp]
  def is_kind (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_kind
  @[simp]
  def is_insttype (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_insttype
  @[simp]
  def is_opent (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_opent
  @[simp]
  def is_type (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_type
  @[simp]
  def is_stable (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_stable
  @[simp]
  def is_stable_red (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_stable_red
  @[simp]
  def is_lam_bound (Γ : Ctx T) (n : Nat) : Bool := (Γ d@ n).is_lam_bound
end Ctx

omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem kind_indexing_exists {Γ : Ctx T} :
  (Γ d@ n).is_kind = true ->
  ∃ t, Γ d@ n = .kind t := by
intros h; unfold Frame.is_kind at h; split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h

omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem type_indexing_exists {Γ : Ctx T} :
  (Γ d@ n).is_type = true ->
  ∃ t, Γ d@ n = .type t := by
intros h; unfold Frame.is_type at h; split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h


omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem term_indexing_exists {Γ : Ctx T} :
  (Γ d@ n).is_term = true ->
  ∃ A t, Γ d@ n = .term A t := by
intros h; unfold Frame.is_term at h; split at h;
case _ a T h' => exists a; exists T
case _ => cases h


omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem datatype_indexing_exists {Γ : Ctx T} :
  (Γ d@ n).is_datatype = true ->
  ∃ t, Γ d@ n = .datatype t := by
intros h; unfold Frame.is_datatype at h; split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h

omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem insttype_indexing_exists {Γ : Ctx T} :
  (Γ d@ n).is_insttype = true ->
  ∃ t, Γ d@ n = .insttype t := by
intros h; unfold Frame.is_insttype at h; split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h

omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem opent_indexing_exists {Γ : Ctx T} :
  (Γ d@ n).is_opent = true ->
  ∃ t, Γ d@ n = .opent t := by
intros h; unfold Frame.is_opent at h; split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h

omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem ctor_indexing_exists {Γ : Ctx T} :
  (Γ d@ n).is_ctor = true ->
  ∃ t, Γ d@ n = .ctor t := by
intros h; unfold Frame.is_ctor at h; split at h;
case _ a h' => apply Exists.intro a; assumption
case _ => cases h


omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem indexing_uniqueness_datatype {Γ : Ctx T} :
  (Γ d@ t).is_datatype ->
  (Γ d@ t).is_opent -> False := by
intro h1 h2;
replace h1 := datatype_indexing_exists h1;
cases h1; case _ h1 =>
rw [h1]at h2; unfold Frame.is_opent at h2; simp at h2

omit [Repr T] [Inhabited T] [SubstitutionTypeLaws T]
theorem indexing_uniqueness_opent {Γ : Ctx T} :
  (Γ d@ t).is_opent ->
  (Γ d@ t).is_datatype -> False := by
intro h1 h2;
replace h1 := opent_indexing_exists h1;
cases h1; case _ h1 =>
rw [h1]at h2; unfold Frame.is_datatype at h2; simp at h2


theorem replace_eq_except n f : (Γ Γ' : Ctx T) ->
  Γ.modify n (λ _ => f) = Γ' ->
  ∀ k, k ≠ n -> Γ d@ k = Γ' d@ k
:= by
intro Γ Γ' j1 k j2
rw[<-j1];
cases Γ;
case _ => simp
case _ hd tl =>
  cases Γ' <;> simp at *;
  case _ hd' tl' =>
    unfold List.modify at j1;
    cases n <;> simp at *
    cases j1; case _ e1 e2 =>
      cases e1; cases e2;
      cases k <;> simp; simp at j2
    cases k <;> simp at *
    cases j1; case _ e1 e2 =>
      case _ n k =>
      have lem := @replace_eq_except n f tl tl' e2 k j2
      unfold List.modify; rw[e2]; rw[lem]
