
import SystemFD.Substitution
-- import Aesop

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
| tyfam : T -> HsFrame T -- `type family F :: ★ → ★`
| tyfaminst : T -> T -> HsFrame T -- type instance F Int = Bool

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
| .tyfam t, p =>
  Std.Format.nest 10 <| "type family " ++ r.reprPrec t p
| .tyfaminst t1 t2, p =>
  Std.Format.nest 10 <| "type instance " ++ r.reprPrec t1 p ++ " = " ++ r.reprPrec t2 p

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
  | tyfam t, σ => tyfam ([σ]t)
  | tyfaminst t1 t2, σ => tyfaminst ([σ]t1) ([σ]t2)

  def get_type : HsFrame T -> Option T
  | .kind t => .some t
  | .type t => .some t
  | .datatypeDecl t _ => .some t
  | .classDecl t _ _ _ => .some t
  | .term t _ => .some t
  | .tyfam t => .some t
  | _ => .none

  @[simp]
  def is_classDecl (f : HsFrame T) : Bool :=
    match f with
    | .classDecl _ _ _ _ => true
    | _ => false

  def is_term (f : HsFrame T) : Bool :=
    match f with
    | .term _ _ => true
    | _ => false

  def is_datatypeDecl (f : HsFrame T) : Bool :=
    match f with
    | datatypeDecl _ _ => true
    | _ => false

  def is_inst (f : HsFrame T) : Bool :=
    match f with
    | .inst _ _ => true
    | _ => false


  def is_type (f : HsFrame T) : Bool :=
    match f with
    | .type _ => true
    | _ => false


  def is_kind (f : HsFrame T) : Bool :=
    match f with
    | .kind _ => true
    | _ => false

  def is_tyfam (f : HsFrame T) : Bool :=
    match f with
    | .tyfam _ => true
    | _ => false

end HsFrame

def HsCtx (T : Type) := List (HsFrame T)

instance instHsCtx_Append : Append (HsCtx T) where
    append := λ a b => List.append a b -- ideally we may want to shift the indices in a?

instance instHsCtxt_repr [Repr T]: Repr (HsCtx T) where
  reprPrec a p := List.repr a p
