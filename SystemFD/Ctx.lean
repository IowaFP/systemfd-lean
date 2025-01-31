
import SystemFD.Substitution

variable {T : Type} [Inhabited T] [SubstitutionType T] [SubstitutionTypeLaws T]

inductive Frame T where
| empty : Frame T
| kind : T -> Frame T
| type : T -> Frame T
| datatype : T -> Nat -> Frame T
| ctor : T -> Frame T
| opent : T -> Frame T
| openm : T -> Frame T
| insttype : T -> Frame T
| inst : Nat -> T -> Frame T
| term : T -> T -> Frame T

namespace Frame
  @[simp]
  def apply : Frame T -> Subst T -> Frame T
  | empty, _ => empty
  | kind t, σ => kind ([σ]t)
  | type t, σ => type ([σ]t)
  | datatype t n, σ => datatype ([σ]t) n
  | ctor t, σ => ctor ([σ]t)
  | opent t, σ => opent ([σ]t)
  | openm t, σ => openm ([σ]t)
  | insttype t, σ => insttype ([σ]t)
  | inst n t, σ => inst n ([σ]t)
  | term ty t, σ => term ([σ]ty) ([σ]t)

  def get_type : Frame T -> Option T
  | empty => .none
  | kind t => .some t
  | type t => .some t
  | datatype t _ => .some t
  | ctor t => .some t
  | opent t => .some t
  | openm t => .some t
  | insttype t => .some t
  | inst _ _ => .none
  | term ty _ => .some ty -- not really a type...

  @[simp]
  def beq [BEq T] : Frame T -> Frame T -> Bool
  | empty, empty => true
  | kind x, kind y => x == y
  | type x, type y => x == y
  | datatype x1 x2, datatype y1 y2 => x1 == y1 && x2 == y2
  | ctor x, ctor y => x == y
  | opent x, opent y => x == y
  | openm x, openm y => x == y
  | insttype x, insttype y => x == y
  | inst x1 x2, inst y1 y2 => x1 == y1 && x2 == y2
  | term x1 x2, term y1 y2 => x1 == y1 && x2 == y2
  | _, _ => false
end Frame

@[simp]
instance instBEq_Frame {T : Type} [BEq T] : BEq (Frame T) where
  beq := Frame.beq

def Ctx (T : Type) := List (Frame T)

@[simp]
instance instBEq_Ctx {T : Type} [BEq T] : BEq (Ctx T) where
  beq := List.beq

@[simp]
instance instAppend_Ctx : {T : Type} -> Append (Ctx T) where
  append := List.append

@[simp]
def is_datatype : Ctx T -> Nat -> Nat -> Bool
| .cons _ t, c + 1, d + 1 => is_datatype t c d
| .cons (.ctor _) t, 0, d + 1 => is_datatype t 0 d
| .cons (.datatype _ _) _, 0, 0 => true
| _, _, _ => false

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

@[simp]
def instance_indices : Ctx T -> Nat -> Nat -> List Nat
| .cons (.inst x _) _, n, 0 => if x == 0 then [n] else []
| .cons (.inst x _) tl, n, y + 1 => if x == y + 1 then n::instance_indices tl (n + 1) y else instance_indices tl (n + 1) y
| .cons _ tl, n, y + 1 => instance_indices tl (n + 1) y
| [], _, _ => []
| _, _, 0 => []

@[simp]
def instantiate_instances : Ctx T -> List Nat -> Nat -> T -> List T
| _, [], _, _ => []
| Γ, .cons n tl, x, s =>
  match Γ d@ n with
  | .inst _ t => s β[x; t]::instantiate_instances Γ tl x s
  | _ => instantiate_instances Γ tl x s
