import SystemFD.Term
import SystemFD.Ctx

@[simp]
def wf_kind : Term -> Option Unit
| .const _ => .some ()
| .arrowk A B => do
  let _ <- wf_kind A
  let _ <- wf_kind B
  .some ()
| _ => .none

inductive InferKindVariant where
| prf | wf

@[simp]
abbrev InferKindArgs : (v : InferKindVariant) -> Type
| .prf => Ctx Term × Term
| .wf => Ctx Term

namespace InferKindArgs
  @[simp]
  def size1 : (v : InferKindVariant) -> InferKindArgs v -> Nat
  | .prf, (_, t) => Term.size t
  | .wf, _ => 0

  @[simp]
  def size2 : (v : InferKindVariant) -> InferKindArgs v -> Nat
  | .prf, (Γ, _) => Γ.length + 1
  | .wf, Γ => Γ.length

end InferKindArgs

@[simp]
abbrev InferKindRet : (v : InferKindVariant) -> Type
| .prf => Option Term
| .wf => Option Unit

@[simp]
def is_const : Term -> Option Const
| _ => sorry

@[simp]
def is_arrowk : Term -> Option (Term × Term)
| _ => sorry

@[simp]
def infer_kind : (v : InferKindVariant) -> InferKindArgs v -> InferKindRet v
| .prf, (Γ, #x) => do
  let _ <- infer_kind .wf Γ
  Frame.get_type (Γ d@ x)
| .prf, (Γ, ∀[A] B) => do
  let _ <- wf_kind A
  let Bk <- infer_kind .prf (.kind A::Γ, B)
  let _ <- wf_kind Bk
  .some Bk
| .prf, (Γ, A -t> B) => do
  let Ak <- infer_kind .prf (Γ, A)
  let _ <- is_const Ak
  let Bk <- infer_kind .prf (Γ, B)
  let K <- is_const Bk
  .some (.const K)
| .prf, (Γ, f `@k a) => do
  let fk <- infer_kind .prf (Γ, f)
  let (A, B) <- is_arrowk fk
  let ak <- infer_kind .prf (Γ, a)
  if A == ak then .some B else .none
| .prf, (Γ, A ~ B) => do
  let Ak <- infer_kind .prf (Γ, A)
  let Bk <- infer_kind .prf (Γ, B)
  if Ak == ★ && Bk == ★ then .some ◯ else .none
| .prf, _ => .none
| .wf, [] => .some ()
| .wf, (.cons (.kind A) Γ) => do
  let _ <- wf_kind A
  infer_kind .wf Γ
| .wf, (.cons _ Γ) => infer_kind .wf Γ
termination_by v args => (InferKindArgs.size1 v args, InferKindArgs.size2 v args)
