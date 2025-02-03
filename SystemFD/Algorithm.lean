import SystemFD.Term
import SystemFD.Ctx
set_option maxHeartbeats 500000

@[simp]
def wf_kind : Term -> Option Unit
| .const _ => .some ()
| .ctor2 .arrowk A B => do
  let _ <- wf_kind A
  let _ <- wf_kind B
  .some ()
| _ => .none

@[simp]
def is_openm : Frame Term -> Option Term
| .openm T => .some T
| _ => .none

@[simp]
def is_const : Term -> Option Const
| .const K => .some K
| _ => .none

@[simp]
def is_pointed : Term -> Option Unit
| .const .pointed => .some ()
| _ => .none

@[simp]
def is_unpointed : Term -> Option Unit
| .const .unpointed => .some ()
| _ => .none

@[simp]
def is_arrowk : Term -> Option (Term × Term)
| .ctor2 .arrowk A B => .some (A, B)
| _ => .none

@[simp]
def is_arrow : Term -> Option (Term × Term)
| .ctor2 .arrow A B => .some (A, B)
| _ => .none

@[simp]
def is_eq : Term -> Option (Term × Term)
| .ctor2 .eq A B => .some (A, B)
| _ => .none

@[simp]
def is_appk : Term -> Option (Term × Term)
| .ctor2 .appk A B => .some (A, B)
| _ => .none


@[simp]
def is_all : Term -> Option (Term × Term)
| .bind2 .all A B => .some (A, B)
| _ => .none

@[simp]
def infer_kind : Ctx Term -> Term -> Option Term
| Γ, #x => do
  let T <- Frame.get_type (Γ d@ x)
  let _ <- wf_kind T
  .some T
| Γ, ∀[A] B => do
  let _ <- wf_kind A
  let Bk <- infer_kind (.kind A::Γ) B
  let _ <- wf_kind Bk
  .some Bk
| Γ, .ctor2 .arrow A B => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  let Bk <- infer_kind Γ B
  let K <- is_const Bk
  .some (.const K)
| Γ, .ctor2 .appk f a => do
  let fk <- infer_kind Γ f
  let (A, B) <- is_arrowk fk
  let ak <- infer_kind Γ a
  if A == ak then .some B else .none
| Γ, .ctor2 .eq A B => do
  let Ak <- infer_kind Γ A
  let Bk <- infer_kind Γ B
  if Ak == ★ && Bk == ★ then .some ◯ else .none
| _, _ => .none

inductive InferTypeVariant where
| prf | ctor

@[simp]
abbrev InferTypeArgs : (v : InferTypeVariant) -> Type
| .prf => Ctx Term × Term
| .ctor => Ctx Term × Term × Nat

namespace InferTypeArgs
  @[simp]
  def size1 : (v : InferTypeVariant) -> InferTypeArgs v -> Nat
  | .prf, (_, t) => Term.size t
  | .ctor, (_, t, _) => Term.size t

  @[simp]
  def size2 : (v : InferTypeVariant) -> InferTypeArgs v -> Nat
  | .prf, (_, t) => Term.size t
  | .ctor, (_, t, n) => Term.size t + n + 1
end InferTypeArgs

@[simp]
def infer_type : (v : InferTypeVariant) -> InferTypeArgs v -> Option Term
| .prf, (Γ, .letdata T n t) => do
  let _ <- wf_kind T
  let A <- infer_type .ctor (.datatype T n::Γ, t, n)
  .some A
| .ctor, (Γ, .bind2 .letctor T t, n + 1) => do
  let Tk <- infer_kind Γ T
  let _ <- is_pointed Tk
  let A <- infer_type .ctor (.ctor T::Γ, t, n)
  .some A
| .ctor, (Γ, t, 0) => infer_type .prf (Γ, t)
| .prf, (Γ, .bind2 .letopentype T t) => do
  let _ <- wf_kind T
  let A <- infer_type .prf (.opent T::Γ, t)
  .some A
| .prf, (Γ, .bind2 .letopen T t) => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let A <- infer_type .prf (.openm T::Γ, t)
  .some A
| .prf, (Γ, .bind2 .insttype T t) => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let A <- infer_type .prf (.insttype T::Γ, t)
  .some A
| .prf, (Γ, .inst x t1 t2) => do
  let T <- is_openm (Γ d@ x)
  let T' <- infer_type .prf (Γ, t1)
  let A <- infer_type .prf (.inst x t1::Γ, t2)
  if T == T' then .some A else .none
| .prf, (Γ, .letterm T b t) => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let B <- infer_type .prf (Γ , b)
  let A <- infer_type .prf (.term T b::Γ, t)
  if T == B then .some A else .none
| .prf, (Γ, #x) => do
  let T <- Frame.get_type (Γ d@ x)
  let _ <- infer_kind Γ T
  .some T
| .prf, (Γ, .ite p s i e) => do
  let A <- infer_type .prf (Γ, p)
  let (τ, R) := Term.to_telescope A
  let ctorid <- Term.neutral_head p
  let dataid <- Term.neutral_head R
  let Rk <- infer_kind Γ R
  let _ <- is_pointed Rk
  let R' <- infer_type .prf (Γ, s)
  let B <- infer_type .prf (Γ, i)
  let (τ', T) := Term.to_telescope B
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let T' <- infer_type .prf (Γ, e)
  if R == R'
    && τ == τ'
    && T == T'
    && is_datatype Γ ctorid dataid
  then .some T
  else .none
| .prf, (Γ, .guard p s t) => do
  let A <- infer_type .prf (Γ, p)
  let (τ, R) := Term.to_telescope A
  let Rk <- infer_kind Γ R
  let _ <- is_unpointed Rk
  let R' <- infer_type .prf (Γ, s)
  let B <- infer_type .prf (Γ, t)
  let (τ', T) := Term.to_telescope B
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  if R == R' && τ == τ' then .some T else .none
| .prf, (Γ, `λ[A] t) => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  let B <- infer_type .prf (.type A::Γ, t)
  .some (A -t>  ([P] B) )
| .prf, (Γ, .ctor2 .app f a) => do
  let T <- infer_type .prf (Γ, f)
  let (A, B) <- is_arrow T
  let A' <- infer_type .prf (Γ, a)
  if A == A' then .some B else .none
| .prf, (Γ, Λ[A] t) => do
  -- let Ak <- infer_kind Γ A
  let _ <- wf_kind A
  let B <- infer_type .prf (.kind A::Γ, t)
  .some (∀[A] B)
| .prf, (Γ, .ctor2 .appt f a) => do
  let T <- infer_type .prf (Γ, f)
  let (A, B) <- is_all T
  let A' <- infer_type .prf (Γ, a)
  if A == A' then .some B else .none
| .prf, (Γ, .ctor2 .cast t c) => do
  let A <- infer_type .prf (Γ, t)
  let T <- infer_type .prf (Γ, c)
  let (A', B) <- is_eq T
  if A == A' then .some B else .none
| .prf, (Γ, .ctor1 .refl A) => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  .some A
| .prf, (Γ, .ctor1 .sym t) => do
  let T <- infer_type .prf (Γ, t)
  let (A, B) <- is_eq T
  .some (B ~ A)
| .prf, (Γ, .ctor2 .seq t1 t2) => do
  let T1 <- infer_type .prf (Γ, t1)
  let T2 <- infer_type .prf (Γ, t2)
  let (A, B) <- is_eq T1
  let (B', C) <- is_eq T2
  if B == B' then .some (A ~ C) else .none
| .prf, (Γ, .ctor2 .appc f a) => do
  let T1 <- infer_type .prf (Γ, f)
  let T2 <- infer_type .prf (Γ, a)
  let (A, B) <- is_eq T1
  let (C, D) <- is_eq T2
  .some ((A `@k C) ~ (B `@k D))
| .prf, (Γ, .ctor2 .arrowc t1 t2) => do
  let T1 <- infer_type .prf (Γ, t1)
  let T2 <- infer_type .prf (Γ, t2)
  let (A, B) <- is_eq T1
  let (C, D) <- is_eq T2
  .some ((A -t> C) ~ (B -t> D))
| .prf, (Γ, .ctor1 .fst t) => do
  let T <- infer_type .prf (Γ, t)
  let (U, V) <- is_eq T
  let (A, _) <- is_appk U
  let (B, _) <- is_appk V
  .some (A ~ B)
| .prf, (Γ, .ctor1 .snd t) => do
  let T <- infer_type .prf (Γ, t)
  let (U, V) <- is_eq T
  let (_, C) <- is_appk U
  let (_, D) <- is_appk V
  .some (C ~ D)
| .prf, (Γ, ∀c[K] t) => do
  let T <- infer_type .prf (.kind K :: Γ, t)
  let (A, B) <- is_eq T
  .some ((∀[K] A) ~ (∀[K] B))
| .prf, (Γ, f `@c[a]) => do
  let T1 <- infer_type .prf (Γ, f)
  let T2 <- infer_type .prf (Γ, a)
  let (U, V) <- is_eq T1
  let (K1, A) <- is_all U
  let (K2, B) <- is_all V
  let (C, D) <- is_eq T2
  if K1 == K2 then .some ((A β[C]) ~ (B β[D])) else .none
| .prf, _ => .none
| .ctor, _ => .none
termination_by v t => (InferTypeArgs.size1 v t, InferTypeArgs.size2 v t)

inductive WfCtxTypeVariant where
| wf | ctor

@[simp]
abbrev WfCtxTypeArgs : (v : WfCtxTypeVariant) -> Type
| .wf => Ctx Term
| .ctor => Ctx Term × Nat

namespace WfCtxTypeArgs
  @[simp]
  def size1 : (v : WfCtxTypeVariant) -> WfCtxTypeArgs v -> Nat
  | .wf, Γ => Γ.length
  | .ctor, (Γ, _) => Γ.length

  @[simp]
  def size2 : (v : WfCtxTypeVariant) -> WfCtxTypeArgs v -> Nat
  | .wf, Γ => Γ.length
  | .ctor, (Γ, n) => Γ.length + n + 1
end WfCtxTypeArgs

@[simp]
def wf_ctx : (v : WfCtxTypeVariant) -> WfCtxTypeArgs v -> Option Unit
| .wf, [] => .some .unit
| .wf, .cons (.type A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  wf_ctx .wf Γ
| .wf, .cons (.kind A) Γ => do
  let _ <- wf_kind A
  wf_ctx .wf Γ
| .wf, .cons (.datatype A n) Γ => do
  let _ <- wf_kind A
  wf_ctx .ctor (Γ, n)
| .ctor, (.cons (.ctor A) Γ, n + 1) => do
  let Ak <- infer_kind Γ A
  let _ <- is_pointed Ak
  wf_ctx .ctor (Γ, n)
| .ctor, (Γ, 0) => wf_ctx .wf Γ
| .wf, .cons (.opent A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  wf_ctx .wf Γ
| .wf, .cons (.openm A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  wf_ctx .wf Γ
| .wf, .cons (.insttype A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  wf_ctx .wf Γ
| .wf, .cons (.term A t) Γ => do
  let A' <- infer_type .prf (Γ, t)
  let _ <- wf_ctx .wf Γ
  if A == A' then .some () else .none
| .wf, .cons (.inst x t) Γ =>
  match Γ d@ x with
  | .openm T => do
    let T' <- infer_type .prf (Γ, t)
    if T == T' then .some () else .none
  | _ => .none
| .wf, _ => .none
| .ctor, _ => .none
termination_by v t => (WfCtxTypeArgs.size1 v t, WfCtxTypeArgs.size2 v t)
