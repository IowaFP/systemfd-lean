import SystemFD.Util
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
| .bind2 .arrow A B => .some (A, B)
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
| Γ, .bind2 .arrow A B => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  let Bk <- infer_kind (.type A::Γ) B
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

@[simp]
def infer_type : Ctx Term -> Term -> Option Term
| Γ, .letdata T t => do
  let _ <- wf_kind T
  let A <- infer_type (.datatype T::Γ) t
  .some A
| Γ, .bind2 .letctor T t => do
  let Tk <- infer_kind Γ T
  let _ <- is_pointed Tk
  let A <- infer_type (.ctor T::Γ) t
  if valid_ctor Γ then .some A else .none
| Γ, .bind2 .letopentype T t => do
  let _ <- wf_kind T
  let A <- infer_type (.opent T::Γ) t
  .some A
| Γ, .bind2 .letopen T t => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let A <- infer_type (.openm T::Γ) t
  .some A
| Γ, .bind2 .insttype T t => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let A <- infer_type (.insttype T::Γ) t
  .some A
| Γ, .inst x t1 t2 => do
  let T <- is_openm (Γ d@ x)
  let T' <- infer_type Γ t1
  let A <- infer_type (.inst x t1::Γ) t2
  if T == T' then .some A else .none
| Γ, .letterm T b t => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let B <- infer_type Γ b
  let A <- infer_type (.term T b::Γ) t
  if T == B then .some A else .none
| Γ, #x => do
  let T <- Frame.get_type (Γ d@ x)
  let _ <- infer_kind Γ T
  .some T
| Γ, .ite p s i e => do
  let A <- infer_type Γ p
  let (τ, sR) := Term.to_telescope A
  let R := [P' τ.length]sR
  let (ctorid, _) <- Term.neutral_form p
  let (dataid, _) <- Term.neutral_form R
  let Rk <- infer_kind Γ R
  let _ <- is_pointed Rk
  let R' <- infer_type Γ s
  let B <- infer_type Γ i
  let (τ', sT) := Term.to_telescope B
  let ξ <- prefix_equal τ τ'
  let sT' := Term.from_telescope ξ sT
  let T := [P' τ.length]sT'
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let T' <- infer_type Γ e
  if R == R'
    && T == T'
    && is_datatype Γ ctorid dataid
  then .some T
  else .none
| Γ, .guard p s t => do
  let A <- infer_type Γ p
  let (τ, sR) := Term.to_telescope A
  let R := [P' τ.length]sR
  let Rk <- infer_kind Γ R
  let _ <- is_unpointed Rk
  let R' <- infer_type Γ s
  let B <- infer_type Γ t
  let (τ', sT) := Term.to_telescope B
  let ξ <- prefix_equal τ τ'
  let sT' := Term.from_telescope ξ sT
  let T := [P' τ.length]sT'
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  if R == R' then .some T else .none
| Γ, `λ[A] t => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  let B <- infer_type (.type A::Γ) t
  .some (A -t> B)
| Γ, .ctor2 .app f a => do
  let T <- infer_type Γ f
  let (A, B) <- is_arrow T
  let A' <- infer_type Γ a
  if A == A' then .some (B β[.kind]) else .none
| Γ, Λ[A] t => do
  let _ <- wf_kind A
  let B <- infer_type (.kind A::Γ) t
  .some (∀[A] B)
| Γ, .ctor2 .appt f a => do
  let T <- infer_type Γ f
  let (A, B) <- is_all T
  let A' <- infer_kind Γ a
  if A == A' then .some (B β[a]) else .none
| Γ, .ctor2 .cast t c => do
  let A <- infer_type Γ t
  let T <- infer_type Γ c
  let (A', B) <- is_eq T
  if A == A' then .some B else .none
| Γ, .ctor1 .refl A => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  .some A
| Γ, .ctor1 .sym t => do
  let T <- infer_type Γ t
  let (A, B) <- is_eq T
  .some (B ~ A)
| Γ, .ctor2 .seq t1 t2 => do
  let T1 <- infer_type Γ t1
  let T2 <- infer_type Γ t2
  let (A, B) <- is_eq T1
  let (B', C) <- is_eq T2
  if B == B' then .some (A ~ C) else .none
| Γ, .ctor2 .appc f a => do
  let T1 <- infer_type Γ f
  let T2 <- infer_type Γ a
  let (A, B) <- is_eq T1
  let (C, D) <- is_eq T2
  .some ((A `@k C) ~ (B `@k D))
| Γ, .ctor2 .arrowc t1 t2 => do
  let T1 <- infer_type Γ t1
  let T2 <- infer_type Γ t2
  let (A, B) <- is_eq T1
  let (C, D) <- is_eq T2
  .some ((A -t> C) ~ (B -t> D))
| Γ, .ctor1 .fst t => do
  let T <- infer_type Γ t
  let (U, V) <- is_eq T
  let (A, _) <- is_appk U
  let (B, _) <- is_appk V
  .some (A ~ B)
| Γ, .ctor1 .snd t => do
  let T <- infer_type Γ t
  let (U, V) <- is_eq T
  let (_, C) <- is_appk U
  let (_, D) <- is_appk V
  .some (C ~ D)
| Γ, ∀c[K] t => do
  let T <- infer_type (.kind K :: Γ) t
  let (A, B) <- is_eq T
  .some ((∀[K] A) ~ (∀[K] B))
| Γ, f `@c[a] => do
  let T1 <- infer_type Γ f
  let T2 <- infer_type Γ a
  let (U, V) <- is_eq T1
  let (K1, A) <- is_all U
  let (K2, B) <- is_all V
  let (C, D) <- is_eq T2
  if K1 == K2 then .some ((A β[C]) ~ (B β[D])) else .none
| _, _ => .none

@[simp]
def wf_ctx : Ctx Term -> Option Unit
| [] => .some .unit
| .cons (.type A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  wf_ctx Γ
| .cons (.kind A) Γ => do
  let _ <- wf_kind A
  wf_ctx Γ
| .cons (.datatype A) Γ => do
  let _ <- wf_kind A
  wf_ctx Γ
| .cons (.ctor A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_pointed Ak
  if valid_ctor Γ then wf_ctx Γ else .none
| .cons (.opent A) Γ => do
  let _ <- wf_kind A
  wf_ctx Γ
| .cons (.openm A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  wf_ctx Γ
| .cons (.insttype A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  wf_ctx Γ
| .cons (.term A t) Γ => do
  let A' <- infer_type Γ t
  let _ <- wf_ctx Γ
  if A == A' then .some () else .none
| .cons (.inst x t) Γ =>
  match Γ d@ x with
  | .openm T => do
    let T' <- infer_type Γ t
    if T == T' then .some () else .none
  | _ => .none
| _ => .none
