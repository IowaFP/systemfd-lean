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

def is_openm : Frame Term -> Option Term
| .openm T => .some T
| _ => .none

theorem is_openm_some : is_openm t = .some k -> t = .openm k := by
intro h
unfold is_openm at h; cases t <;> simp at h
rw [h]

def is_const : Term -> Option Const
| .const K => .some K
| _ => .none

theorem is_const_some : is_const t = .some k -> t = .const k := by
intro h
unfold is_const at h; cases t <;> simp at h
rw [h]

def is_pointed : Term -> Option Unit
| .const .pointed => .some ()
| _ => .none

theorem is_pointed_some : is_pointed t = .some () -> t = ★ := by
intro h
unfold is_pointed at h; cases t <;> try simp at h
case _ k => cases k <;> simp at *

def is_unpointed : Term -> Option Unit
| .const .unpointed => .some ()
| _ => .none

theorem is_unpointed_some : is_unpointed t = .some () -> t = ◯ := by
intro h
unfold is_unpointed at h; cases t <;> try simp at h
case _ k => cases k <;> simp at *

def is_arrowk : Term -> Option (Term × Term)
| .ctor2 .arrowk A B => .some (A, B)
| _ => .none

theorem is_arrowk_some : is_arrowk t = .some (A, B) -> t = (A -k> B) := by
intro h
unfold is_arrowk at h; cases t <;> try simp at h
case _ v A B =>
  cases v <;> simp at h
  rw [h.1, h.2]

def is_arrow : Term -> Option (Term × Term)
| .bind2 .arrow A B => .some (A, B)
| _ => .none

theorem is_arrow_some : is_arrow t = .some (A, B) -> t = (A -t> B) := by
intro h
unfold is_arrow at h; cases t <;> try simp at h
case _ v A B =>
  cases v <;> simp at h
  rw [h.1, h.2]

def is_eq : Term -> Option (Term × Term)
| .ctor2 .eq A B => .some (A, B)
| _ => .none

theorem is_eq_some : is_eq t = .some (A, B) -> t = (A ~ B) := by
intro h
unfold is_eq at h; cases t <;> try simp at h
case _ v A B =>
  cases v <;> simp at h
  rw [h.1, h.2]

def is_appk : Term -> Option (Term × Term)
| .ctor2 .appk A B => .some (A, B)
| _ => .none

theorem is_appk_some : is_appk t = .some (A, B) -> t = (A `@k B) := by
intro h
unfold is_appk at h; cases t <;> try simp at h
case _ v A B =>
  cases v <;> simp at h
  rw [h.1, h.2]

def is_all : Term -> Option (Term × Term)
| .bind2 .all A B => .some (A, B)
| _ => .none

theorem is_all_some : is_all t = .some (A, B) -> t = (∀[A] B) := by
intro h
unfold is_all at h; cases t <;> try simp at h
case _ v A B =>
  cases v <;> simp at h
  rw [h.1, h.2]

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
  let _ <- is_pointed Ak
  let Bk <- infer_kind Γ B
  let _ <- is_pointed Bk
  .some ◯
| _, _ => .none

@[simp]
def infer_type : Ctx Term -> Term -> Option Term
| Γ, .letdata T t => do
  let _ <- wf_kind T
  let A <- infer_type (.datatype T::Γ) t
  .some (.decl A)
| Γ, .bind2 .letctor T t => do
  let Tk <- infer_kind Γ T
  let _ <- is_pointed Tk
  let A <- infer_type (.ctor T::Γ) t
  if valid_ctor Γ then .some (.decl A) else .none
| Γ, .bind2 .letopentype T t => do
  let _ <- wf_kind T
  let A <- infer_type (.opent T::Γ) t
  .some (.decl A)
| Γ, .bind2 .letopen T t => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let A <- infer_type (.openm T::Γ) t
  .some (.decl A)
| Γ, .bind2 .insttype T t => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let A <- infer_type (.insttype T::Γ) t
  .some (.decl A)
| Γ, .inst x t1 t2 => do
  let T <- is_openm (Γ d@ x)
  let T' <- infer_type Γ t1
  let A <- infer_type (.inst x t1::Γ) t2
  if T == T' then .some (.decl A) else .none
| Γ, .letterm T b t => do
  let Tk <- infer_kind Γ T
  let _ <- is_const Tk
  let B <- infer_type Γ b
  let A <- infer_type (.term T b::Γ) t
  if T == B then .some (.decl A) else .none
| Γ, #x => do
  let T <- Frame.get_type (Γ d@ x)
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
    && [S' τ.length]R == sR
    && [S' τ.length]T == sT'
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
  if R == R'
    && [S' τ.length]R == sR
    && [S' τ.length]T == sT'
  then .some T
  else .none
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
  let _ <- is_pointed Ak
  .some (A ~ A)
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
| Γ, .bind2 .arrowc t1 t2 => do
  let T1 <- infer_type Γ t1
  let T2 <- infer_type (.empty :: Γ) t2
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
  let _ <- wf_kind K
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
| .cons .empty Γ => wf_ctx Γ
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
  let Ak <- infer_kind Γ A
  let _ <- is_const Ak
  let A' <- infer_type Γ t
  let _ <- wf_ctx Γ
  if A == A' then .some () else .none
| .cons (.inst x t) Γ =>
  match Γ d@ x with
  | .openm T => do
    let T' <- infer_type Γ t
    let _ <- wf_ctx Γ
    if T == T' then .some () else .none
  | _ => .none
