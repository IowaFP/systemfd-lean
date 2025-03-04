import SystemFD.Util
import SystemFD.Term
import SystemFD.Ctx
set_option maxHeartbeats 500000

@[simp]
def wf_kind : Term -> Option Unit
| .type => .some ()  -- ★
| .ctor2 .arrowk A B => do -- κ → κ'
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

def is_type : Term -> Option Unit
| .type => .some ()
| _ => .none

theorem is_type_some : is_type t = .some () -> t = ★ := by
intro h
unfold is_type at h; cases t <;> try simp at *

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
  let _ <- is_type Bk
  .some ★
| Γ, .bind2 .arrow A B => do
  let Ak <- infer_kind Γ A
  let _ <- is_type Ak
  let Bk <- infer_kind (.empty::Γ) B
  let _ <- is_type Bk
  .some ★
| Γ, .ctor2 .appk f a => do
  let fk <- infer_kind Γ f
  let (A, B) <- is_arrowk fk
  let ak <- infer_kind Γ a
  if A == ak then .some B else .none
| Γ, .ctor2 .eq A B => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  let Bk <- infer_kind Γ B
  let _ <- wf_kind Bk
  if Ak == Bk then .some ★ else .none
| _, _ => .none

-- A is of the form
-- ∀[★]∀[★].. x -t> y -t> T p q r
-- we need to check that T is a datatype in Γ
def valid_ctor : (Γ : Ctx Term) -> (A : Term) -> Option Unit
  | Γ, .bind2 .arrow A B => valid_ctor (.type A :: Γ) B -- arrow case
  | Γ, .bind2 .all A B => valid_ctor (.kind A :: Γ)  B  -- all case
  | Γ, A => do let (x, _) <- A.neutral_form -- refl case
               if (Γ.is_datatype x) then .some () else .none

-- A is of the form
-- ∀[★]∀[★].. x -t> y -t> T p q r
-- we need to check that T is an inst type in Γ
def valid_insttype : (Γ : Ctx Term) -> (A : Term) -> Option Unit
  | Γ, .bind2 .arrow A B => valid_insttype (.type A :: Γ) B -- arrow case
  | Γ, .bind2 .all A B => valid_insttype (.kind A :: Γ)  B  -- all case
  | Γ, A => do let (x, _) <- A.neutral_form -- refl case
               if (Γ.is_opent x) then .some () else .none

def stable_type_match (Γ : Ctx Term) (A R : Term) : Option Unit := do
  let (τ, sR) := Term.to_telescope A
  let (x, _) <- Term.neutral_form R
  if [S' τ.length]R == sR
    && (Γ d@ x).is_stable
  then .some ()
  else .none

def prefix_type_match (Γ : Ctx Term) (A B : Term) : Option Term := do
  let (τ, R) := Term.to_telescope A
  let (τ', sT) := Term.to_telescope B
  let ξ <- prefix_equal τ τ'
  let T := [P' τ.length](Term.from_telescope ξ sT)
  let (x, _) <- Term.neutral_form R
  let x' := x - τ.length
  if [S' τ.length]T == Term.from_telescope ξ sT
    && x = x' + τ.length
    && (Γ d@ x').is_stable
  then .some T
  else .none

@[simp]
def infer_type : Ctx Term -> Term -> Option Term
| Γ, #x => do
  let T <- Frame.get_type (Γ d@ x)
  .some T
| Γ, .ite p s i e => do
  let A <- infer_type Γ p
  let R <- infer_type Γ s
  let Rk <- infer_kind Γ R
  let _ <- wf_kind Rk
  let B <- infer_type Γ i
  let _ <- stable_type_match Γ A R
  let (ph, _) <- Term.neutral_form p
  let (rh, _) <- Term.neutral_form R
  let ctor_headed := Γ.is_ctor ph
  let dt_headed := Γ.is_datatype rh
  let T <- prefix_type_match Γ A B
  let Tk <- infer_kind Γ T
  let _ <- wf_kind Tk
  let T' <- infer_type Γ e
  if T == T' && ctor_headed && dt_headed
  then .some T
  else .none
| Γ, .guard p s t => do
  let A <- infer_type Γ p
  let R <- infer_type Γ s
  let Rk <- infer_kind Γ R
  let _ <- wf_kind Rk
  let _ <- stable_type_match Γ A R
  let (ph, _) <- Term.neutral_form p
  let (rh, _) <- Term.neutral_form R
  let insttype_headed := Γ.is_insttype ph
  let ot_headed := Γ.is_opent rh
  let B <- infer_type Γ t
  let T <- prefix_type_match Γ A B
  let Tk <- infer_kind Γ T
  let _ <- wf_kind Tk
  if (insttype_headed && ot_headed)
    then .some T
    else .none
| Γ, `λ[A] t => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  let B <- infer_type (.type A::Γ) t
  .some (A -t> B)
| Γ, .ctor2 .app f a => do
  let T <- infer_type Γ f
  let (A, B) <- is_arrow T
  let A' <- infer_type Γ a
  if A == A' then .some (B β[a]) else .none
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
  let Ak <- infer_kind Γ A
  let Bk <- infer_kind Γ B
  let Ck <- infer_kind Γ C
  let Dk <- infer_kind Γ D
  let (K1, K2) <- is_arrowk Ak
  let (K3, K4) <- is_arrowk Bk
  if ((K1 == K3) && (K2 == K4) && (Ck == K1) && (Dk == K3))
  then .some ((A `@k C) ~ (B `@k D))
  else .none
| Γ, .bind2 .arrowc t1 t2 => do
  let T1 <- infer_type Γ t1
  let T2 <- infer_type (.empty :: Γ) t2
  let (A, B) <- is_eq T1
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  let Bk <- infer_kind Γ B
  let _ <- wf_kind Bk
  let (C, D) <- is_eq T2
  let Ck <- infer_kind (.empty :: Γ) C
  let _ <- wf_kind Ck
  let Dk <- infer_kind (.empty :: Γ) D
  let _ <- wf_kind Dk
  .some ((A -t> C) ~ (B -t> D))
| Γ, .ctor1 .fst t => do
  let T <- infer_type Γ t
  let (U, V) <- is_eq T
  let (A, _) <- is_appk U
  let Ak <- infer_kind Γ A
  let (K1, K2) <- is_arrowk Ak
  let (B, _) <- is_appk V
  let Bk <- infer_kind Γ B
  let (K3, K4) <- is_arrowk Bk
  if K1 == K3 && K2 == K4
  then .some (A ~ B)
  else .none
| Γ, .letterm A t b => do
  let Ak <- infer_kind Γ A
  let _ <- is_type Ak
  let A' <- infer_type Γ t
  let sT <- infer_type (.term A t :: Γ) b
  let T := [P]sT
  let Tk <- infer_kind Γ T
  let _ <- is_type Tk
  if A == A' then .some T else .none
| Γ, .ctor1 .snd t => do
  let T <- infer_type Γ t
  let (U, V) <- is_eq T
  let (_, C) <- is_appk U
  let Ck <- infer_kind Γ C
  let _ <- wf_kind Ck
  let (_, D) <- is_appk V
  let Dk <- infer_kind Γ D
  if Ck == Dk then .some (C ~ D) else .none
| Γ, ∀c[K] t => do
  let T <- infer_type (.kind K :: Γ) t
  let (A, B) <- is_eq T
  let Ak <- infer_kind Γ (∀[K] A)
  let _ <- wf_kind Ak
  let Bk <- infer_kind Γ (∀[K] B)
  let _ <- wf_kind Bk
  .some ((∀[K] A) ~ (∀[K] B))
| Γ, f `@c[a] => do
  let T1 <- infer_type Γ f
  let T2 <- infer_type Γ a
  let (U, V) <- is_eq T1
  let (K1, A) <- is_all U
  let (K2, B) <- is_all V
  let (C, D) <- is_eq T2
  let Ck <- infer_kind Γ C
  let Dk <- infer_kind Γ D
  if K1 == K2 && Ck == Dk && K1 == Ck
  then .some ((A β[C]) ~ (B β[D]))
  else .none
| _, _ => .none

@[simp]
def wf_ctx : Ctx Term -> Option Unit
| [] => .some .unit
| .cons .empty Γ => wf_ctx Γ
| .cons (.type A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  wf_ctx Γ
| .cons (.kind A) Γ => do
  let _ <- wf_kind A
  wf_ctx Γ
| .cons (.datatype A) Γ => do
  let _ <- wf_kind A
  wf_ctx Γ
| .cons (.ctor A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  let _ <- valid_ctor Γ A
  wf_ctx Γ
| .cons (.opent A) Γ => do
  let _ <- wf_kind A
  wf_ctx Γ
| .cons (.openm A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  wf_ctx Γ
| .cons (.insttype A) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  let _ <- valid_insttype Γ A
  wf_ctx Γ
| .cons (.term A t) Γ => do
  let Ak <- infer_kind Γ A
  let _ <- wf_kind Ak
  let A' <- infer_type Γ t
  let _ <- wf_ctx Γ
  if A == A' then .some () else .none
| .cons (.inst #x t) Γ =>
  match Γ d@ x with
  | .openm T => do
    let T' <- infer_type Γ t
    let _ <- wf_ctx Γ
    if T == T' then .some () else .none
  | _ => .none
| .cons (.inst _ _) _ => .none
