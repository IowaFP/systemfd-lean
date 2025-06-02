import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Term
import SystemFD.Algorithm

@[simp]
def compile_ctor2variant : HsCtor2Variant -> Ctor2Variant
| .arrowk => .arrowk
| .appk => .appk
| .appt => .appt
| .app => .app

@[simp]
def compile_bind2variant : HsBind2Variant -> Bind2Variant
| .all => .all
| .arrow => .arrow
| .farrow => .arrow
| .lam => .lam
| .lamt => .lamt

-- TODO: move bind2_frame and hs_bind2_frame in a common place
@[simp]
def hs_bind2_frame : Term -> HsBind2Variant -> Frame Term
| t, .all => .kind t
| t, .lam => .type t
| t, .lamt => .kind t
| _ , _ =>  .empty


@[simp]
def compile_spine_variant : HsSpineVariant -> SpineVariant
| .term => .term
| .type => .type
| .kind => .kind


def synth_term : Ctx Term -> Term -> Option Term := λ _ _ => .some `0
def synth_coercion : Ctx Term -> Term -> Term -> Option Term := λ _ _ _ => .some `0

-- surface: datatype Bool (tt, ff); #0 = ff, #1 = tt, #2 = Bool <-- defined by hs_nth

-- @[simp]
def compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> Option Term
-- TODO: Type directed compilation
-- def compile : (Γ : Ctx Term) -> Term -> HsTerm -> Option Term
-------------------
--- Kind
-------------------
| _ , □, `★ => .some ★

| Γ, □ , .HsCtor2 .arrowk t1 t2 => do
  let t1' <- compile Γ □ t1
  let t2' <- compile Γ □ t2
  .some (.ctor2 .arrowk t1' t2')

| Γ, ★ , .HsBind2 .arrow A B => do
  let A' <- compile Γ □ A
  let B' <- compile (.empty :: Γ) □ B
  .some (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .farrow A B => do
  let A' <- compile Γ □ A
  let B' <- compile (.empty :: Γ) □ B
  .some (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .all A B => do
  let A' <- compile Γ □ A
  let B' <- compile (.kind A' :: Γ) ★ B
  .some (.bind2 .all A' B')

-- | Γ, κ , .HsCtor2 .appk A (.HsAnnotate k B) => do
--   let k' <- compile Γ □ k
--   let A' <- compile Γ (k' -k> κ) A
--   let B' <- compile Γ k' B
--   .some (.ctor2 .appk A' B')

| Γ, τ, .HsHole a => do
  let a' <- compile Γ ★ a
  let t <- synth_term Γ a'
  if τ == a'
  then .some t
  else do
    let η <- synth_coercion Γ a' τ
    .some (t ▹ η )


| Γ, .bind2 .arrow A B, .HsBind2 .lam A' t => do
  let α' <- compile  Γ ★ A'
  if A == α'
  then do
    let t' <- compile (.type A :: Γ) B t
    .some (.bind2 .lam A t')
  else .none

| Γ, .bind2 .all A B, .HsBind2 .lamt A' t => do
  let α' <- compile Γ ★ A'
  if A == α'
  then do
    let t' <- compile (.kind A :: Γ) B t
    .some (.bind2 .lamt A t')
  else .none

-- guard blah in
-- guard blah in \ . \ .
--   ... : u ~ v


| Γ, τ, .HsLet A t1 t2 => do
  let α <- compile Γ ★ A
  let t1' <- compile Γ α t1
  let t2' <- compile (.term α t1' :: Γ) τ t2 -- Deal with dB BS
  .some (.letterm α t1' t2')

| Γ, τ, .HsIte (.HsAnnotate pτ p) (.HsAnnotate sτ s) (.HsAnnotate iτ i) t => do
  let pτ' <- compile Γ ★ pτ
  let p' <- compile Γ pτ' p
  let sτ' <- compile Γ ★ sτ
  let s' <- compile Γ sτ' s
  let iτ' <- compile Γ ★ iτ
  let i' <- compile Γ iτ' i
  let t' <- compile Γ τ t
  .some (.ite p' s' i' t')

--
-- f : Eq a => B -> A
-- b : B

-- f (annotate B b)
-- goal type is A

-- (annoate T f) a1 a2 a3

-- (annotate eta (Eq a => B -> C)) ? a1 a2

-- (==) : Eq a => a -> a -> Bool
-- eta : Eq a => a -> a -> Bool
-- eta = \ a. \ b. a == b

-- | Γ, τ, .HsCtor2 .app f (.HsAnnotate τa a) => do
--   let f' <- compile Γ (τa → τ) f
--   let a' <- compile Γ τa a
--   .some (.ctor2 .app f' a')


-- | Γ, τ, .HsCtor2 .appt f (.HsAnnotate τa a) => do
--   let f' <- compile Γ (τa → τ) f
--   let a' <- compile Γ τa a
--   .some (.ctor2 .app f' a')

| Γ, τ, t => do
  let (head, args) <- t.neutral_form
  match head with
  | .HsAnnotate τ' h => do
    let τ' <- compile Γ ★ τ'
    -- τ' is of the form ∀ αs, C a ⇒ τ -> τ''
    let (τs, τ'') := τ'.to_telescope
    let h' <- compile Γ τ' h

      -- τs.length ≥ args.length
      -- actually τs.length = typeargs + args
    let τs' <- List.mapM (Frame.get_type ·) τs


    let args' <- List.mapM -- (HsSpineVariant × HsTerm) HsTerm
        (λ a =>
           match a with
           | (.kind k, (.type, argτ)) => do
             let argτ' <- compile Γ k argτ
             .some (.type, argτ')
           | (.type τ, (.term, arg)) => do
             let arg' <- compile Γ τ arg
             .some (.term, arg')
           | _ => .none)
        (List.zip τs args)

    .some (h'.apply_spine args')
  | .HsVar h => do
    let τ' <- (Γ d@ h).get_type
    let (τs, τ'') := τ'.to_telescope
    -- let h' <- compile Γ τ' h

      -- τs.length ≥ args.length
      -- actually τs.length = typeargs + args
    let τs' <- List.mapM (Frame.get_type ·) τs


    let args' <- List.mapM -- (HsSpineVariant × HsTerm) HsTerm
        (λ a =>
           match a with
           | (.kind k, (.type, argτ)) => do
             let argτ' <- compile Γ k argτ
             .some (.type, argτ')
           | (.type τ, (.term, arg)) => do
             let arg' <- compile Γ τ arg
             .some (.term, arg')
           | _ => .none)
        (List.zip τs args)

    .some ((#h).apply_spine args')


  | _ => .none
decreasing_by repeat sorry
