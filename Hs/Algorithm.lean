import Hs.HsTerm
import Hs.HsCtx
import SystemFD.Term
import SystemFD.Algorithm
import Hs.SynthInstance

set_option profiler true

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

-- surface: datatype Bool (tt, ff); #0 = ff, #1 = tt, #2 = Bool <-- defined by hs_nth
abbrev DsM a := Except Std.Format a

namespace DsM

def ok : a -> DsM a := λ x => Except.ok x
def error : Std.Format -> DsM a := λ x => Except.error x
def bind : DsM a -> (a -> DsM b) -> DsM b := Except.bind

def toDsM (pfix : Std.Format) : Option a -> DsM a
| .some a => ok a
| .none => error (pfix ++ Std.Format.line)

def toDsMq : Option a -> DsM a := toDsM ""

def run [Repr a] : DsM a -> Std.Format
| .error e => "Error:" ++ Std.Format.line ++ e
| .ok t => repr t

end DsM


def helper1
  (compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term)
  (Γ : Ctx Term)
  (head : HsTerm)
  : DsM (Term × Term)
:=
  match head with
  | .HsAnnotate τh h => do
    let τh' <-compile Γ ★ τh
  -- τh' is of the form ∀ αs, C a ⇒ τ -> τ''
    let h' <- compile Γ τh' h
    DsM.ok (h', τh')
  | .HsVar h => do
    let τh' <- DsM.toDsM ("helper1 head" ++ repr head) (Γ d@ h).get_type
    -- τ' is of the shape ∀ αs, C a ⇒ τ -> τ''
    .ok (#h, τh')
  | t => DsM.error ("helper1 unsupported head" ++ repr t)

def helper2
  (compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term)
  (Γ : Ctx Term)
  : Term × Term -> HsSpineVariant × HsTerm -> DsM (Term × Term)
:= λ acc arg => do
  let (accτ, acc) : Term × Term := acc
  let (τ, res_τ) <- .toDsM ("helper2 " ++ repr accτ) accτ.to_telescope_head
  match τ, arg with
  | .kind k, (.type, arg) => do -- accτ better of of the form ∀[a] b
    let arg' <- compile Γ k arg
    .ok (res_τ β[arg'], acc `@t arg')
  | .type k, (.term, arg) => do -- accτ better of of the form a -> b
    let arg' <- compile Γ k arg
    .ok (res_τ β[arg'], acc `@ arg')
  | _, _ => .error ("heper2" ++ repr τ ++ repr arg)

-- @[simp]
unsafe def compile : (Γ : Ctx Term) -> (τ : Term) -> (t : HsTerm) -> DsM Term
-- TODO: Type directed compilation
-- def compile : (Γ : Ctx Term) -> Term -> HsTerm -> Option Term
-------------------
--- Kind
-------------------
| _ , □, `★ => .ok ★

| Γ, □ , .HsCtor2 .arrowk t1 t2 => do
  let t1' <- compile Γ □ t1
  let t2' <- compile Γ □ t2
  .ok (.ctor2 .arrowk t1' t2')

| Γ, κ, .HsCtor2 .appk f a => do
  let (h, sp) <- .toDsMq (HsTerm.split_kind_app (.HsCtor2 .appk f a))
  let τ <- .toDsM ("GetType" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr h) ((Γ d@ h).get_type)
  let (κs, κ') <- .toDsMq (Term.split_kind_arrow τ)
  let args' <- List.mapM
    (λ a => compile Γ a.1 a.2)
    (List.zip κs sp)
  .ok (Term.mk_kind_app h args')


| Γ, ★ , .HsBind2 .arrow A B => do
  let A' <- compile Γ ★ A
  let B' <- compile (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .farrow A B => do
  let A' <- compile Γ ★ A
  let B' <- compile (.empty :: Γ) ★ B
  .ok (.bind2 .arrow A' B')

| Γ, ★ , .HsBind2 .all A B => do
  let A' <- compile Γ □ A
  let B' <- compile (.kind A' :: Γ) ★ B
  .ok (.bind2 .all A' B')

-- | Γ, κ , .HsCtor2 .appk A (.HsAnnotate k B) => do
--   let k' <- compile Γ □ k
--   let A' <- compile Γ (k' -k> κ) A
--   let B' <- compile Γ k' B
--   .ok (.ctor2 .appk A' B')

| Γ, τ, .HsHole a => do
  let a' <- compile Γ ★ a
  let t <- .toDsM ("synth_term hole" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr a')
           (synth_term Γ a')
  if τ == a'
  then .ok t
  else do
    let η <- .toDsM ("synth_coercion hole" ++  Std.Format.line ++ repr Γ ++ repr (a' ~[★]~ τ))
             (synth_coercion Γ a' τ)
    .ok (t ▹ η )


| Γ, .bind2 .arrow A B, .HsBind2 .lam A' t => do
  let α' <- compile  Γ ★ A'
  if A == α'
  then do
    let t' <- compile (.type A :: Γ) B t
    .ok (.bind2 .lam A t')
  else .error ("compile lam" ++ (repr (A -t> B)) ++ (repr (λ̈[A'] t)))

| Γ, .bind2 .all A B, .HsBind2 .lamt A' t => do
  let α' <- compile Γ □ A'
  if A == α'
  then do
    let t' <- compile (.kind A :: Γ) B t
    .ok (.bind2 .lamt A t')
  else .error ("compile lamt" ++ (repr (∀[A] B)) ++ (repr (Λ̈[A'] t)))

-- guard blah in
-- guard blah in \ . \ .
--   ... : u ~ v


| Γ, τ, .HsLet A t1 t2 => do
  let α <- compile Γ ★ A
  let t1' <- compile Γ α t1
  let t2' <- compile (.term α t1' :: Γ) τ t2 -- Deal with dB BS
  .ok (.letterm α t1' t2')

| Γ, τ, .HsIte (.HsAnnotate pτ p) (.HsAnnotate sτ s) (.HsAnnotate iτ i) t => do
  let pτ' <- compile Γ ★ pτ
  let p' <- compile Γ pτ' p
  let sτ' <- compile Γ ★ sτ
  let s' <- compile Γ sτ' s
  let iτ' <- compile Γ ★ iτ
  let i' <- compile Γ iτ' i
  let t' <- compile Γ τ t
  .ok (.ite p' s' i' t')

| Γ, exp_τ, `#h => do
  let τ <- .toDsM ("get_type" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr h)
           ((Γ d@ h).get_type)
  if τ == exp_τ
  then .ok #h
  else do
    let η <- .toDsM ("synth_coercion variable" ++ Std.Format.line ++ repr Γ
                    ++ Std.Format.line ++ repr (τ ~[★]~ exp_τ)
                    ++ Std.Format.line ++ repr h) (synth_coercion Γ τ exp_τ)
    .ok (#h ▹ η)

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

| Γ, exp_τ, t => do
  let (head, args) <- .toDsM ("no neutral form" ++ repr t) t.neutral_form
  -- Compile Head
  let (h', τh') <- helper1 compile Γ head
  let (τs, res_τh') := τh'.to_telescope

  if args.length > τs.length
  then .error ("compile length mismatch"
                ++ Std.Format.line ++ (repr exp_τ)
                ++ Std.Format.line ++ (repr t))
  else
  -- Compile Args and actual type
    let (actual_τ, t') <- args.foldlM (helper2 compile Γ) (τh', h')
    if exp_τ == actual_τ
    then .ok t'
    else do
      let η <- .toDsM ("synth_coercion spine" ++ repr Γ ++ Std.Format.line ++ repr (actual_τ ~[★]~ exp_τ))
                      (synth_coercion Γ actual_τ exp_τ)
      .ok (t' ▹ η)

-- | _, _, _ => .none
-- decreasing_by repeat sorry
-- all_goals(simp at *)
-- case _ => sorry


namespace Test
  def Γ : Ctx Term := [
    .openm (∀[★](#5 `@k #0) -t> #1 -t> #2 -t> #9),
    .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
    .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
    .opent (★ -k> ★),
    .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
    .opent (★ -k> ★),
    .datatype ★ ]

    #guard wf_ctx Γ == .some ()

    #eval (Γ d@ 0)
    #eval! DsM.run (compile Γ (∀[★](#6 `@k #0) -t> #1 -t> #2 -t> #10) `#0)
    #eval! DsM.run (compile Γ ((#5 `@k #6) -t> #7 -t> #8 -t> #9) (`#0 `•t `#6))
    #eval! DsM.run (compile Γ (#5 `@k #6) (.HsHole (`#5 `•k `#6)))
    #eval! DsM.run (compile Γ (#6 -t> #7 -t> #8) (`#0 `•t `#6 `• (.HsHole (`#5 `•k `#6))))
end Test
