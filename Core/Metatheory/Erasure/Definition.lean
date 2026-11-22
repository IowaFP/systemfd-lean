import Core.Global
import Core.Term
import Core.Typing
import Core.Metatheory.Global
import Core.Reduction
import Core.Untyped

open Lilac
open LeanSubst
open List

namespace Core

@[simp]
def Pattern.erase (pm : Pattern m) : Untyped.Pattern m :=
  pm.map (fun ⟨s, _, _, i, j⟩ => (s, i, j))

/--
Erases both types and coercions.
-/
@[simp]
def Term.erase : Term → Untyped.Term
  | #x => #x
  -- Just like a variable
  | d#x => d#x
  | spctor _ x _ _ ts => .spctor x (Term.erase <$> ts)
  | ctor0 (.refl _) => .unit
  | ctor1 (.appt _) b => .app b.erase .unit
  | ctor1 (.prj _) t => t.erase
  | ctor2 .app t1 t2 => .app t1.erase t2.erase
  | ctor2 .apptc _ _ => .unit
  | lam _ t => .lam t.erase
  | tbind .allc _ t => t.erase
  | tbind .lamt _ t => .lam t.erase
  | cast _ _ t => t.erase
  | mtch m n vm pmn vn => 
    .mtch m n (erase <$> vm) (Pattern.erase <$> pmn) (erase <$> vn)


-- TODO: define erase on Subst Term
-- beta rule for subs

@[simp]
def Constructor.erase (c : Constructor) : Untyped.Constructor :=
  let ⟨s, _, _, _, _, n, vm⟩ := c
  ⟨s, n, vm.map Term.erase⟩

@[simp]
def Global.erase : Global → Untyped.Global
| defn s _ t => .defn s t.erase
| inst s pm t => .inst s pm.erase t.erase
-- To simplify indexing,
-- use a dummy variant
| _ => .erased

@[simp]
def GlobalEnv.erase (G : GlobalEnv) := Global.erase <$> G

-- TODO: do we need to know
-- what de Brujin indices
-- we use for the untyped version?
-- (So have a lookup for
-- those indicies corresponding
-- to types)?
@[simp]
def Action.erase : Action Term → Action Untyped.Term
| re n => re n
| su t => su t.erase

@[simp]
def Ren.erase (τ : Ren Term) : Ren Untyped.Term :=
  {act := τ.act}

@[simp]
def Subst.erase (σ : Subst Term) : Subst Untyped.Term :=
  {inner := λ n => Action.erase (σ.inner n)}

notation "⟦" e "⟧" => Term.erase e
notation "⟦" g "⟧" => Global.erase g
notation "⟦" G "⟧" => GlobalEnv.erase G
notation "⟦" pm "⟧" => Pattern.erase pm
notation "⟦" vm "⟧" => Term.erase <$> vm
notation "⟦" pmn "⟧" => Pattern.erase <$> pmn
notation "⟦" a "⟧" => Action.erase a
notation "⟦" τ "⟧" => Ren.erase τ
notation "⟦" σ "⟧" => Subst.erase σ
