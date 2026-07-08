import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Eval.SmallStep
import Core.Infer.Type
import Core.Infer.Global

import Core.Examples.Common
import Core.Examples.Boolean

open Lilac
open LeanSubst

namespace Core.Examples

def LeftPat : String × (n : Nat) × Vec Ty n × Nat × Nat := ⟨"Left", 2, #(t#1, t#0), 0, 1⟩
def RightPat : String × (n : Nat) × Vec Ty n × Nat × Nat := ⟨"Right", 2, #(t#1, t#0), 0, 1⟩

def LTPat : String × (n : Nat) × Vec Ty n × Nat × Nat := ⟨"LT", 0, #(), 0, 0⟩
def EQPat : String × (n : Nat) × Vec Ty n × Nat × Nat := ⟨"EQ", 0, #(), 0, 0⟩
def GTPat : String × (n : Nat) × Vec Ty n × Nat × Nat := ⟨"GT", 0, #(), 0, 0⟩

def LTCtor : Term := ctor! "LT" #() #() .nil
def EQCtor : Term := ctor! "EQ" #() #() .nil
def GTCtor : Term := ctor! "GT" #() #() .nil

def OrdCtx : GlobalEnv := [

  .inst "eq" #(⟨"EqOfOrd", 1, #(t#0), 0, 1⟩) (λ[t#0]λ[t#0]
         mtch' #((openm! "compare" #(t#0) #() #(#2).to).mkApps [] [#1, #0])
           #( (#(LTPat), FalseCtor)
            , (#(EQPat), TrueCtor)
            , (#(GTPat), FalseCtor)
            )
  ),

  .octor "EqOfOrd" ⟨1, #(★), 0, #(), 1, #(gt#"Ord" • t#0), gt#"Eq" • t#0⟩,

  .inst "compare" #(⟨"OrdEither", 1, #(t#0), 2, 3⟩) (
        let t1 := (d#"arrowc").mkApps [t#2, (gt#"Either" • t#1) • t#0, gt#"Ordering", gt#"Ordering"] [#0, refl! gt#"Ordering"]
        let t2 := ((d#"arrowc").mkApps [t#2, (gt#"Either" • t#1) • t#0, t#2 -:> gt#"Ordering", ((gt#"Either" • t#1) • t#0) -:> gt#"Ordering"]) [#0, t1]
        let t3 := ((d#"sym" •[t#2 -:> (t#2 -:> gt#"Ordering")]) •[((gt#"Either" • t#1) • t#0) -:> (((gt#"Either" • t#1) • t#0) -:> gt#"Ordering")]) • t2
        Term.cast t#0 t3 ((d#"compEither").mkApps [t#1, t#0] [#2, #1])
  ),

  -- OrdEither : ∀ t u v. Ord u, Ord v, t ~ Either u v ⇒ Ord t
  .octor "OrdEither" ⟨1, #(★), 2, #(★, ★), 3, #(gt#"Ord" • t#1, gt#"Ord" • t#0, t#2 ~[★]~ ((gt#"Either" • t#1) • t#0)), (gt#"Ord" • t#2)⟩,

  .defn "compEither" (∀[★]∀[★] (gt#"Ord" • t#1) -:> ((gt#"Ord" • t#0) -:> (((gt#"Either" • t#1) • t#0) -:> (((gt#"Either" • t#1) • t#0) -:> gt#"Ordering"))))
    (Λ[★]Λ[★]λ[gt#"Ord" • t#1]λ[gt#"Ord" • t#0]λ[((gt#"Either" • t#1) • t#0)]λ[((gt#"Either" • t#1) • t#0)]
      mtch' #(#1, #0)
        #( (#(LeftPat, LeftPat), ((openm! "compare" #(t#1) #() #(#5).to).mkApps [] [#1, #0]))
         , (#(LeftPat, RightPat), LTCtor)
         , (#(RightPat, LeftPat), GTCtor)
         , (#(RightPat, RightPat), ((openm! "compare" #(t#0) #() #(#4).to).mkApps [] [#1, #0]))
         )
       ),

  -- data Either a b = Left a | Right b
  .data 2 "Either" (★ -:> (★ -:> ★))
    #( ("Left",  ⟨2, #(★, ★), 0, #(), 1, #(t#1), (gt#"Either" • t#1) • t#0⟩)
     , ("Right", ⟨2, #(★, ★), 0, #(), 1, #(t#0), (gt#"Either" • t#1) • t#0⟩)
     ),


  .inst "compare" #(⟨"OrdBool", 1, #(t#0), 0, 1⟩) (λ[t#0]λ[t#0]
    (d#"compBool").mkApps [] [(.cast t#0 #2 #1), (.cast t#0 #2 #0)]
  ),

  .octor "OrdBool" ⟨1, #(★), 0, #(), 1, #(t#0 ~[★]~ gt#"Bool"), (gt#"Ord" • t#0)⟩,

  .defn "compBool" (gt#"Bool" -:> (gt#"Bool" -:> gt#"Ordering")) ( λ[gt#"Bool"]λ[gt#"Bool"]
    mtch' #(#1, #0)
      #( (#(FalsePat, FalsePat), EQCtor)
       , (#(FalsePat, TruePat), LTCtor)
       , (#(TruePat, FalsePat), GTCtor)
       , (#(TruePat, TruePat), EQCtor)
       )
  ),

  .defn "max" (∀[★] (gt#"Ord" • t#0) -:> t#0 -:> t#0 -:> t#0) (Λ[★]λ[gt#"Ord" • t#0]λ[t#0]λ[t#0]
    mtch' #((openm! "compare" #(t#0) #() #(#2).to).mkApps [] [#1, #0])
      #( (#(⟨"LT", 0,  #(), 0, 0⟩), #1)
       , (#(⟨"EQ", 0,  #(), 0, 0⟩), #1)
       , (#(⟨"GT", 0,  #(), 0, 0⟩), #0))),

  -- open compare : ∀ t. Ord t ⇒ t → t → Ord
  .openm "compare" ⟨1, #(★), 0, #(), 1, #(gt#"Ord" • t#0), t#0 -:> t#0 -:> gt#"Ordering" ⟩,

  -- open Ord : ★ → ★
  .odata "Ord" (★ -:> ★),

  -- data Ordering = LT | EQ | GT
  .data 3 "Ordering" ★
    #( ("LT", ⟨0, #(), 0, #(), 0, #(), gt#"Ordering"⟩)
     , ("EQ", ⟨0, #(), 0, #(), 0, #(), gt#"Ordering"⟩)
     , ("GT", ⟨0, #(), 0, #(), 0, #(), gt#"Ordering"⟩) )

  ] ++ EqBoolCtx ++ CastCtx


#guard OrdCtx.wf_globals == some ()
#guard OrdCtx.check_open_exhaustive == some ()

-- #eval! do
--   match lookup "eqOfOrd" OrdCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "eqOfOrd" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders (.data .opn) OrdCtx Δ n Ts #(⟨"OrdEither", 1, #(t#0), 2, 3⟩)

--         let t3 := inst! "OrdEither" #(t#2) #(t#1, t#0) #(#2, #1, #0).to
--         let t4 := inst! "EqOfOrd" #(t#2) #() #(t3).to
--         let R' := t4.infer_type OrdCtx (ζ ++ Δ) Γ
--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R') -- R'
--       else none
--   | _ => none


-- #eval! do
--   match lookup "compare" OrdCtx with
--   | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
--       if "compare" == y then
--         let Δ := (Ks1.list ++ Ks2.list).reverse
--         let (ζ, Γ) <- pattern_binders (.data .opn) OrdCtx Δ n Ts #(⟨"OrdEither", 1, #(t#0), 2, 3⟩)

--         let t1 := (d#"arrowc").mkApps [t#2, (gt#"Either" • t#1) • t#0, gt#"Ordering", gt#"Ordering"] [#0, refl! gt#"Ordering"]
--         let t2 := ((d#"arrowc").mkApps [t#2, (gt#"Either" • t#1) • t#0, t#2 -:> gt#"Ordering", ((gt#"Either" • t#1) • t#0) -:> gt#"Ordering"]) [#0, t1]
--         let t3 := ((d#"sym" •[t#2 -:> (t#2 -:> gt#"Ordering")]) •[((gt#"Either" • t#1) • t#0) -:> (((gt#"Either" • t#1) • t#0) -:> gt#"Ordering")]) • t2

--         let t4 := Term.cast t#0 t3 ((d#"compEither").mkApps [t#1, t#0] [#2, #1])
--         let R' <- t4.infer_type OrdCtx (ζ ++ Δ) Γ
--         return (ζ ++ Δ, Γ, R⟨Ren.add Ty ζ.length⟩, R') -- R'
--       else none
--   | _ => none


-- #eval (((openm! "compare" #(t#1) #() #(#5).to))).infer_type OrdCtx [★, ★] [gt#"Ord" • t#1, gt#"Ord" • t#0, ((gt#"Either" • t#1) • t#0), ((gt#"Either" • t#1) • t#0), t#1, t#1].reverse

-- #eval ((openm! "compare" #(t#0) #() #(#2).to)).infer_type OrdCtx [★] [t#0, t#0, gt#"Ord" • t#0]

end Core.Examples
