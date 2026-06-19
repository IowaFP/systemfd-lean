import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer

namespace Core.Examples

def Ctx : GlobalEnv := [
    .data 1 "C" ★ #(("c", ⟨0, #(), 3, #(★, ★, ★), 2, #(t#0, t#2), gt#"C"⟩)),
    .data 1 "B" (★ -:> ★) #(("b", ⟨2, #(★, ★), 1, #(★), 3, #(gt#"B" • t#1, t#0, t#1), gt#"B" • t#2⟩)),
    .data 1 "A" (★ -:> ★) #(("a", ⟨1, #(★), 2, #(★, ★), 1, #(t#1), gt#"A" • t#2⟩)),
    .data 1 "Unit" ★ #(("unit", ⟨0, #(), 0, #(), 0, #(), gt#"Unit"⟩))
  ]

def unit : Term := ctor! "unit" #() #() #().to

def test1 : Term := ctor! "a" #(gt#"Unit") #(gt#"Unit", gt#"Unit") #(unit).to

-- def test2 : Term := λ[gt#"A"]
--   mtch' #(#0) #(
--     (#(⟨"a", 0, #(), 2, 1⟩), unit)
--   )

-- #eval! pattern_binders Ctx [] 1 #(gt#"A") #(⟨"a", 0, #(), 2, 1⟩)

def test2 : Term := Λ[★] λ[gt#"A" • gt#"Unit"] λ[gt#"B" • t#0] λ[gt#"C"]
  mtch' #(#2, #1, #0) #(
    (#(⟨"a", 1, #(gt#"Unit"), 2, 1⟩, ⟨"b", 2, #(t#0, gt#"Unit"), 1, 3⟩, ⟨"c", 0, #(), 3, 2⟩),
      #4)
  )

#eval!
  pattern_binders Ctx [★] 2 #(gt#"B" • t#0, gt#"C")
    #(⟨"b", 2, #(t#0, gt#"Unit"), 1, 3⟩, ⟨"c", 0, #(), 3, 2⟩)


#eval!
  pattern_binders Ctx [★] 3 #(gt#"A" • gt#"Unit", gt#"B" • t#0, gt#"C")
    #(⟨"a", 1, #(gt#"Unit"), 2, 1⟩, ⟨"b", 2, #(t#0, gt#"Unit"), 1, 3⟩, ⟨"c", 0, #(), 3, 2⟩)

#eval! lookup_kind Ctx "A"

#eval! Ctx.wf_globals
#eval! test1.infer_type Ctx [] []
#eval! test2.infer_type Ctx [] []

end Core.Examples

/-
Here is my explanation of a type-binder bug in pattern binding Apoorv found:

Consider the following artificial example on closed data:
```lean4
def Ctx : GlobalEnv := [
    .data 1 "C" ★ #(("c", ⟨0, #(), 3, #(★, ★, ★), 2, #(t#0, t#2), gt#"C"⟩)),
    .data 1 "B" (★ -:> ★) #(("b", ⟨2, #(★, ★), 1, #(★), 3, #(gt#"B" • t#1, t#0, t#1), gt#"B" • t#2⟩)),
    .data 1 "A" (★ -:> ★) #(("a", ⟨1, #(★), 2, #(★, ★), 1, #(t#1), gt#"A" • t#2⟩)),
    .data 1 "Unit" ★ #(("unit", ⟨0, #(), 0, #(), 0, #(), gt#"Unit"⟩))
  ]

def test2 : Term := Λ[★] λ[gt#"A" • gt#"Unit"] λ[gt#"B" • t#0] λ[gt#"C"]
  mtch' #(#2, #1, #0) #(
    (#(⟨"a", 1, #(gt#"Unit"), 2, 1⟩, ⟨"b", 2, #(t#0, gt#"Unit"), 1, 3⟩, ⟨"c", 0, #(), 3, 2⟩),
      #4)
  )

#eval! -- some ([★, ★, ★, ★, ★, ★], [t#2, t#0, gt#Unit, t#3, gt#B • gt#Unit, t#5])
  pattern_binders Ctx [★] 3 #(gt#"A" • gt#"Unit", gt#"B" • t#0, gt#"C")
    #(⟨"a", 1, #(gt#"Unit"), 2, 1⟩, ⟨"b", 2, #(t#0, gt#"Unit"), 1, 3⟩, ⟨"c", 0, #(), 3, 2⟩)

#eval! -- some (∀[ ★ ] ((gt#A • gt#Unit) -:> ((gt#B • t#0) -:> (gt#C -:> gt#B • gt#Unit))))
  test2.infer_type Ctx [] []
```

When we're trying to generate binders for a pattern (e.g., `⟨"c", 0, #(), 3, 2⟩`) we lookup the type of the constructor (`c`), but this type is in an empty context. Even more annoying, the parts of the type we care about are under quantifiers.

Consider this pattern: `⟨"b", 2, #(t#0, gt#"Unit"), 1, 3⟩`, we want to substitute `t#0` and `gt#"Unit"` (the universally quantified variables) into the type of `"b"`, but to do that properly, we have to lift to account for the *other* universally quantified types (which we like to refer to as "existential").

Hence, what we had before was `Ts[σ]` (where `Ts` is the collection of not-quantified types), but we actually need `Ts[σ.lift n]` (where `n` is the length of the "existential" quantified types).

This is however not enough, because as we're working through the parallel patterns we're adding more types onto the final context, so we *also* need to account for these. That means we need `Ts[σ.lift n]⟨.add Ty ℓ.length⟩` where `ℓ` is the previously added bound types.

But wait, there's more. We also need to check the return type (call it `R`) of `"b"`. Before we had `R[σ] = R'` (where `R` is from the type of `"b"` and `R'` is the actual scrutinee type that should match after subtitution). This has the same problem, but we *also* need to correct `R'` to account for the "existential" type variables. that gives us `R[σ.lift n] = R'⟨add Ty n⟩` as the correct check.
-/
