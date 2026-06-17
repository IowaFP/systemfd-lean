import Core.Ty
import Core.Term
import Core.Global
import Core.Vec
import Core.Infer

import Core.Eval.BigStep
import Core.Examples.Boolean

import LeanSubst
import Lilac
open Lilac
open LeanSubst

-- def c1  := mtch' #0 #𝓋[ g#"Nothing" •[t#0] , g#"Just" •[t#0] ]
--                      v[ g#"True" , λ[t#0] g#"False" ]
--                      g#"False"

-- def c2 := λ[t#0] match! #1
--               v[ g#"Nothing" •[t#0], g#"Just" •[t#0]]
--               v[ g#"False", λ[t#0] ((((g#"eq" •[ t#0 ]) •(.open) #4) • #1) •#0) ]
--               g#"False"

namespace Core.Examples

def NothingPattern : Pattern 1 := #(⟨"Nothing", 1, #(t#0), 0, 0⟩)
def JustPattern : Pattern 1 := #(⟨"Just", 1, #(t#0), 0, 1⟩)


def MaybeBoolCtx : GlobalEnv := [

   /- Λ t. λ (i : Eq t).
        If EqMaybe[t] <- i.
           Λ u. λ (tmu : t ~ Maybe u). λ eqU : Eq u.
            eqMaybe @Bool eqU ▹ sym (tmu -c> tmu -c> <Bool>)
    -/
  -- .inst "eq" #(⟨"EqMaybe", 1, #(t#0), 1, 2⟩) (λ[ t#1 ] λ[ t#1 ] -- #3 : t ~ Maybe u, #2 : Eq u
  --      (((d#"eq@Maybe" •[t#0]) • #2) • (.cast t#1 #3 #1)) • (.cast t#1 #3 #0)) ,

  -- ∀ a. Eq a →  Maybe a → Maybe a → Bool
  .defn "eq@Maybe" (∀[★] (gt#"Eq" • t#0) -:> (gt#"Maybe" • t#0) -:> (gt#"Maybe" • t#0) -:> gt#"Bool")
        (Λ[★] λ[gt#"Eq" • t#0] λ[ gt#"Maybe" • t#0 ] λ[gt#"Maybe" • t#0]
          (mtch' #(#1)
            #((NothingPattern,
                (mtch' #(#0)
                       #( (NothingPattern , TrueCtor)
                        , (JustPattern, FalseCtor)))) ,
              (JustPattern,
                (mtch' #(#1)
                     #( (NothingPattern , FalseCtor)
                       , (JustPattern, (openm! "eq" #(t#0) #() (Vec.to (#( #4 ))) • #0) • #1))))
             ))),

  .defn "isNothing" (∀[★] (gt#"Maybe" • t#0) -:> gt#"Bool")
        (Λ[★] λ[gt#"Maybe" • t#0]
          (mtch' #(#0)
            #( (NothingPattern, TrueCtor) ,
               (JustPattern, FalseCtor)))),


  -- EqMaybe : ∀ t u. (t ~ Maybe u) → Eq u → Eq t
  .octor "EqMaybe" ⟨1, #(★), 1, #(★), 2, #(t#1 ~[★]~ (gt#"Maybe" • t#0) , gt#"Eq" • t#0 ),  (gt#"Eq" • t#1)⟩,

  -- data Maybe a = Nothing | Just a
  Global.data 2 "Maybe" (★ -:> ★)
           #( ("Nothing", ⟨1, #(★), 0, #(), 0, #(), (gt#"Maybe" • t#0)⟩) ,
              ("Just", ⟨1, #(★), 0, #(), 1,  #(t#0), (gt#"Maybe" • t#0)⟩) )

  ] ++ EqBoolCtx

#eval MaybeBoolCtx

#guard MaybeBoolCtx.wf_globals == .some ()

#eval lookup "eq" MaybeBoolCtx
#eval lookup_spine_type MaybeBoolCtx "EqMaybe"
-- na = 1, Ks1 = [★], nb = 1, Ks2 := [★],  nc := 2, Ts := [t ~ Maybe u] Eq u, R := Eq t

#eval do
  let e := lookup "eq" MaybeBoolCtx
  match e with
  | some (.openm _ ⟨_, Ks1, _, Ks2, m, Ts, R⟩) => do
      pattern_binders MaybeBoolCtx [] m Ts
        (#(⟨"EqMaybe", 2, #(gt#"Maybe"•t#0, t#1), 1, 2⟩ ))
      -- let T <- t.infer_type G Ks.to_list Γ
      -- if T == R then return () else none
  | _ => none


def NothingCtor (T : Ty) : Term := ctor! "Nothing" #(T) .nil .nil
def JustCtor (T : Ty) (Tm : Term) : Term := ctor! "Just" #(T) .nil (Vec.to #(Tm))

#guard (NothingCtor gt#"Bool").infer_type MaybeBoolCtx [] [] == some (gt#"Maybe" • gt#"Bool")
#guard (JustCtor gt#"Bool" TrueCtor).infer_type MaybeBoolCtx [] [] == some (gt#"Maybe" • gt#"Bool")
#guard (JustCtor gt#"Bool" FalseCtor).infer_type MaybeBoolCtx [] [] == some (gt#"Maybe" • gt#"Bool")

#guard (refl! (gt#"Maybe" • gt#"Bool")).infer_type MaybeBoolCtx [] []
              == some ((gt#"Maybe" • gt#"Bool") ~[★]~ (gt#"Maybe" • gt#"Bool"))

def iMaybeBool : Term :=
    inst! "EqMaybe" #(gt#"Maybe" • gt#"Bool") #(gt#"Bool") (Vec.to #( refl! (gt#"Maybe" • gt#"Bool"), iBool ))

#guard iMaybeBool.infer_type MaybeBoolCtx [] [] == some (gt#"Eq" • (gt#"Maybe" • gt#"Bool"))


def t0 := (((d#"eq@Maybe" •[gt#"Bool"]) • iBool)
                          • NothingCtor gt#"Bool")
                          • NothingCtor gt#"Bool"

#eval! t0.eval_loop MaybeBoolCtx -- True

def mt1 := (((d#"eq@Maybe" •[gt#"Bool"]) • iBool)
                          • NothingCtor gt#"Bool")
                          • JustCtor gt#"Bool" TrueCtor
#eval! mt1.eval_loop MaybeBoolCtx -- True


def mt2 := (((d#"eq@Maybe" •[gt#"Bool"]) • iBool)
                          • JustCtor gt#"Bool" TrueCtor)
                          • JustCtor gt#"Bool" TrueCtor
#eval! mt2.eval_loop MaybeBoolCtx -- True


def mt3 := openm! "eq" #(gt#"Maybe" • gt#"Bool") .nil (Vec.to #( iMaybeBool ))
#eval! mt3.infer_type MaybeBoolCtx [] []

#eval! ((mt3 • JustCtor (gt#"Bool") TrueCtor) • JustCtor gt#"Bool" TrueCtor).infer_type MaybeBoolCtx [] []

#eval ((mt3 • JustCtor gt#"Bool" TrueCtor) • JustCtor gt#"Bool" TrueCtor).eval_loop MaybeBoolCtx

end Core.Examples
