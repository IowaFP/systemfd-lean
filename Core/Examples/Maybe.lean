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
def MaybeBoolCtx : GlobalEnv := [

   /- Λ t. λ (i : Eq t).
        If EqMaybe[t] <- i.
          Λ u. λ (tmu : t ~ Maybe u). λ eqU : Eq u.
            eqMaybe ▹ sym (<t ~ Maybe u> → <t ~ Maybe u> → <Bool>)
    -/

  -- .inst "eq" #𝓋[ ⟨"EqMaybe", 1, #𝓋[ gt#"Maybe" • t#0 ], 2⟩ ] (λ[ t#0 ] λ [ t#0 ] -- #2 : t ~ Maybe u, #3 : Eq u
  --      TrueCtor),
       -- ((d#"eq@Maybe" •[t#0]) • #0))   ),


  -- ∀ a. Eq a →  Maybe a → Maybe a → Bool
  .defn "eq@Maybe" (∀[★] (gt#"Eq" • t#0) -:> (gt#"Maybe" • t#0) -:> (gt#"Maybe" • t#0) -:> gt#"Bool")
        (Λ[★] λ[gt#"Eq" • t#0] λ[ gt#"Maybe" • t#0] λ[gt#"Maybe" • t#0]
          mtch' #𝓋[#1]
           #𝓋[ (#𝓋[⟨"Nothing", 1, #𝓋[ t#0 ], 0⟩],
             mtch' #𝓋[#0]
                     #𝓋[ (#𝓋[ ⟨"Nothing", 1, #𝓋[ t#0 ], 0 ⟩] , TrueCtor)
                       , (#𝓋[ ⟨"Just", 1, #𝓋[ t#0 ], 1⟩ ], FalseCtor) ]
             ) ,
             (#𝓋[⟨"Just", 1, #𝓋[t#0], 1⟩],
                 mtch' #𝓋[#1]
                     #𝓋[ (#𝓋[ ⟨"Nothing", 1, #𝓋[ t#0 ], 0 ⟩] , FalseCtor)
                       , (#𝓋[ ⟨"Just", 1, #𝓋[ t#0 ], 1⟩ ], (openm! "eq" #𝓋[t#0] (Vec.to (#𝓋[ #4 ])) • #0) • #1) ]
             )
             ]),

  -- EqMaybe : ∀ t u. (t ~ Maybe u) → Eq u -> Eq t
  .octor "EqMaybe" ⟨2, #𝓋[★ , ★], 2, #𝓋[t#1 ~[★]~ (gt#"Maybe" • t#0) , gt#"Eq" • t#0 ],  (gt#"Eq" • t#1)⟩,

  -- data Maybe a = Nothing | Just a
  Global.data 2 "Maybe" (★ -:> ★)
           #𝓋[ ("Nothing", ⟨1, #𝓋[★], 0, #𝓋[], (gt#"Maybe" • t#0)⟩) ,
               ("Just", ⟨1, #𝓋[★], 1,  #𝓋[t#0],  (gt#"Maybe" • t#0)⟩) ]

  ] ++ EqBoolCtx

#guard MaybeBoolCtx.wf_globals == .some ()


def NothingCtor (T : Ty) : Term := ctor! "Nothing" #𝓋[T] .nil
def JustCtor (T : Ty) (Tm : Term) : Term := ctor! "Just" #𝓋[T] (Vec.to #𝓋[Tm])

#guard (NothingCtor gt#"Bool").infer_type MaybeBoolCtx [] [] == some (gt#"Maybe" • gt#"Bool")
#guard (JustCtor gt#"Bool" TrueCtor).infer_type MaybeBoolCtx [] [] == some (gt#"Maybe" • gt#"Bool")
#guard (JustCtor gt#"Bool" FalseCtor).infer_type MaybeBoolCtx [] [] == some (gt#"Maybe" • gt#"Bool")

#guard (refl! (gt#"Maybe" • gt#"Bool")).infer_type MaybeBoolCtx [] []
              == some ((gt#"Maybe" • gt#"Bool") ~[★]~ (gt#"Maybe" • gt#"Bool"))

-- #eval! Vec.Ty.repr (#𝓋[t#1 ~[★]~ (gt#"Maybe" • t#0) , gt#"Eq" • t#0 ].map (λ x => x[Sequ.append_vec (Vec.map su #𝓋[ gt#"Bool" , gt#"Maybe" • gt#"Bool" ]) +0] ))

def iMaybeBool : Term := inst! "EqMaybe" #𝓋[ gt#"Bool", gt#"Maybe" • gt#"Bool" ] (Vec.to #𝓋[ refl! (gt#"Maybe" • gt#"Bool"), iBool ])
#guard iMaybeBool.infer_type MaybeBoolCtx [] [] == some (gt#"Eq" • (gt#"Maybe" • gt#"Bool"))


def t0 := (((d#"eq@Maybe" •[gt#"Bool"]) • iBool)
                          • NothingCtor gt#"Bool")
                          • NothingCtor gt#"Bool"

#eval! t0.eval_loop MaybeBoolCtx -- True

def t0' := (((d#"eq@Maybe" •[gt#"Bool"]) • iBool)
                          • NothingCtor gt#"Bool")
                          • JustCtor gt#"Bool" TrueCtor
#eval! t0'.eval_loop MaybeBoolCtx -- True

-- #guard t.eval_loop MaybeBoolCtx == g#"True"


end Core.Examples
