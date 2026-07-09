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

import Lilac
open Lilac

namespace Core.Examples

def PCtx : GlobalEnv :=  [

  .defn "flipPair" (∀[★]∀[★] ((gt#"Pair" • t#1) • t#0) -:> ((gt#"Pair" • t#0) • t#1)) (
    Λ[★]Λ[★]λ[(gt#"Pair" • t#1) • t#0]
      (d#"mkPair").mkApps [t#0, t#1] [(d#"snd").mkApps [t#1, t#0] [#0], (d#"fst").mkApps [t#1, t#0] [#0]]

  ),

  .defn "snd" (∀[★]∀[★] ((gt#"Pair" • t#1) • t#0) -:> t#0)
    (Λ[★]Λ[★]λ[(gt#"Pair" • t#1) • t#0]
    mtch' #(#0)
      #( (#(⟨"mkP", 2, #(t#1, t#0), 0, 2⟩), #0) )
    ),

  .defn "fst" (∀[★]∀[★] ((gt#"Pair" • t#1) • t#0) -:> t#1)
    (Λ[★]Λ[★]λ[(gt#"Pair" • t#1) • t#0]
    mtch' #(#0)
      #( (#(⟨"mkP", 2, #(t#1, t#0), 0, 2⟩), #1) )
    ),

  .defn "mkPair" (∀[★]∀[★] t#1 -:> t#0 -:> ((gt#"Pair" • t#1) • t#0))
    (Λ[★]Λ[★]λ[t#1]λ[t#0] ctor! "mkP" #(t#1, t#0) #() #(#1, #0).to),

  .data 1 "Pair" (★ -:> ★ -:> ★)
    #(⟨"mkP", 2, #(★, ★), 0, #(), 2, #(t#1, t#0), (gt#"Pair" • t#1) • t#0⟩)

  ]


#guard PCtx.wf_globals == some ()


end Core.Examples
