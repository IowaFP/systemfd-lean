
import Surface.Global
import Surface.Term

import Translation.Global

import Surface.Examples.Maybe

namespace Surface.Examples.TypeFunction


def TypeFunctionCtx : GlobalEnv := [

  .instDecl "FMM" ⟨2 , #(★, ★), 2, #(★, ★),
          3, #((gt#"Maybe" • t#1) ~[★]~ t#3, (gt#"Maybe" • t#0) ~[★]~ t#2, (gt#"F" • t#1) • t#0),
             ((gt#"F" • t#3) • t#2)⟩ [],

  .instDecl "FIB" ⟨2, #(★, ★), 0, #(), 2, #(gt#"Int" ~[★]~ t#1, gt#"Bool" ~[★]~ t#0), (gt#"F" • t#1) • t#0⟩ [],

  .classDecl "F" #(★, ★) [⟨"fdF", [1], 0⟩] [] [],

  .data "Int" ★ #()

  ] ++ Surface.Examples.Maybe.mbenv


#eval TypeFunctionCtx
#eval Translation.translate_SI TypeFunctionCtx
#eval! do
  let benv' <- Translation.translate_SI TypeFunctionCtx
  Translation.translate_IC benv'


#guard (do
  let benv' <- Translation.translate_SI TypeFunctionCtx
  let Γ <- Translation.translate_IC benv'
  return Γ.wf_globals) == .ok ()

#guard (do
  let benv' <- Translation.translate_SI TypeFunctionCtx
  let Γ <- Translation.translate_IC benv'
  return Γ.check_open_exhaustive) == .ok ()


end Surface.Examples.TypeFunction
