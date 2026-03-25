import Surface.Global
import Core.Global

import Surface.Typing

import Translation.Ty
import Translation.Term




inductive Translation.GlobalWf : Surface.GlobalEnv -> Core.GlobalEnv -> Surface.Global -> Prop where
| data {ctors : Vect n (String × Surface.Ty)} {G : Surface.GlobalEnv}{G' : Core.GlobalEnv}:
  (∀ i y T, ctors i = (y, T) ->
    (Surface.Global.data x K Vect.nil :: G)&[] ⊢s T : `★
    ∧ Surface.ValidCtor x T
    ∧ x ≠ y
    ∧ Surface.lookup y G = none) ->
  (∀ i j, (ctors i).1 ≠ (ctors j).1) ->
  Surface.lookup x G = none ->
  GlobalWf G G' (Surface.Global.data x K ctors)
| defn :
  Surface.lookup x G = none ->
  G&[] ⊢s T : `★ ->
  Surface.Term.Elab G G' .chk [] [] t T t' ->
  GlobalWf G G' (Surface.Global.defn x T t)
| classDecl :
  Surface.lookup s G = none ->
  Surface.ValidOpenKind K ->
  (∀ i j, (ms i).1 ≠ (ms j).1) ->
  (∀ i y T, ms i = (y, T) ->
    (Surface.Global.classDecl s K Vect.nil :: G)&[] ⊢s T : `★
    ∧ Surface.ValidClassMethodTy s T
    ∧ s ≠ y
    ∧ Surface.lookup y G = none) ->
  GlobalWf G G' (Surface.Global.classDecl s K ms)
| instDecl :
  Surface.ValidClassInstTy C T ->
  -- TODO: Do Non-overlapping check here
  Surface.lookup C G = some (.opent C K ms') ->
  -- TODO: check for method types
  GlobalWf G G' (.instDecl T ms)



inductive Surface.Global.Elab : Surface.GlobalEnv -> Core.GlobalEnv -> Prop
| nil : Surface.Global.Elab [] []

| defn :
  Surface.Global.Elab G G' ->

  Surface.lookup x G = none ->
  G&[] ⊢s T : `★ ->
  Surface.Term.Elab G G' .chk [] [] t T t' ->

  Surface.Global.Elab (.cons (.defn x T t) G) ((.defn x (T.translate) t') :: G')

| data {n : Nat} {ctors : Vect n (String × Ty)} {ctors' : Vect n (String × Core.Ty)} :
  Surface.Global.Elab G G' ->

  (∀ i y T, ctors i = (y, T) ->
    (Surface.Global.data x K Vect.nil :: G)&[] ⊢s T : `★
    ∧ Surface.ValidCtor x T
    ∧ x ≠ y
    ∧ Surface.lookup y G = none) ->
  (∀ i j, (ctors i).1 ≠ (ctors j).1) ->
  Surface.lookup x G = none ->

  ctors' = (λ i => ((ctors i).1 , (ctors i).2.translate)) ->

  Surface.Global.Elab (.cons (.data (n := n) x K ctors) G) (.cons (.data n x K.translate ctors') G')

| classDecl {n : Nat} {ms : Vect n (String × Ty)} {ms' : Vect n Core.Global} :
  Surface.Global.Elab G G' ->

  Surface.lookup x G = none ->
  Surface.ValidOpenKind K ->
  (∀ i j, (ms i).1 ≠ (ms j).1) ->
  (∀ i y T, ms i = (y, T) ->
    (Surface.Global.classDecl x K Vect.nil :: G)&[] ⊢s T : `★
    ∧ Surface.ValidClassMethodTy x T
    ∧ x ≠ y
    ∧ Surface.lookup y G = none) ->
  ms' = (λ i => Core.Global.openm (ms i).1 (ms i).2.translate) ->

  Surface.Global.Elab ((.classDecl x K ms) :: G) (ms'.to_list ++ (Core.Global.opent x K.translate :: G'))


notation:170 G:170 " -↪ " G':170 => Surface.Global.Elab G G'

namespace Test.Core.Global

#guard (gt`#"One").translate == gt#"One"

end Test.Core.Global
