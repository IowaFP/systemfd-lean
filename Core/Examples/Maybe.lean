import Core.Ty
import Core.Term
import Core.Global
import Core.Vec
import Core.Infer

import Core.Eval.BigStep
import Core.Examples.Boolean
import Core.Examples.Common

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

def eq_maybe_inst : Term :=
    let t1 := (((((d#"arrowc" •[t#1]) •[gt#"Maybe" • t#0]) •[gt#"Bool"]) •[gt#"Bool"]) • #1) • (refl! gt#"Bool")
    let t2 := (((((d#"arrowc" •[t#1]) •[gt#"Maybe" • t#0]) •[t#1 -:> gt#"Bool"]) •[(gt#"Maybe" • t#0) -:> gt#"Bool"]) • #1) • t1
    let t3 := ((d#"sym" •[t#1 -:> (t#1 -:> gt#"Bool")]) •[(gt#"Maybe" • t#0) -:> ((gt#"Maybe" • t#0) -:> gt#"Bool")]) • t2
    Term.cast t#0 t3 ((d#"eq@Maybe" •[t#0]) • #0)

def NothingPattern : Pattern 1 := #(⟨"Nothing", 1, #(t#0), 0, 0⟩)
def JustPattern : Pattern 1 := #(⟨"Just", 1, #(t#0), 0, 1⟩)


def MaybeBoolCtx : GlobalEnv := [

   /- Λ t.
        If EqMaybe[t] <- i.
            Λ u. λ (tmu : t ~ Maybe u). λ eqU : Eq u.
            eqMaybe @u eqU ▹ sym (tmu -c> tmu -c> <Bool>)
    -/
  .inst "eq" #(⟨"EqMaybe", 1, #(t#0), 1, 2⟩) (-- #1 : t ~ Maybe u, #0 : Eq u
        eq_maybe_inst
       ) ,

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
  .octor "EqMaybe" ⟨1, #(★), 1, #(★), 2, #(t#1 ~[★]~ gt#"Maybe" • t#0 , gt#"Eq" • t#0),  gt#"Eq" • t#1⟩,

  -- data Maybe a = Nothing | Just a
  Global.data 2 "Maybe" (★ -:> ★)
           #( ("Nothing", ⟨1, #(★), 0, #(), 0, #(), (gt#"Maybe" • t#0)⟩) ,
              ("Just", ⟨1, #(★), 0, #(), 1,  #(t#0), (gt#"Maybe" • t#0)⟩) )

  ] ++ EqBoolCtx ++ CastCtx

-- #eval MaybeBoolCtx

#guard MaybeBoolCtx.wf_globals == .some ()

-- #eval lookup "eq" MaybeBoolCtx
-- na = 1, Ks1 = [★], nb = 0, Ks2 = [],   nc = 1,  Ts := [Eq t],              R := t -> t -> Bool
-- #eval lookup_spine_type MaybeBoolCtx "EqMaybe"
-- na = 1, Ks1 = [★], nb = 1, Ks2 := [★], nc := 2, Ts := [t#1 ~ Maybe t#0, Eq #0], R := Eq t

#eval! do
  match lookup "eq" MaybeBoolCtx with
  | some (.openm y ⟨_, Ks1, _, Ks2, n, Ts, R⟩) =>
      if "eq" == y then
        let Δ := (Ks1.list ++ Ks2.list).reverse
        let (ζ, Γ) <- pattern_binders MaybeBoolCtx Δ n Ts #(⟨"EqMaybe", 1, #(t#0), 1, 2⟩)


        -- let t1 := (((((d#"arrowc" •[t#1]) •[gt#"Maybe" • t#0]) •[gt#"Bool"]) •[gt#"Bool"]) • #1) • (refl! gt#"Bool")
        -- let t2 := (((((d#"arrowc" •[t#1]) •[gt#"Maybe" • t#0]) •[t#1 -:> gt#"Bool"]) •[(gt#"Maybe" • t#0) -:> gt#"Bool"]) • #1) • t1
        -- let t3 := ((d#"sym" •[t#1 -:> (t#1 -:> gt#"Bool")]) •[(gt#"Maybe" • t#0) -:> ((gt#"Maybe" • t#0) -:> gt#"Bool")]) • t2

        -- let t4 := Term.cast t#0 t3 ((d#"eq@Maybe" •[t#0]) • #0)
        -- let R' <- t4.infer_type MaybeBoolCtx (ζ ++ Δ) Γ
        return (ζ ++ Δ, Γ) -- R'

      else none
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

#guard t0.eval_loop MaybeBoolCtx == TrueCtor

def mt1 := (((d#"eq@Maybe" •[gt#"Bool"]) • iBool)
                          • NothingCtor gt#"Bool")
                          • JustCtor gt#"Bool" TrueCtor

#guard mt1.eval_loop MaybeBoolCtx == FalseCtor


def mt2 := (((d#"eq@Maybe" •[gt#"Bool"]) • iBool)
                          • JustCtor gt#"Bool" TrueCtor)
                          • JustCtor gt#"Bool" TrueCtor
#guard mt2.eval_loop MaybeBoolCtx == TrueCtor


def mt3 := openm! "eq" #(gt#"Maybe" • gt#"Bool") .nil (Vec.to #( iMaybeBool ))
#guard mt3.infer_type MaybeBoolCtx [] [] == some ((gt#"Maybe" • gt#"Bool") -:> (gt#"Maybe" • gt#"Bool") -:> gt#"Bool")

#guard ((mt3 • JustCtor (gt#"Bool") TrueCtor) • JustCtor gt#"Bool" TrueCtor).infer_type MaybeBoolCtx [] [] == some (gt#"Bool")

-- #eval ((mt3 • JustCtor gt#"Bool" TrueCtor) • JustCtor gt#"Bool" TrueCtor).eval_loop MaybeBoolCtx

def e1 := (mt3 • JustCtor gt#"Bool" TrueCtor) • JustCtor gt#"Bool" TrueCtor
#eval e1
#guard e1.infer_type MaybeBoolCtx [] []  == some (gt#"Bool")

/-
(eq •[(gt#Maybe • gt#Bool)]•[]•{EqMaybe •[(gt#Maybe • gt#Bool)]•[gt#Bool] •{EqBool •[gt#Bool]•[]•{(refl! gt#Bool)}, (refl! (gt#Maybe • gt#Bool))}}
    • Just •[gt#Bool, ]•[]•{True •[]•[]•{}, }) • Just •[gt#Bool, ]•[]•{True •[]•[]•{}, }
-/

def e2 := (e1.eval MaybeBoolCtx).getD (d#"fail")
#eval e2
/-
((((d#eq@Maybe •[gt#Maybe • gt#Bool]) • (refl! (gt#Maybe • gt#Bool)))▸(((d#sym •[t#0 -:> t#0 -:> gt#Bool]) •[(gt#Maybe • (gt#Maybe • gt#Bool)) -:> (gt#Maybe • (gt#Maybe • gt#Bool)) -:> gt#Bool]) • ((((((d#arrowc •[t#0]) •[gt#Maybe • (gt#Maybe • gt#Bool)]) •[t#0 -:> gt#Bool]) •[(gt#Maybe • (gt#Maybe • gt#Bool)) -:> gt#Bool]) • EqBool •[gt#Bool, ]•[]•{(refl! gt#Bool), }) • ((((((d#arrowc •[t#0]) •[gt#Maybe • (gt#Maybe • gt#Bool)]) •[gt#Bool]) •[gt#Bool]) • EqBool •[gt#Bool, ]•[]•{(refl! gt#Bool), }) • (refl! gt#Bool))))) • Just •[gt#Bool, ]•[]•{True •[]•[]•{}, }) • Just •[gt#Bool, ]•[]•{True •[]•[]•{}, }
-/

#eval! e2.infer_type MaybeBoolCtx [] []

def e3 := (e2.eval MaybeBoolCtx).getD (d#"fail")
#eval e3
def e4 := (e3.eval MaybeBoolCtx).getD (d#"fail")
#eval e4
def e5 := (e4.eval MaybeBoolCtx).getD (d#"fail")
#eval e5
def e6 := (e5.eval MaybeBoolCtx).getD (d#"fail")
#eval e6
def e7 := (e6.eval MaybeBoolCtx).getD (d#"fail")
#eval e7



end Core.Examples


/-

((((d#eq@Maybe •[gt#Maybe • gt#Bool]) • (refl! (gt#Maybe • gt#Bool)))▸(((d#sym •[t#0 -:> t#0 -:> gt#Bool]) •[(gt#Maybe • (gt#Maybe • gt#Bool)) -:> (gt#Maybe • (gt#Maybe • gt#Bool)) -:> gt#Bool]) • ((((((d#arrowc •[t#0]) •[gt#Maybe • (gt#Maybe • gt#Bool)]) •[t#0 -:> gt#Bool]) •[(gt#Maybe • (gt#Maybe • gt#Bool)) -:> gt#Bool]) • EqBool •[gt#Bool | ]•[]•{(refl! gt#Bool) | }) • ((((((d#arrowc •[t#0]) •[gt#Maybe • (gt#Maybe • gt#Bool)]) •[gt#Bool]) •[gt#Bool]) • EqBool •[gt#Bool | ]•[]•{(refl! gt#Bool) | }) • (refl! gt#Bool))))) • Just •[gt#Bool | ]•[]•{True •[]•[]•{} | }) • Just •[gt#Bool | ]•[]•{True •[]•[]•{} | }


-/
