import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep
import Core.Infer

namespace Core.Examples.Bool
def c1 := match! #0 v[ g#"S" ]  v[ λ[gt#"Nat"] g#"False" ] g#"True"
def c2 := λ[ gt#"Nat"] match! #1
                       v[ g#"S" ]
                       v[ λ[ gt#"Nat"] (g#"eq" • #1) • #0 ]
                       g#"False"

def NatCtxFix : List Global := [

    /- ==@Nat := λ x λ y.
                  case x of
                    Zero → case y of
                            Zero → True
                            _ → False
                    Suc → λ x'. case y of
                            Zero → False
                            Succ →  λ y'. ==@Nat x' y'
   -/

  .inst "eq"
     (λ[ gt#"Nat"] λ[gt#"Nat"]
        match! #1
        v[ g#"Z" , g#"S" ]
        v[ match! #0 v[ g#"S" ]  v[ λ[gt#"Nat"] g#"False" ] g#"True"
         , λ[ gt#"Nat"] match! #1
                       v[ g#"S" ]
                       v[ λ[ gt#"Nat"] (g#"eq" • #1) • #0 ]
                       g#"False"
         ]
        g#"False"
    ) ,

  .openm "eq" (gt#"Nat" -:> gt#"Nat" -:> gt#"Bool"),
  -- Bool = True | False
  .data "Bool" ★ v[ ("True", gt#"Bool"), ("False", gt#"Bool") ],

  -- two = add (S Z) (S Z)
  .defn "two" gt#"Nat" ((g#"add" • (g#"S" • g#"Z")) • (g#"S" • g#"Z")),

  .defn "add" (gt#"Nat" -:> gt#"Nat" -:> gt#"Nat")
        ((g#"fix" •[gt#"Nat" -:> gt#"Nat" -:> gt#"Nat"]) • g#"add_rec"),

  -- let add_rec : (Nat -> Nat -> Nat) -> Nat -> Nat -> Nat :=
  --   λ rec n m. ite zero <- n then m
  --     else ite succ <- n then λ x. succ (rec x m)
  --     else m
  .defn "add_rec"
        ((gt#"Nat" -:> gt#"Nat" -:> gt#"Nat") -:> gt#"Nat" -:> gt#"Nat" -:> gt#"Nat")
        (λ[ gt#"Nat" -:> gt#"Nat" -:> gt#"Nat"]
          λ[gt#"Nat"] λ[gt#"Nat"]
            match! #1
              v[ g#"Z", g#"S" ]
              v[ #0 ,
                 λ[ gt#"Nat" ] (g#"S" • ((#3 • #0) • #1)) ]
              g#"Z"
         ),

  -- instance fix = Λ a. λ f. f (fix i f)
  .inst "fix" (Λ[★] λ[t#0 -:> t#0] (#0 • ((g#"fix" •[t#0]) • #0))),
  -- open fix : ∀ a, (a -> a) -> a
  .openm "fix" (∀[★] (t#0 -:> t#0) -:> t#0),
  -- data Nat = Z | Succ Nat
  .data "Nat" ★ v[ ("Z", gt#"Nat"), ("S", gt#"Nat" -:> gt#"Nat") ]

]

#guard Globals.wf_globals NatCtxFix == some ()
-- #eval eval_loop NatCtxFix g#"two"

#guard ((g#"eq" • g#"Z") • g#"Z").eval_loop NatCtxFix  == g#"True"
#guard ((g#"eq" • (g#"Z")) • ((g#"S" • g#"Z"))).eval_loop NatCtxFix == g#"False"
#guard ((g#"eq" • (g#"S" • g#"Z")) • ((g#"S" • g#"Z"))).eval_loop NatCtxFix == g#"True"
#guard ((g#"eq" • (g#"S" • (g#"S" • g#"Z"))) • (g#"S" • (g#"S" • g#"Z"))).eval_loop NatCtxFix == g#"True"
#guard  ((g#"eq" • (g#"two")) • (g#"S" • (g#"S" • g#"Z"))).eval_loop NatCtxFix == g#"True"
#guard  ((g#"eq" • (g#"two")) • ((g#"S" • g#"Z"))).eval_loop NatCtxFix == g#"False"


#guard ((g#"eq" • g#"Z") • g#"Z").infer_type NatCtxFix [] [] == .some (gt#"Bool")
#guard ((g#"eq" • (g#"two")) • ((g#"S" • g#"Z"))).infer_type NatCtxFix [] [] == .some (gt#"Bool")



#eval NatCtxFix
namespace Core.Exampes.Bool
