import Core.Ty
import Core.Term
import Core.Global
import Core.Vec

import Core.Eval.BigStep

def c1  := Λ[★] match! #0 v[ "Nothing", "Just"]
                     v[ Λ[★] g#"True" , Λ[★] λ[BaseKind.closed, t#0] g#"False" ]

def c2 := Λ[★] λ[.closed, t#0] match! #1
              v[ "Nothing", "Just" ]
              v[ Λ[★] g#"False", Λ[★] λ[BaseKind.closed, t#0] ((((g#"eq" •[ t#0 ]) • #4) • #1) •#0) ]

def MaybeBoolCtx : List Global := [


   /- Λ t. λ (i : Eq t).
        If EqMaybe[t] <- i.
          Λ u. λ (tmu : t ~ Maybe u). λ eqU : Eq u.
            eqMaybe ▹ sym (<t ~ Maybe u> → <t ~ Maybe u> → <Bool>)
    -/

  .inst "eq" (Λ[★] λ[BaseKind.open, gt#"Eq" • t#0]
       .guard (g#"EqMaybe" •[t#0]) #0
         (Λ[★] λ[BaseKind.closed, t#1 ~[★]~ (gt#"Maybe" • t#0)] λ[ BaseKind.open , gt#"Eq" • t#0]
     ((g#"eq@Maybe" •[t#0]) • #0) ▹ sym! (#1 -c> #1 -c> refl! gt#"Bool"))
   ),


  -- ∀ a. Eq a →  Maybe a → Maybe a → Bool
  .defn "eq@Maybe" (∀[★] (gt#"Eq" • t#0) =:> (gt#"Maybe" • t#0) -:> (gt#"Maybe" • t#0) -:> gt#"Bool")
        (Λ[★] λ[.open, gt#"Eq" • t#0] λ[.closed, gt#"Maybe" • t#0] λ[.closed, gt#"Maybe" • t#0]
          match! #1 v[ "Nothing" , "Just" ]
                    v[ c1 , c2 ]

        ),

  -- EqMaybe : ∀ t u. (t ~ Maybe u) → Eq u -> Eq t
  .instty "EqMaybe" (∀[★] ∀[★] (t#1 ~[★]~ (gt#"Maybe" • t#0)) -:> (gt#"Eq" • t#0) -:>  (gt#"Eq" • t#1)),

  -- data Maybe a = Nothing | Just a
  .data "Maybe" (★ -:> ★) v[ ("Nothing", ∀[★] gt#"Maybe" • t#0), ("Just", ∀[★] t#0 -:> (gt#"Maybe" • t#0)) ],


  -- instance (==)[t] i
  --    If EqBool[t] tBool ← i
  --        let c = refl @ tBool @ (refl @ tBool @ refl) in
  --        λb1. λb2. ==@Bool ▹ sym c
  .inst "eq" (Λ[ ★ ] λ[ .open, gt#"Eq" • t#0 ]
        .guard (g#"EqBool" •[ t#0 ]) #0
           (λ[.open, t#1 ~[★]~ gt#"Bool"] (g#"eqBool" ▹ sym! (#0 -c> #0 -c> refl! gt#"Bool")))
   ),

  .defn "eqBool" (gt#"Bool" -:> gt#"Bool" -:> gt#"Bool")
    (λ[ .closed,  .global "Bool" ] λ[ .closed, .global "Bool" ]
      match! #1
      v[ "True", "False" ]
      v[ match! #0 v[ "True", "False" ] v[ g#"True", g#"False"] ,
         match! #0 v[ "True", "False" ] v[ g# "False", g# "False"]
       ]),

  -- EqBool : ∀ t. t ~ Bool → Eq t
  .instty "EqBool" (∀[★] (t#0 ~[★]~ gt#"Bool") -:> (gt#"Eq" • t#0)) ,

  -- == : ∀ t. Eq t → t → t → Bool
  .openm "eq" (∀[★] (gt#"Eq" • t#0) -:> t#0 -:> t#0 -:> gt#"Bool") ,

  -- class Eq a
  .opent "Eq" (★ -:> ◯),
  -- data Bool = True | False
  .data "Bool" ★ v[ ("True", gt#"Bool") , (("False"), gt#"Bool") ]

]


def t0 := (((g#"eq@Maybe" •[gt#"Bool"]) • ((g#"EqBool" •[gt#"Bool"]) • refl! gt#"Bool"))
                          • (g#"Nothing" •[gt#"Bool"] ))
                          • (g#"Nothing" •[gt#"Bool"])
-- #eval! eval_loop MaybeBoolCtx t0 -- True

def t0' := (((g#"eq@Maybe" •[gt#"Bool"]) • ((g#"EqBool" •[gt#"Bool"]) • refl! gt#"Bool"))
                           • (g#"Nothing" •[gt#"Bool"]) )
                           • ((g#"Just" •[gt#"Bool"]) • g#"True")
-- #eval! eval_loop MaybeBoolCtx t0' -- False


def t1 := (((g#"eq@Maybe" •[gt#"Bool"]) • ((g#"EqBool" •[gt#"Bool"]) • refl! gt#"Bool"))
                         • ((g#"Just" •[gt#"Bool"]) • g#"True"))
                         • ((g#"Just" •[gt#"Bool"]) • g#"True")
-- #eval! eval_loop MaybeBoolCtx t1 -- True

-- eq : ∀ t -> Eq t -> t -> t -> Bool
def t2 := let eqt := ((((g#"EqMaybe") •[ gt#"Maybe" • gt#"Bool" ]) •[ gt#"Bool" ])
                                       • (refl! (gt#"Maybe" • gt#"Bool")))
                                       • (((g#"EqBool" •[gt#"Bool"]) • refl! gt#"Bool"));
          ((((g#"eq" •[ gt#"Maybe" • gt#"Bool" ])
                     • eqt)
                     • ((g#"Just" •[gt#"Bool"]) • g#"True")))
                     • ((g#"Just" •[gt#"Bool"]) • g#"True")

#eval! eval_loop MaybeBoolCtx t2

def t3 := let eqt := ((((g#"EqMaybe") •[ gt#"Maybe" • gt#"Bool" ]) •[ gt#"Bool" ])
                                       • (refl! (gt#"Maybe" • gt#"Bool")))
                                       • (((g#"EqBool" •[gt#"Bool"]) • refl! gt#"Bool"));
          ((((g#"eq" •[ gt#"Maybe" • gt#"Bool" ])
                     • eqt)
                     • ((g#"Just" •[gt#"Bool"]) • g#"True")))
                     • ((g#"Nothing" •[gt#"Bool"]))

#eval! eval_loop MaybeBoolCtx t3




-- #eval! eval MaybeBoolCtx t2
-- def t3 := Option.getD (eval MaybeBoolCtx t2) `0
-- #eval! eval MaybeBoolCtx t3
-- def t4 := Option.getD (eval MaybeBoolCtx t3) `0
-- #eval! eval MaybeBoolCtx t4
-- def t5 := Option.getD (eval MaybeBoolCtx t4) `0
-- #eval! eval MaybeBoolCtx t5
-- def t6 := Option.getD (eval MaybeBoolCtx t5) `0
-- #eval! eval MaybeBoolCtx t6
-- def t7 := Option.getD (eval MaybeBoolCtx t6) `0
-- #eval! eval MaybeBoolCtx t7
-- def t8 := Option.getD (eval MaybeBoolCtx t7) `0
-- #eval! eval MaybeBoolCtx t8
-- def t9 := Option.getD (eval MaybeBoolCtx t8) `0
-- #eval! eval MaybeBoolCtx t9
-- def t10 := Option.getD (eval MaybeBoolCtx t9) `0
-- #eval! eval MaybeBoolCtx t10
-- def t11 := Option.getD (eval MaybeBoolCtx t10) `0
-- #eval! eval MaybeBoolCtx t11
-- def t12 := Option.getD (eval MaybeBoolCtx t11) `0
-- #eval! eval MaybeBoolCtx t12
-- def t13 := Option.getD (eval MaybeBoolCtx t12) `0
-- #eval! eval MaybeBoolCtx t13
-- def t14 := Option.getD (eval MaybeBoolCtx t13) `0
-- #eval! eval MaybeBoolCtx t14
-- def t15 := Option.getD (eval MaybeBoolCtx t14) `0
-- #eval! eval MaybeBoolCtx t15
-- def t16 := Option.getD (eval MaybeBoolCtx t15) `0
-- #eval! eval MaybeBoolCtx t16
-- def t17 := Option.getD (eval MaybeBoolCtx t16) `0
-- #eval! eval MaybeBoolCtx t17
-- def t18 := Option.getD (eval MaybeBoolCtx t17) `0
-- #eval! eval MaybeBoolCtx t18
-- def t19 := Option.getD (eval MaybeBoolCtx t18) `0
-- #eval! eval MaybeBoolCtx t19
-- def t20 := Option.getD (eval MaybeBoolCtx t19) `0
-- #eval! eval MaybeBoolCtx t19
-- def t21 := Option.getD (eval MaybeBoolCtx t20) `0
-- #eval! eval MaybeBoolCtx t20
-- def t22 := Option.getD (eval MaybeBoolCtx t21) `0
-- #eval! eval MaybeBoolCtx t22
-- def t23 := Option.getD (eval MaybeBoolCtx t22) `0
-- #eval! eval MaybeBoolCtx t23
-- def t24 := Option.getD (eval MaybeBoolCtx t23) `0
-- #eval! eval MaybeBoolCtx t24
-- def t25 := Option.getD (eval MaybeBoolCtx t24) `0
-- #eval! eval MaybeBoolCtx t25
-- def t26 := Option.getD (eval MaybeBoolCtx t25) `0
-- #eval! eval MaybeBoolCtx t26
-- def t27 := Option.getD (eval MaybeBoolCtx t26) `0
-- #eval! eval MaybeBoolCtx t27
-- def t28 := Option.getD (eval MaybeBoolCtx t27) `0
-- #eval! eval MaybeBoolCtx t28
-- def t29 := Option.getD (eval MaybeBoolCtx t28) `0
-- #eval! eval MaybeBoolCtx t29
