
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def ctx : Ctx Term := [
    -- f : ∀ t. F Int t → t → t
    --   = Λ t λd.
    --     let h = fdF[Int][Bool][t](FIB [Int][Bool] <Int> <Bool>) d in
    --     not ▹ <→> `@c h `@c h
    -- .term (∀[★] (#9 `@k #10 `@k #0) -t> #1 -t> #2)
    --   (Λ[★]`λ[#8 `@k #9 `@k #0]
    --     Term.letterm ((#15 ~ #1)) (#10 `@t #12 `@t #15 `@t  #1 `@ (#9 `@t #12 `@t #15 `@t #1) `@ #0) (
    --     #3 ▹ (#0 -c> #1))),

     -- not : Bool → Bool → Bool
     --     = λ x if x ← True then False else True
    -- .term (#12 -t> #13)
    --        (`λ[#12] Term.ite #11 #0 #12 #11),

  --   Λ t u v. λ d1 d2.
  --     If FMM[t][u] ← d1 then Λ a' b'. λ (h1: Maybe a' ~  t) (h2 : Maybe b' ~ u) (e1 : F a' b').
  --     If FMM[t][v] ← d2 then Λ a'' b''. λ (k1: Maybe a'' ~ t) (k2 : Maybe b'' ~ v) (e2 : F a'' b'').
  --     let j : (a' ~ a'') = (h1 ; sym k1).2 in
  --     let e1' : F a'' b' = e1 ▹ <F> `@c j `@c <b'> in
  --       sym h2 ; <Maybe> `@c fdF[a''][b'][b''] e1' e2 ; k2
    .inst #6
      (Λ[★]Λ[★]Λ[★]  `λ[#10 `@k #2 `@k  #1]  `λ[#11 `@k #3 `@k #1]
      Term.guard  (#5 `@t #4 `@t #3) #1
               (Λ[★] Λ[★] `λ[(#10 `@k #1) ~ #6] `λ[(#11 `@k #1) ~ #6] `λ[(#16 `@k #3 `@k #2)]
      Term.guard  (#10 `@t #9 `@t #7) #5
              (Λ[★] Λ[★] `λ[(#15 `@k #1) ~ #11] `λ[(#16 `@k #1) ~ #10] `λ[(#21 `@k #3 `@k #2)]
                 .letterm (#9 ~ #4) ((#7 `; sym! #2).!2) (
                    .letterm (#23 `@k #5 `@k #9) (#6 ▹ (refl! #23 `@c #0 `@c refl! #9)) (
                      .letterm (#15 ~ #14) ((sym! #8) `; (refl! #20 `@c (#23 `@t #6 `@t #10 `@t #5 `@ #0 `@ #2)) `; #3)
                        #0
                )
              )))),

  -- FMM : ∀ a b a' b'. Maybe a' ~ a → Maybe b' ~ b → F a' b' → F a b
  .insttype (∀[★]∀[★]∀[★]∀[★]
                (#6 `@k #1 ~ #3) -t> (#7 `@k #1 ~ #3) -t> (#12 `@k #3 `@k #2) -t> (#13 `@k #6 `@k #5)),
  .ctor (∀[★] #0 -t> (#3 `@k #1)),  -- Just : ∀ a. a → Maybe a
  .ctor (∀[★] #1 `@k #0), -- Nothing : ∀ a. Maybe a
  .datatype (★ -k> ★),        -- Maybe : ★ → ★
  -- fdf : Λ t u v. λ (d1 : F t u)  (d2 : F t v).
  --       If FIB[t][u] ← d1 then λ (h1: Int ~ t) (h2 : Bool ~ u)
  --       If FIB[t][v] ← d2 then λ (k1: Int ~ t) (k2 : Bool ~ v)
  --          (sym h2) ; k2
  .inst #1 (Λ[★]Λ[★]Λ[★] `λ[#5 `@k #2 `@k  #1]  `λ[#6 `@k #3 `@k #1]
                 (Term.guard (#5 `@t #4 `@t #3) #1 (`λ[#8 ~ #4] `λ[#12 ~ #4]
                 Term.guard (#7 `@t #6 `@t #4) #2 (`λ[#10 ~ #6] `λ[#14 ~ #5] ((sym! #2) `; #0))))),
  -- FIB : ∀ t u. Int ~ t → Bool ~ u → F t u
  .insttype (∀[★]∀[★] (#4 ~ #1) -t> (#8 ~ #1) -t> (#5 `@k #3 `@k #2)),
  -- -- fdF : ∀ t u v. F t u → F t v → u ~ v
  .openm (∀[★]∀[★]∀[★] (#3 `@k #2 `@k #1) -t> (#4 `@k #3 `@k #1) -t> (#3 ~ #2)),
  .opent (★ -k> ★ -k> ★),   -- F : ★ → ★ → ★
  .datatype ★,   -- Int : ★
  .ctor #1, -- True : Bool
  .ctor #0, -- False : Bool
  .datatype  ★  -- Bool : ★
]

#eval wf_ctx ctx

  --   Λ t u v. λ (d1: F t u) (d2 : F t v).
  --     If FMM[t][u] ← d1 then Λ a' b'. λ (h1: Maybe a' ~  t) (h2 : Maybe b' ~ u) (e1 : F a' b').
  --     If FMM[t][v] ← d2 then Λ a'' b''. λ (k1: Maybe a'' ~ t) (k2 : Maybe b'' ~ v) (e2 : F a'' b'').
  --       sym h2 ; <Maybe> `@c fdF[a''][b'][b''] (e1 ▹ <F> `@c[ (h1 ; sym k1).2] `@c[b']) e2 ; k2

-- def ctx2 := ([.type (#11 `@k #3 `@k #1), .type (#10 `@k #2 `@k  #1), .kind ★, .kind ★, .kind ★] ++ ctx)
-- def ctx3 := ([.type (#16 `@k #3 `@k #2), .type ((#11 `@k #1) ~ #6), .type ((#10 `@k #1) ~ #6), .kind ★, .kind ★] ++ ctx2)
-- def ctx4 := ([.type (#21 `@k #3 `@k #2), .type ((#16 `@k #1) ~ #10), .type ((#15 `@k #1) ~ #11), .kind ★, .kind ★] ++ ctx3)
-- def ctx5 := ([.term (#23 `@k #5 `@k #9) (#6 ▹ (refl! #23 `@c #0 `@c refl! #9)), .term (#9 ~ #4) ((#7 `; sym! #2).!2)] ++ ctx4)
-- def t :=  (Λ[★]Λ[★]Λ[★]  `λ[#10 `@k #2 `@k  #1]  `λ[#11 `@k #3 `@k #1]
--       Term.guard  (#5 `@t #4 `@t #3) #1
--                (Λ[★] Λ[★] `λ[(#10 `@k #1) ~ #6] `λ[(#11 `@k #1) ~ #6] `λ[(#16 `@k #3 `@k #2)]
--       Term.guard  (#10 `@t #9 `@t #7) #5
--               (Λ[★] Λ[★] `λ[(#15 `@k #1) ~ #11] `λ[(#16 `@k #1) ~ #10] `λ[(#21 `@k #3 `@k #2)]
--                  .letterm (#9 ~ #4) ((#7 `; sym! #2).!2) (
--                     .letterm (#23 `@k #5 `@k #9) (#6 ▹ (refl! #23 `@c #0 `@c refl! #9)) (
--                       .letterm (#15 ~ #14) ((sym! #8) `; (refl! #20 `@c (#23 `@t #6 `@t #10 `@t #5 `@ #0 `@ #2)) `; #3)
--                       #0
--                 )
--               ))))
-- #eval infer_type ctx t


-- #eval
--   infer_type (.term (#9 ~ #4) ((#7 `; sym! #2).!2) :: ctx4) (#6 ▹ (refl! #23 `@c #0 `@c refl! #9))

-- #eval infer_type ctx5 (sym! #8)
-- #eval
--   infer_type ctx5 (refl! #20 `@c (#23 `@t #6 `@t #10 `@t #5 `@ #0 `@ #2))
-- #eval infer_type ctx5 #3

-- #eval
--   infer_type ctx5
--     ((sym! #8) `; ((refl! #20 `@c (#23 `@t #6 `@t #10 `@t #5 `@ #0 `@ #2)) `; #3))


-- #eval infer_kind ctx4 (#9 ~ #4)
-- #eval infer_type ctx4 ((#7 `; sym! #2).!2)




-- #eval
--   infer_type ctx3 (#10 `@t #9 `@t #7)
-- #eval infer_type ctx3 #5
-- #eval [P' 5]((#22 `@ #14) `@ #12)
-- #eval
--   infer_type ctx3 (Λ[★] Λ[★] `λ[(#15 `@k #1) ~ #11] `λ[(#16 `@k #1) ~ #10] `λ[(#21 `@k #3 `@k #2)] #24)




-- #eval infer_type ctx2 ((#5 `@t #4 `@t #3))
-- #eval [P' 5](((#17 `@ #9) `@ #8))
-- #eval infer_type ctx2 #1
-- #eval infer_type
--   ctx2 (Λ[★] Λ[★] `λ[(#10 `@k #1) ~ #6] `λ[(#11 `@k #1) ~ #6] `λ[(#16 `@k #3 `@k #2)] #0)


-- #eval eval_ctx_loop ctx
--     (t
--         `@t (#3 `@k #8)  -- Maybe Int
--         `@t (#3 `@k #11)  -- Maybe Bool
--         `@t (#3 `@k #11)  -- Maybe Bool
--         -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
--         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #11))
--              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
--        -- -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
--         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #11))
--              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
--         )
-- -- ∀[★](∀[★]((#10 @ #1) ∼ #6 → (#11 @ #1) ∼ #6 → ((#16 @ #3) @ #2) → ((#17 @ #9) @ #8)))
-- -- ((#12 @ #4) @ #3)

-- def unwrap : Option Term -> Term
-- | x => Option.getD x .kind


--   -- let A <- infer_type Γ p
--   def A := unwrap (infer_type ctx2 (#5 `@t #4 `@t #3))
--   #eval A
--   -- let R <- infer_type Γ s
--   def R := unwrap (infer_type ctx2 #1)
--   #eval R
--   -- let Rk <- infer_kind Γ R
--   -- let _ <- wf_kind Rk
--   -- let _ <- stable_type_match Γ A R
--   #eval stable_type_match ctx2 A R
--   -- let (ph, _) <- Term.neutral_form p
--   def ph := Option.getD (Term.neutral_form ((#5 `@t #4 `@t #3))) (0, [])
--   #eval ph
--   -- let (rh, _) <- Term.neutral_form R
--   def rh := Option.getD (Term.neutral_form R) (0, [])
--   #eval rh
--   -- let insttype_headed := Γ.is_insttype ph
--   #eval Ctx.is_insttype ctx2 ph.1
--   -- let ot_headed := Γ.is_opent rh
--   #eval Ctx.is_opent ctx2 rh.1
--   -- let B <- infer_type Γ t
--   def t' := Λ[★] Λ[★] `λ[(#10 `@k #1) ~ #6] `λ[(#11 `@k #1) ~ #6] `λ[#16 `@k #3 `@k #2] #19
--   def B := unwrap (infer_type ctx2 t')
--   #eval B
--   -- let T <- prefix_type_match Γ A B
--   #eval prefix_type_match ctx2 A B
--   -- let Tk <- infer_kind Γ T
--   -- let _ <- wf_kind Tk
--   -- if (insttype_headed && ot_headed)
--   --   then .some T
--   --   else .none


-- -- def prefix_type_match (Γ : Ctx Term) (A B : Term) : Option Term := do
-- --   let (τ, sR) := Term.to_telescope A
-- def τ := (Term.to_telescope A).fst
-- def sR := (Term.to_telescope A).snd
-- #eval (τ, sR)
-- --   let (τ', sT) := Term.to_telescope B
-- def τ' := (Term.to_telescope B).fst
-- def sT := (Term.to_telescope B).snd
-- #eval (τ', sT)
-- --   let ξ <- prefix_equal τ τ'
-- def ξ := prefix_equal τ τ'
-- #eval ξ
-- --   let T := [P' τ.length](Term.from_telescope ξ sT)
-- def T := [P' τ.length](Term.from_telescope [] sT)
-- #eval T
-- --   let R := [P' τ.length]sR
-- def R' := [P' τ.length]sR
-- #eval R'
-- --   let (x, _) <- Term.neutral_form R
-- --   if [S' τ.length]T == Term.from_telescope ξ sT
-- --     && [S' τ.length]R == sR
-- --     && (Γ d@ x).is_stable
-- --   then .some T
-- --   else .none

-- #eval Term.to_telescope (Option.getD (infer_type ctx2 (#5 `@t #4 `@t #3)) .kind)
-- #eval ([P' 5]((#17 `@ #9) `@ #8))

-- -- def t := (
-- --     -- Term.guard  (#5 `@t #4 `@t #3) #1 (Λ[★] Λ[★] `λ[(#10 `@k #1) ~ #6] `λ[(#11 `@k #1) ~ #6] `λ[#16 `@k #3 `@k #2]
-- --             #1
-- --       -- Term.guard  (#10 `@t #9 `@t #8) #5
-- --       --          (Λ[★] Λ[★] `λ[(#14 `@k #1) ~ #11] `λ[(#15 `@k #1) ~ #10] `λ[(#20 `@k #3 `@k #2)]
-- --       --            ((sym! #6) `; (((refl!(∀[★](#19 `@k #0)))
-- --       --                    `@c[#21 `@t #4 `@t #8 `@t #3 `@
-- --       --                (#5 ▹ ((refl!(∀[★] ∀[★] (#24 `@k #1 `@k #0))) `@c[(#7 `; sym! #2).!2] `@c[refl! #8])) `@ #0]) `;
-- --       --         #1))
-- --       --       )
-- --             )

-- -- #eval infer_type ([.type (#11 `@k #3 `@k #2), .type (#10 `@k #2 `@k  #1), .kind ★, .kind ★, .kind ★] ++ ctx) t




-- -- def t := Λ[★]Λ[★]Λ[★]  `λ[#11 `@k #2 `@k  #1]  `λ[#12 `@k #3 `@k #1]
-- --       Term.guard (#6 `@t #4 `@t #3) #1
-- --                (Λ[★] Λ[★] `λ[(#11 `@k #1) ~ #6] `λ[(#12 `@k #1) ~ #6] `λ[(#17 `@k #3 `@k #2)]
-- --       Term.guard  (#11 `@t #9 `@t #7) #5
-- --                (Λ[★] Λ[★] `λ[(#16 `@k #1) ~ #11] `λ[(#17 `@k #1) ~ #10] `λ[(#22 `@k #3 `@k #2)]
-- --                (#25)
-- --         -- Term.letterm (#23 `@k #5 `@k #9) (#6 ▹ ((refl!(∀[★] ∀[★] (#25 `@k #1 `@k #0))) `@c[#0]  `@c[refl! #4])) (
-- --         --     ((sym! #8) `; ((refl!(∀[★](#21 `@k #0))) `@c[#23 `@t #6 `@t #10 `@t #5 `@ #0 `@ #2]) `; #3)
-- --         --        )
-- --         --       )
-- --                 )
-- --                )

-- -- #eval infer_type ctx t
-- -- #eval eval_ctx_loop ctx
-- --     (t
-- --         `@t (#3 `@k #8)  -- Maybe Int
-- --         `@t (#3 `@k #11)  -- Maybe Bool
-- --         `@t (#3 `@k #11)  -- Maybe Bool
-- --         -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
-- --         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #11))
-- --              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
-- --        -- -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
-- --         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #11))
-- --              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
-- --         )



--   -- fdf : Λ t u v. λ (d1:F t u) (d2:F t v).
--   --       If FIB[t][u] ← d1 then λ (h1:Int ~ t) (h2:Bool ~ u)
--   --       If FIB[t][v] ← d2 then λ (k1:Int ~ t) (k2:Bool ~ v)
--   --          (sym h2) ; k2
-- -- #eval infer_type ctx ((Λ[★]Λ[★]Λ[★] `λ[#5 `@k #2 `@k  #1]  `λ[#6 `@k #3 `@k #1]
-- --                      `λ[#8 ~ #4] `λ[#11 ~ #4] (#7 `@t #6 `@t #4)))

-- -- #eval! eval_ctx_loop ctx ((Λ[★]Λ[★]Λ[★] `λ[#5 `@k #2 `@k  #1]  `λ[#6 `@k #3 `@k #1]
-- --                  (Term.guard (#5 `@t #4 `@t #3) #1 (`λ[#8 ~ #4] `λ[#12 ~ #4]
-- --                  Term.guard (#7 `@t #6 `@t #4) #2 (`λ[#10 ~ #6] `λ[#14 ~ #5] ((sym! #2) `; (#0))))))
-- --                  `@t #3 `@t #6 `@t #6
-- --                  `@ (#0 `@t #3 `@t #6 `@ refl! #3 `@ refl! #6)
-- --                  `@ (#0 `@t #3 `@t #6 `@ refl! #3 `@ refl! #6)
-- --                   )

-- -- #eval infer_type ctx (#0 `@t #14 `@ (#8 `@t #9 `@t #11 `@ (refl! #6) `@ (refl! #9)) `@ #12) -- #14

-- -- #eval ctx.length -- 15
-- -- #eval (get_instances ctx 9).length -- 2

-- -- #eval! eval_ctx_loop ctx (#0 `@t #14 `@ (#8 `@t #9 `@t #11 `@ (refl! #6) `@ (refl! #9)) `@ #12) -- #13
-- -- #eval! eval_ctx_loop ctx (#0 `@t #14 `@ (#8 `@t #9 `@t #11 `@ (refl! #6) `@ (refl! #9)) `@ #13) -- #12

-- -- #eval! eval_ctx_loop ctx (#1 `@ #12) -- #13
-- -- #eval! eval_ctx_loop ctx (#1 `@ #13) -- #12

-- -- def h1 := Option.getD (eval_inst ctx (t
-- --         `@t (#3 `@k #8)  -- Maybe Int
-- --         `@t (#3 `@k #11)  -- Maybe Bool
-- --         `@t (#3 `@k #11)  -- Maybe Bool
-- --         -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
-- --         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #8))
-- --              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
-- --        -- -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
-- --         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #8))
-- --              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
-- --        )) []

-- -- def h1 := Option.getD (eval_outer ctx ([t
-- --         `@t (#3 `@k #8)  -- Maybe Int
-- --         `@t (#3 `@k #11)  -- Maybe Bool
-- --         `@t (#3 `@k #11)  -- Maybe Bool
-- --         -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
-- --         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #11))
-- --              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
-- --        -- -- FMM[Maybe Int][Maybe Bool][Int][Bool] <Maybe Int>  <Maybe Bool> (FIB[Int][Bool] <Int> <Bool>)
-- --         `@ (#0 `@t (#3 `@k #8) `@t (#3 `@k #11) `@t #8 `@t #11 `@ (refl! (#3 `@k #8)) `@ (refl! (#3 `@k #11))
-- --              `@ (#5 `@t #8 `@t #11 `@ (refl! #8) `@ (refl! #11)))
-- --        ])) []

-- -- #eval! eval_outer ctx h1
-- -- def h2 := Option.getD (eval_outer ctx h1) []
-- -- #eval! eval_outer ctx h2
-- -- def h3 := Option.getD (eval_outer ctx h2) []
-- -- #eval! eval_outer ctx h3
-- -- def h4 := Option.getD (eval_outer ctx h3) []
-- -- #eval! eval_outer ctx h4
-- -- def h5 := Option.getD (eval_outer ctx h4) []
-- -- #eval! eval_outer ctx h5
-- -- def h6 := Option.getD (eval_outer ctx h5) []
-- -- #eval! eval_outer ctx h6
-- -- def h7 := Option.getD (eval_outer ctx h6) []
-- -- #eval! eval_outer ctx h7
-- -- def h8 := Option.getD (eval_outer ctx h7) []
-- -- #eval! eval_outer ctx h8
-- -- def h9 := Option.getD (eval_outer ctx h8) []
-- -- #eval! eval_outer ctx h9
-- -- def h10 := Option.getD (eval_outer ctx h9) []
-- -- #eval! eval_outer ctx h10
-- -- def h20 := Option.getD (eval_outer ctx h10) []
-- -- #eval! eval_outer ctx h20
-- -- def h21 := Option.getD (eval_outer ctx h20) []
-- -- #eval! eval_outer ctx h21
-- -- def h22 := Option.getD (eval_outer ctx h21) []
-- -- #eval! eval_outer ctx h22
-- -- def h23 := Option.getD (eval_outer ctx h22) []
-- -- #eval! eval_outer ctx h23
-- -- def h24 := Option.getD (eval_outer ctx h23) []
-- -- #eval! eval_outer ctx h24
-- -- def h25 := Option.getD (eval_outer ctx h24) []
-- -- #eval! eval_outer ctx h25
-- -- def h26 := Option.getD (eval_outer ctx h25) []
-- -- #eval! eval_outer ctx h26
-- -- def h27 := Option.getD (eval_outer ctx h26) []
-- -- #eval! eval_outer ctx h27
-- -- def h28 := Option.getD (eval_outer ctx h27[0]) []
-- -- #eval! eval_outer ctx h28[0]
-- -- def h29 := Option.getD (eval_outer ctx h28[0]) []
-- -- #eval! eval_outer ctx h29[0]
-- -- def h30 := Option.getD (eval_outer ctx h29[0]) []
-- -- #eval! eval_outer ctx h30[0]
-- -- def h31 := Option.getD (eval_outer ctx h30[0]) []
-- -- #eval! eval_outer ctx h31[0]
-- -- def h32 := Option.getD (eval_outer ctx h31[0]) []
-- -- #eval! eval_outer ctx h32[0]
-- -- def h33 := Option.getD (eval_outer ctx h32[0]) []
-- -- #eval! eval_inst ctx h33[0]
-- -- def h34 := Option.getD (eval_inst ctx h33[0]) []
-- -- #eval! eval_inst ctx h34[0]
-- -- def h35 := Option.getD (eval_inst ctx h34[0]) []
-- -- #eval! eval_inst ctx h35[0]
-- -- def h36 := Option.getD (eval_inst ctx h35[0]) []
-- -- #eval! eval_inst ctx h36[0]
