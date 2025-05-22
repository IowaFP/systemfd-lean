
import SystemFD.Term
import SystemFD.Judgment
import SystemFD.Ctx
import SystemFD.Algorithm
import SystemFD.Evaluator

def ctx : Ctx Term := [
     -- not : Bool → Bool → Bool = λ x if x ← True then False else True
    .term (#12 -t> #13)
           (`λ[#12] Term.ite #11 #0 #12 #11),
  --   Λ t u v. λ d1 d2.
  --     If FMM[t][u] ← d1 then Λ a' b'. λ (h1: Maybe a' ~  t) (h2 : Maybe b' ~ u) (e1 : F a' b').
  --     If FMM[t][v] ← d2 then Λ a'' b''. λ (k1: Maybe a'' ~ t) (k2 : Maybe b'' ~ v) (e2 : F a'' b'').
  --     let j : (a' ~ a'') = (h1 ; sym k1).2
  --     let e1' : F a'' b' = e1 ▹ <F> `@c[ j ] `@c[<b'>]
  --       sym h2 ; <Maybe> `@c fdF[a''][b'][b''] e1' e2 ; k2
    .inst #6
      (Λ[★]Λ[★]Λ[★]  `λ[#10 `@k #2 `@k  #1]  `λ[#11 `@k #3 `@k #1]
      Term.guard  (#5 `@t #4 `@t #3) #1
               (Λ[★] Λ[★] `λ[(#10 `@k #1) ~[★]~ #6] `λ[(#11 `@k #1) ~[★]~ #6] `λ[(#16 `@k #3 `@k #2)]
      Term.guard  (#10 `@t #9 `@t #7) #5
              (Λ[★] Λ[★] `λ[(#15 `@k #1) ~[★]~ #11] `λ[(#16 `@k #1) ~[★]~ #10] `λ[(#21 `@k #3 `@k #2)]
                 .letterm (#9 ~[★]~ #4) (snd! ★ (#7 `; sym! #2)) (
                    .letterm (#23 `@k #5 `@k #9) (#6 ▹ (refl! (★ -k> ★ -k> ★) #23 `@c #0 `@c refl! ★ #9))
                      ((sym! #8) `; (refl! (★ -k> ★) #20 `@c (#23 `@t #6 `@t #10 `@t #5 `@ #0 `@ #2)) `; #3)
              )))),
  -- FMM : ∀ a b a' b'. Maybe a' ~ a → Maybe b' ~ b → F a' b' → F a b
  .insttype (∀[★]∀[★]∀[★]∀[★]
                ((#6 `@k #1) ~[★]~ #3) -t> ((#7 `@k #1) ~[★]~ #3) -t> (#12 `@k #3 `@k #2) -t> (#13 `@k #6 `@k #5)),
  .ctor (∀[★] #0 -t> (#3 `@k #1)),  -- Just : ∀ a. a → Maybe a
  .ctor (∀[★] #1 `@k #0), -- Nothing : ∀ a. Maybe a
  .datatype (★ -k> ★),        -- Maybe : ★ → ★
  -- fdf : Λ t u v. λ (d1 : F t u)  (d2 : F t v).
  --       If FIB[t][u] ← d1 then λ (h1: Int ~ t) (h2 : Bool ~ u)
  --       If FIB[t][v] ← d2 then λ (k1: Int ~ t) (k2 : Bool ~ v)
  --          (sym h2) ; k2
  .inst #1 (Λ[★]Λ[★]Λ[★] `λ[#5 `@k #2 `@k  #1]  `λ[#6 `@k #3 `@k #1]
                 (Term.guard (#5 `@t #4 `@t #3) #1 (`λ[#8 ~[★]~ #4] `λ[#12 ~[★]~ #4]
                 Term.guard (#7 `@t #6 `@t #4) #2 (`λ[#10 ~[★]~ #6] `λ[#14 ~[★]~ #5] ((sym! #2) `; #0))))),
  -- FIB : ∀ t u. Int ~ t → Bool ~ u → F t u
  .insttype (∀[★]∀[★] (#4 ~[★]~ #1) -t> (#8 ~[★]~ #1) -t> (#5 `@k #3 `@k #2)),
  -- -- fdF : ∀ t u v. F t u → F t v → u ~ v
  .openm (∀[★]∀[★]∀[★] (#3 `@k #2 `@k #1) -t> (#4 `@k #3 `@k #1) -t> (#3 ~[★]~ #2)),
  .opent (★ -k> ★ -k> ★),   -- F : ★ → ★ → ★
  .datatype ★,   -- Int : ★
  .ctor #1, -- True : Bool
  .ctor #0, -- False : Bool
  .datatype  ★  -- Bool : ★
]

#eval wf_ctx ctx
#guard (wf_ctx ctx == .some ())

 --  (∀[★] (#9 `@k #10 `@k #0) -t> #1 -t> #2)
-- f : ∀ t. F Int t → t → t
--   = Λ t λ (d : F Int t).
--     let h : Bool ~ t = fdF[Int][Bool][t](FIB [Int][Bool] <Int> <Bool>) d in
--     not ▹ <→> `@c h `@c h
def fnot := Λ[★]`λ[#10 `@k #11 `@k #0]
        .letterm ((#15 ~[★]~ #1))
          (#10 `@t #12 `@t #15 `@t #1
               `@ (#9 `@t #12 `@t #15 `@ (refl! ★ #12) `@ (refl! ★ #15))
               `@ #0)
            (#3 ▹ (#0 -c> #1))

#eval infer_type ctx fnot
#guard (infer_type ctx fnot == .some (∀[★] #10 `@k #11 `@k #0 -t> #1 -t> #2))
