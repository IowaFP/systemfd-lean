import Hs.HsTerm
import Hs.Translator.HsCtx
import SystemFD.Algorithm
import SystemFD.Term
import SystemFD.Evaluator

/-
datatype Bool = False | True
-/
def BoolFDT : HsFrame HsTerm :=
   .datatypeDecl `★ [ `#0     -- True
                    , `#1     -- False
                    ]
/-
datatype Maybe a = Nothing | Just a
-/
def MbF : HsFrame HsTerm :=
   .datatypeDecl (`★ `-k> `★) [ (`∀{`★} (`#1 `•k `#0))      -- Nothing :: ∀ a. Maybe a
                              , (`∀{`★} `#0 → `#3 `•k `#1)  -- Just :: ∀ a. a -> Maybe a
                              ]

/-
not : Bool -> Bool
not = λ x. match x with
           True -> False
           _ -> True

-/
def notT : HsFrame HsTerm :=
  .term (`#2 → `#3) (λ̈[`#2] .HsIte (.HsAnnotate `#3 `#2) (.HsAnnotate `#3 `#0) (.HsAnnotate `#3 `#1) `#2)



/-
eqBool : Bool -> Bool -> Bool
eqBool = λ x λ y. case y of
                    False -> match x with
                              False -> True
                              _ -> False
                    _ -> match x with
                              True -> True
                              _ -> False
-/
def eqBoolT : HsFrame HsTerm :=
  .term (`#3 → `#4 → `#5) (λ̈[`#3] λ̈[`#4] (.HsIte (.HsAnnotate `#5 `#3) (.HsAnnotate `#5 `#0)
                                                 (.HsAnnotate `#5 (.HsIte (.HsAnnotate `#5 `#3)
                                                                          (.HsAnnotate `#5 `#1)
                                                                          (.HsAnnotate `#5 `#3) `#4))
                                                 ((.HsIte (.HsAnnotate `#5 `#4) (.HsAnnotate `#5 `#1)
                                                                          (.HsAnnotate `#5 `#3) `#4))))
/-
class Eq a where
  == : a -> a -> Bool
  /= : a -> a -> Bool
-/
def EqC : HsFrame HsTerm :=
  .classDecl (`★ `-k> `★)
         .nil .nil
         [ `∀{`★} `#0 → `#1 → `#8
         , `∀{`★} `#0 → `#1 → `#9 ]


/-
instance Eq Bool where
    == = eqBool
    /= = λ x y. not (eqBool x y)
-/
def EqBoolInst : HsFrame HsTerm :=
  .inst (`#2 `•k `#7)
  [ `#4
  , .HsAnnotate (`#9 → `#10 → `#11) (λ̈[`#9]λ̈[`#10] (`#8 `• (`#7 `• `#0 `• `#1)))
  ]

/-
eqMaybe : ∀ a Eq a => Maybe a → Maybe a → Bool
eqMaybe = Λ (a:★) λ (d : Eq a) λ m1 λ m2 ->
  case m1 of
    Nothing -> case m2 of
                  Nothing -> true
                  _       -> false
    Just x  -> case m2 of
                  Just y -> eq a d x y
                  Nohting -> false
-/

def eqMaybeTy := `∀{`★} (`#9 `•k `#0) ⇒ (`#4 `•k `#1) → (`#5 `•k `#2) → `#17
def eqMaybeT := Λ̈[`★] λ̈[`#9 `•k `#0]
  λ̈[`#4 `•k `#1] λ̈[`#5 `•k `#2]
     .HsIte (.HsAnnotate (`#6 `•k `#3) (`#5 `•t `#3)) (.HsAnnotate (`#6 `•k `#3) `#1)
        (.HsAnnotate `#17 (.HsIte (.HsAnnotate (`#6 `•k `#3) (`#5 `•t `#3)) (.HsAnnotate (`#6 `•k `#3) `#0)
               (.HsAnnotate `#17 `#16)   -- x = Nothing; y = Nothing
               `#15))                    -- x = Nothing; y ≠ Nothing
        (.HsIte (.HsAnnotate (`#3 → `#7 `•k `#4) (`#4 `•t `#3)) (.HsAnnotate (`#6 `•k `#3) `#1)
             (.HsAnnotate (`#3 → `#18) (λ̈[`#3]
                 (.HsIte (.HsAnnotate (`#4 → `#8 `•k `#5) (`#5 `•t `#4)) (.HsAnnotate (`#7 `•k `#4) `#1)
                         (.HsAnnotate (`#4 → `#19) (λ̈[`#4]
                             `#13 `•t `#5 `• `#4 `• `#1 `• `#0
                             ))   --x = Just x';y = Just y'
                         `#17)))  -- x = Just x'; y = Nothing
            `#16)


def eqMaybeF : HsFrame HsTerm := .term eqMaybeTy eqMaybeT

def Γ : HsCtx HsTerm := [
  MbF,
  EqBoolInst,
  EqC,
  eqBoolT,
  notT,
  BoolFDT ]

def Γ1 : HsCtx HsTerm := [
  eqMaybeF,
  MbF,
  EqBoolInst,
  EqC,
  eqBoolT,
  notT,
  BoolFDT ]



#guard (do
  let Γ <- compile_ctx [EqBoolInst, EqC, eqBoolT, notT, BoolFDT]
  let t : HsTerm := (`#4 `•t `#10 `• (.HsHole (`#5 `•k `#10)) `• `#8 `• `#8)
  let t' <- compile Γ #10 t
  .toDsMq (eval_ctx_loop Γ t')) == .ok #8

#guard (do
  let Γ <- compile_ctx [EqBoolInst, EqC, eqBoolT, notT, BoolFDT]
  let t : HsTerm := (`#4 `•t `#10 `• (.HsHole (`#5 `•k `#10)) `• `#8 `• `#9)
  let t' <- compile Γ #10 t
  .toDsMq (eval_ctx_loop Γ t')) == .ok #9

/-
instance Eq a => Eq (Maybe a) where
  == = eqMaybe
  /= = λ x y. not (eqMaybe x y)
-/

def EqMaybeI : HsFrame HsTerm :=
  .inst (`∀{`★} (`#10 `•k `#0) ⇒ (`#11 `•k (`#5 `•k `#1)))
  [
    `#1
    -- Λu λa λb not (eqMaybe[u] __@(Eq u) a b)
  , .HsAnnotate (`∀{`★}(`#12 `•k `#0) ⇒ (`#7 `•k `#1) → (`#8 `•k `#2) → `#20)
               (Λ̈[`★] λ̈[`#12 `•k `#0] λ̈[`#7 `•k `#1]λ̈[`#8 `•k `#2]
                       `#17 `• (`#6 `•t `#3 `• `#2  `• `#1 `• `#0))
  ]


def Γ2 : HsCtx HsTerm := [
  -- EqMaybeI,
  eqMaybeF,
  MbF,
  EqBoolInst,
  EqC,
  eqBoolT,
  notT,
  BoolFDT ]


#eval DsM.run (compile_ctx Γ2)

#guard (do let Γ2 <- compile_ctx Γ2
           .toDsMq (wf_ctx Γ2)
       ) == .ok ()
