import Hs.HsTerm
import Hs.Translator.HsCtx
import SystemFD.Algorithm
import SystemFD.Term

-- data Bool = True | False
def BoolF : HsFrame HsTerm :=
   .datatypeDecl `★ [ `#0     -- True
                    , `#1     -- False
                    ]

-- convention True is deeper in the context than False

-- not :: Bool -> Bool
-- not = λ x case x of {True -> False ; _ -> True}
def notF : HsFrame HsTerm :=
  .term (`#2 → `#3) (λ̈[`#2] .HsIte (.HsAnnotate `#3 `#2) (.HsAnnotate `#3 `#0) (.HsAnnotate `#3 `#1) `#2)

/-
eq_bool : Bool -> Bool -> Bool
eq_bool =
  λ x y.
    case y of
      False -> case x of
                  False -> True
                  _     -> False
      _ -> case x of
             True -> True
             _ -> False
-/
def eqBoolF : HsFrame HsTerm :=
  .term (`#3 → `#4 → `#5) (λ̈[`#3] λ̈[`#4] (.HsIte (.HsAnnotate `#5 `#3) (.HsAnnotate `#5 `#0)
                                                 (.HsAnnotate `#5 (.HsIte (.HsAnnotate `#5 `#3)
                                                                          (.HsAnnotate `#5 `#1)
                                                                          (.HsAnnotate `#5 `#4) `#3))
                                                 ((.HsIte (.HsAnnotate `#5 `#4) (.HsAnnotate `#5 `#1)
                                                                          (.HsAnnotate `#5 `#4) `#3))))
-- eq_bool True True --> True
#guard (do
  let Γ <- compile_ctx [eqBoolF, notF, BoolF]
  .toDsMq (eval_ctx_loop Γ (#0 `@ #3 `@ #3))) == .ok #3

-- eq_bool True False --> False
#guard (do
  let Γ <- compile_ctx [eqBoolF, notF, BoolF]
  .toDsMq (eval_ctx_loop Γ (#0 `@ #3 `@ #2))) == .ok #2

-- not true --> False
#guard (do
  let Γ <- compile_ctx [eqBoolF, notF, BoolF]
  .toDsMq (eval_ctx_loop Γ (#1 `@ #3))) == .ok #2

-- not False --> True
#guard (do
  let Γ <- compile_ctx [eqBoolF, notF, BoolF]
  .toDsMq (eval_ctx_loop Γ (#1 `@ #2))) == .ok #3


-- class Eq a where
--   == : a -> a -> Bool
--   /= : a -> a -> Bool
def EqCF : HsFrame HsTerm :=
  .classDecl (`★ `-k> `★)
         .nil
         .nil
         [ `∀{`★} `#0 → `#1 → `#8
         , `∀{`★} `#0 → `#1 → `#9 ]

-- instance Eq Bool where
--   == = eq_bool
--   /= = λ x y. not (eq_bool x y)
def EqBoolI : HsFrame HsTerm :=
  .inst (`#2 `•k `#7)
  [ `#4
  , .HsAnnotate (`#9 → `#10 → `#11) (λ̈[`#9]λ̈[`#10] (`#8 `• (`#7 `• `#0 `• `#1)))
  ]

-- class Eq a => Ord a where
--    (≤) :: a -> a -> Bool
def OrdC : HsFrame HsTerm :=
  HsFrame.classDecl (`★ `-k> `★)
    [ `#7 `•k `#0 ]
    .nil
    [ `∀{`★} (`#0 → `#1 → `#15)
    ]

/-
leq_bool =
  λ x y.
    case y of
       False -> case x of
                  False -> True
                  _     -> False
        _     -> True
-/
def leqBoolF : HsFrame HsTerm :=
  .term (`#13 → `#14 → `#15) (
    λ̈[`#13]λ̈[`#14]
      .HsIte (.HsAnnotate `#15 `#13) (.HsAnnotate `#15 `#0)
        (.HsAnnotate (`#15) (.HsIte (.HsAnnotate `#15 `#13) (.HsAnnotate `#15 `#1) (.HsAnnotate `#15 `#14) `#13))
        (`#14)
  )


-- (leq_bool) False False --> True
#guard (do
  let Γ <- compile_ctx [BoolF, notF, eqBoolF, EqCF, EqBoolI, OrdC, leqBoolF].reverse
  .toDsMq (eval_ctx_loop Γ (#0 `@ #12 `@ #12))) == .ok #13

-- leq_bool True False --> False
#guard (do
  let Γ <- compile_ctx [BoolF, notF, eqBoolF, EqCF, EqBoolI, OrdC, leqBoolF].reverse
  .toDsMq (eval_ctx_loop Γ (#0 `@ #13 `@ #12))) == .ok #12


-- leq_bool False True --> True
#guard (do
  let Γ <- compile_ctx [BoolF, notF, eqBoolF, EqCF, EqBoolI, OrdC, leqBoolF].reverse
  .toDsMq (eval_ctx_loop Γ (#0 `@ #12 `@ #13))) == .ok #13

/-
instance Ord Bool where
  (≤) = leq_bool
-/
def OrdBoolF : HsFrame HsTerm :=
  HsFrame.inst
  (`#3 `•k `#14)
  [ `#2
  ]

def supCtx := OrdBoolF ::
              leqBoolF ::
              OrdC ::
              EqBoolI ::
              EqCF ::
              eqBoolF ::
              notF ::
              BoolF ::
              .nil


-- #eval println! "OrdBool, Ord, EqBool, Bool"
-- #eval supCtx
-- #eval! DsM.run (compile_ctx supCtx)
#guard (do let ctx <- compile_ctx supCtx
           .toDsMq (wf_ctx ctx)) == .ok ()


def ex1 := (`#4 `•t `#17 `• (.HsHole (`#6 `•k `#17))) `• `#15 `• `#16
-- (≤)[Bool] (Ord Bool) False True --> True
#guard (
  do let Γ <- compile_ctx supCtx
     let t' <- compile_term Γ #17 ex1
     .toDsMq (eval_ctx_loop Γ t')
 ) == .ok #16


def ex2 : HsTerm := (`#11 `•t `#17 `• (.HsHole (`#6 `•k `#17))) `• `#16 `• `#16
-- (==)[Bool] (Ord Bool) True True --> True
#guard (
  do let Γ <- compile_ctx supCtx
     let t' <- compile_term Γ #17 ex2
     .toDsMq (eval_ctx_loop Γ t')
 ) == .ok #16



def ex3 : HsTerm := `#10 `•t `#17 `• (.HsHole (`#6 `•k `#17)) `• `#16 `• `#16
-- (/=)[Bool] (Ord Bool) True True --> True
#guard (
  do let Γ <- compile_ctx supCtx
     let t' <- compile_term Γ #17 ex3
     .toDsMq (eval_ctx_loop Γ t')
 ) == .ok #15

-- #eval @DsM.run Term _ (do
--   let Γ <- compile_ctx supCtx
--   (compile Γ #17 ex3)
-- )
