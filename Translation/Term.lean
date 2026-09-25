import Core.Ty
import Core.Term
import Core.Infer
-- import Surface.Ty
import Surface.Term
import Core.Typing
import Core.Synth

import Core.Util

import Translation.Ty
open LeanSubst
open Lilac


@[simp] abbrev TM α := Except Std.Format α

def List.tryM {α : Type w} {β : Type u} (f : α → TM β) (as : List α) : TM (List β) :=
  let rec @[specialize] loop
    | [], bs => pure bs.reverse
    | .cons a as, bs => do
      match f a with
      | .error _ => loop as bs
      | .ok a => loop as (a :: bs)
  loop as []

namespace Translation

namespace Option
def toTM (e : Std.Format) : Option α -> Except Std.Format α
| none => Except.error e
| some e => Except.pure e
end Option



theorem Except.bind_eq_ok_iff {α : Type u_1} {β : Type u_2} {ε : Type u_3} {b : β} {x : Except ε α} {f : α → Except ε β} :
  x.bind f = .ok b ↔ ∃ (a : α), x = .ok a ∧ f a = .ok b
:= by
  apply Iff.intro
  all_goals (intro h; cases x <;> simp [Except.bind] at *; apply h)

theorem Except.map_eq_ok_iff {α : Type u_1} {β : Type u_2} {ε : Type u_3} {b : β} {x : Except ε α}  {f : α → β} :
  x.map f = .ok b ↔ ∃ (a : α), x = .ok a ∧ f a = b := by
  apply Iff.intro
  intro h; simp [Except.map] at *; split at h <;> (try simp at *); apply h
  intro h; simp [Except.map]; split <;>  (try simp at *); apply h

@[simp]
theorem Except.ite_true_eq_ok_iff {α : Type u_1} {t : TM α} {t' : α} {b : Bool} {e : Std.Format}:
  ((if b then t else Except.error e) = Except.ok t') <->
  t = .ok t' ∧ b = True
:= by
  apply Iff.intro
  intro h; split at h <;> simp at h
  case _ b => apply And.intro; apply h; simp; apply b
  intro h; rcases h with ⟨h1, h2⟩; subst h1; simp at h2; subst h2; simp

@[simp]
theorem Except.ite_false_eq_ok_iff {α : Type u_1} {t : TM α} {t' : α} {b : Bool} {e : Std.Format}:
  ((if b then Except.error e else t) = Except.ok t') <->
  t = .ok t' ∧ b = False
:= by
  apply Iff.intro
  intro h; split at h <;> try simp at h
  case _ b => apply And.intro; apply h; simp at b; simp; apply b
  intro h; rcases h with ⟨h1, h2⟩; subst h1; simp at h2; subst h2; simp

theorem Option.toTM_some_eq_ok_iff :
  Option.toTM s c = Except.ok e <-> c = some e
:= by
  apply Iff.intro;
  intro h; simp [Option.toTM] at h; split at h <;> simp at *
  cases h; rfl
  intro h; subst h; simp [Option.toTM, Except.pure]


def Core.Ty.synth_coercion (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv)
  (T1 : Core.Ty) (T2 : Core.Ty) : Option Core.Term :=
  match T1.infer_kind G Δ, T2.infer_kind G Δ with
  | some K1, some K2 =>
    if h : K1 == K2 then
    by simp at h; subst h; apply Core.Synth.synth_coercion_term G Δ Γ (T1 ~[K1]~ T2)
    else none
  | _, _ => none


-- should satisfy the property if Core.Ty.ty_match n τ1 τ2 = some σ -> τ1[σ] = τ2
-- all variables above n are untouchables
def Core.Ty.ty_match (n : Nat) : (τ1 τ2 : Core.Ty) -> Option (Subst Core.Ty)  -- τ1 is the template, τ2 is the "ground" term
| t#v, τ =>
  if v < n then
  return ⟨λ x => if x == v then .su τ else .su t#v⟩
  else Subst.id Core.Ty
| gt#x, gt#y => if x == y then return Subst.id Core.Ty else none
| (A -:> B), (A' -:> B')
| (.app A B), (.app A' B') => do
  let σ1 <- Core.Ty.ty_match n A A'
  let σ2 <- Core.Ty.ty_match n B B'
  return (σ1 ∘ σ2)
| .eq K A B, .eq K' A' B' => do
  if K == K' then
  let σ1 <- Core.Ty.ty_match n A A'
  let σ2 <- Core.Ty.ty_match n B B'
  return (σ1 ∘ σ2)
  else none
| _, _ => none



#eval do
  let σ <- Core.Ty.ty_match 0 (gt#"Eq" • t#0) (gt#"Eq" • gt#"Bool")
  return (t#0)[σ]


def find_matching_insts (τ : Core.Ty) : Core.GlobalEnv -> List String
| [] => [] -- TODO: also do for openm
| .cons (.octor x ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩) tl  =>
  let is := find_matching_insts τ tl
  if (Core.Ty.ty_match nb R τ).isSome then x :: is
  else is
| .cons _ tl => find_matching_insts τ tl

def check_class_type (G : Core.GlobalEnv) (τ : Core.Ty) : Bool :=
  match τ.spine with
  | some (x, _) => Core.is_data .opn G x
  | _ => false

def is_eq_type (τ : Core.Ty) : Bool :=
  match τ with
  | .eq _ _ _ => true
  | _ => false

def check_synth_type (G : Core.GlobalEnv) (τ : Core.Ty) : Option Unit :=
  if check_class_type G τ || is_eq_type τ then return () else none


partial def Core.Ty.synth_term' (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) (τ : Core.Ty) :
  TM ((t : Core.Term) ×' (τ' : Core.Ty) ×' (G&Δ, Γ ⊢ t : τ')) := do
  Option.toTM "synth_term' check_synth type" $ check_synth_type G τ
  match h : Γ.findIdx? (· == τ) with
  | some i =>
    match h1 : τ.infer_kind G Δ with
    | some ★ =>
      return ⟨#i, τ,
        by simp [List.findIdx?_eq_some_iff_getElem] at h;
           apply Core.Typing.var;
           · grind;
           · apply Core.infer_kind_sound h1⟩
    | _ => .error $ "synth_term'" ++ τ.repr max_prec ++ "is not kind ★"
  | none =>
    match h : Core.Synth.synth_coercion_term G Δ Γ τ with
    | some t =>
      return ⟨t, τ, by replace h := Core.Synth.synth_coercion_term_sound h; apply h⟩
    | none =>
      let candidates := find_matching_insts τ G
      let ts : List ((t : Core.Term) ×' ((τ' : Core.Ty) ×' (G&Δ, Γ ⊢ t : τ'))) <- candidates.tryM (λ x =>
        match lk : Core.lookup_spine_type (.data .opn) G x with -- TODO: Do the same with Core.lookup_spine_type (.openm)?
        | some ⟨na, Ks1, 0, Ks2, nc, Ts, R⟩ => do
          let (cls, tys) <- Option.toTM "synth_term' τ.spine" $ τ.spine
          let tys' := Vec.from_list tys
          if e : na == tys'.1 then
            let σ := (tys.reverse.map su ++ Subst.id Core.Ty)
            let R' := R[σ]
            let tys'' := tys'.2.map (Core.Ty.infer_kind G Δ ·)
            let Ks1' <- Option.toTM "synth_term' infer tys kinds" $ tys''.sequence
            if h : τ == R' && Vec.beq Ks1' Ks1 && tys''.sequence.isEqSome (Ks1')
                   && (List.range tys'.1).all ((R.fv ·)) && Core.lookup_ctor? G Core.DataConst.opn x R
              then
                let Ts' := Ts[σ]
                let ts' := Ts'.map (Core.Ty.synth_term' G Δ Γ ·)
                let ts <- ts'.sequence
                if h : (ts.map (λ x => x.2.1) == Ts') then
                  let targs := ts.map (·.fst)

                  return ⟨inst! x tys'.2 #() targs.to, R', by
                    simp at e; subst e; simp at h; rcases h with ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩;
                    simp at h;

                    apply Core.Typing.spctor (R' := R') (Ts' := Ts') (Ts := Ts)
                    · apply lk
                    · simp [Ts', σ]; congr; simp [tys']; grind
                    · simp [R', σ]; congr; simp [tys']; grind
                    · intro i; simp [tys']; simp [Vec.beq_iff_eq] at e2; subst e2;
                      simp [tys''] at e3; replace e3 := Vec.traverse_eq_pure_iff_getElem_Option e3 i;
                      replace e3 := Core.infer_kind_sound e3; simp [tys'] at e3;
                      apply e3;
                    · intro i; apply i.elim0
                    · intro i; simp [targs, <-h]; simp [Vec.to_get_elem]; apply ts[i].2.2
                    · simp; apply e5
                    · simp; intro i hi; simp [Core.Ty.FV.reflection]; apply e4 i hi;
                    · simp; ⟩
                else .error "synth_term' kind checks"
              else .error "synth_term' lookup_spine_type tys na"
          else .error "synth_term' n tys"
        | some ⟨na, Ks1, nb, Ks2, nc, Ts, R⟩ => do
          let (cls, tys) <- Option.toTM "synth_term' τ.spine" $ τ.spine -- τ = C τs
          let ⟨na' , tys'⟩ := Vec.from_list tys
          if e : na == na' then
            let σ : Subst Core.Ty := (((List.range nb).map (t#·)).reverse.map su)  ++ tys.reverse.map su ++ Subst.id Core.Ty
            let R' := R[σ]
            let tys'' := tys'.map (Core.Ty.infer_kind G Δ ·)
            let Ks1' <- Option.toTM "synth_term' infer tys kinds" $ tys''.sequence
            if h : τ == R' && Ks1'.beq Ks1 && tys''.sequence.isEqSome (Ks1')
                   && ((List.range na').map (·+ nb)).all ((R.fv ·)) && Core.lookup_ctor? G Core.DataConst.opn x R
              then
                let Ts' := Ts[σ]
                let σsE := Ts'.map (λ τ => match τ with
                  | .eq K τ τ' => Option.toTM ("synth_term' fail match: " ++ τ.repr max_prec ++ " " ++ τ'.repr max_prec ++ Std.Format.line
                                   ++  Ts'.repr max_prec)
                                  $ Core.Ty.ty_match nb τ' τ
                  | _ => return (Subst.id Core.Ty))
                let σsE' : Vec (Subst Core.Ty) nc <- σsE.sequence
                let σsE': Subst Core.Ty := σsE'.foldr (init := Subst.id Core.Ty) (λ σ acc => Subst.compose acc σ)
                let Ts' : Vec Core.Ty nc := Ts'[σsE']
                let ts' := Ts'.map (Core.Ty.synth_term' G Δ Γ ·)
                let ts <- ts'.sequence
                if h : (ts.map (λ x => x.2.1) == Ts') then
                  let targs := ts.map (·.fst)

                  return ⟨inst! x tys' ((Vec.range nb).map (t#·))[σsE'] targs.to, R', by
                    simp at e; subst e; simp at h; rcases h with ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩;
                    simp at h;

                    -- apply Core.Typing.spctor (R' := R') (Ts' := Ts') (Ts := Ts)
                    · sorry
                    -- · apply lk
                    -- · simp [Ts', σ]; congr; simp [tys']; grind
                    -- · simp [R', σ]; congr; simp [tys']; grind
                    -- · intro i; simp [tys']; simp [Vec.beq_iff_eq] at e2; subst e2;
                    --   simp [tys''] at e3; replace e3 := Vec.traverse_eq_pure_iff_getElem_Option e3 i;
                    --   replace e3 := Core.infer_kind_sound e3; simp [tys'] at e3;
                    --   apply e3;
                    -- · intro i; apply i.elim0
                    -- · intro i; simp [targs, <-h]; simp [Vec.to_get_elem]; apply ts[i].2.2
                    -- · simp; apply e5
                    -- · simp; intro i hi; simp [Core.Ty.FV.reflection]; apply e4 i hi;
                    ⟩
                else .error "synth_term' kind checks"
              else .error ("synth_term' lookup_spine_type " ++ Std.Format.line
                          ++ "(cls, tys) :"  ++ cls ++ " " ++ tys.repr max_prec ++ Std.Format.line
                          ++ "τ = R': " ++ τ.repr max_prec ++ " =?= "++ R'.repr max_prec ++ Std.Format.line
                          ++ "Ks1' = Ks1: "  ++ Ks1'.repr max_prec ++ " =?= "++ Ks1.repr max_prec ++ Std.Format.line
                          ++ "tys'' = Ks1: " ++ tys''.sequence.repr max_prec ++ " =?= "++ Ks1.repr max_prec ++ Std.Format.line
                          ++ "fvs: " ++ R.repr max_prec ++ " " ++ (((List.range na').map (· + nb)).all ((R.fv ·))).repr max_prec ++ Std.Format.line
                          ++ "R head: " ++ (Core.lookup_ctor? G Core.DataConst.opn x R).repr max_prec
                          )

          else .error "synth_term' n tys"
        | _ => .error "synth_term' coercion term")
        match ts.head? with
        | some t => return t
        | none => .error $ "synth_term' no instances found for: " ++ τ.repr max_prec ++ "tried candidates: " ++ Std.Format.line ++ candidates.repr max_prec


def Core.Ty.synth_term (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) (τ : Core.Ty)
  : TM ((t : Core.Term) ×' (G&Δ, Γ ⊢ t : τ)) := do
  let ⟨t, τ', j⟩ <- Core.Ty.synth_term' G Δ Γ τ
  if h : τ == τ' then
  return by simp at h; subst h; constructor; apply j;
  else .error "synth_term τ≠τ'"


-- inductive SynthTermIdx : Type where | one | many

-- @[simp]
-- abbrev SynthTermArgs : SynthTermIdx -> Type
-- | .one => Core.Ty × Core.Term
-- | .many => List (Core.Term) × Core.Ty × Core.Ty

-- inductive Core.Translation.SynthTerm
--   (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) : (i : SynthTermIdx) -> SynthTermArgs i -> Prop where
--   --

-- | nil :
--   SynthTerm G Δ Γ .many ([], T, T)

-- | rcons_o {ηs : List (Core.Term)} {η : Term} :
--   G&Δ ⊢ i : ★ ->
--   SynthTerm G Δ Γ .many (ηs, i -:> R, T)  ->
--   SynthTerm G Δ Γ .one (i ,  η) ->
--   SynthTerm G Δ Γ .many (ηs ++ [η], R, T)

-- | rcons_ty {ηs : List Core.Term} {τ : Ty}:
--   G&Δ ⊢ τ : K -> -- conjure a type
--   G&Δ ⊢ ∀[K]R : ★ ->
--   SynthTerm G Δ Γ .many (ηs, ∀[K]R, T)  ->
--   SynthTerm G Δ Γ .one (t ,  η) ->
--   R' = R[su τ::Subst Ty Id] ->
--   SynthTerm G Δ Γ .many (ηs ++ [.type τ], R', T)


-- -- Instance Synthesis
-- | var {x : Nat} :
--   G&Δ,Γ ⊢ #x : T ->
--   SynthTerm G Δ Γ .one (T , #x)

-- | inst {υs σs: List Core.Ty} {T R : Core.Ty}: -- T = ∀αs. νs => R
--   SynthTerm G Δ Γ .many (ηs, R, T) ->
--   SynthTerm G Δ Γ .one (T, M) ->
--   SynthTerm G Δ Γ .one
--     (R, (M.mkApps [] ηs))

-- -- coercions
-- -- | refl :
-- --   G&Δ ⊢ T : K ->
-- --   SynthTerm G Δ Γ .one (T ~[K]~ T, refl! T)
-- -- | sym :
-- --   SynthTerm G Δ Γ .one (τ ~[K]~ σ, c) ->
-- --   SynthTerm G Δ Γ .one (σ ~[K]~ τ, sym! c)
-- -- | trans :
-- --   SynthTerm G Δ Γ .one (τ  ~[K]~ ν, c1) ->
-- --   SynthTerm G Δ Γ .one (ν ~[K]~ σ, c2) ->
-- --   SynthTerm G Δ Γ .one (τ ~[K]~ σ, .seq c1 c2)
-- -- | fst :
-- --   G&Δ ⊢ σ1 : K ->
-- --   G&Δ ⊢ σ2 : K ->
-- --   SynthTerm G Δ Γ .one ((τ1 • σ1)  ~[K']~ (τ2 • σ2), η) ->
-- --   SynthTerm G Δ Γ .one (τ1 ~[K -:> K']~ τ2, fst! η)
-- -- | snd :
-- --   G&Δ ⊢ σ1 : K' ->
-- --   G&Δ ⊢ σ2 : K' ->
-- --   SynthTerm G Δ Γ .one ((τ1 • σ1)  ~[K]~ (τ2 • σ2), η) ->
-- --   SynthTerm G Δ Γ .one (σ1 ~[K']~ σ2, snd! η)
-- -- | capp :
-- --   SynthTerm G Δ Γ .one (τ1 ~[K -:> K']~ τ2, η1) ->
-- --   SynthTerm G Δ Γ .one (σ1  ~[K]~ σ2, η2) ->
-- --   SynthTerm G Δ Γ .one ((τ1 • σ1) ~[K']~ (τ2 • σ2), η1 •c η2)


-- notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢ " τ:170 " ⋈ " M:170  => Core.Translation.SynthTerm G Δ Γ SynthTermIdx.one (τ , M)

-- notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢⋈ " τs:170  => Core.Translation.SynthTerm G Δ Γ SynthTermIdx.many τs


-- inductive Surface.Ty.ImplicitSpineType
--   (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv) :
--    List Surface.Ty -> -- Predicate
--    List Term ->       -- Synth evidence
--    Surface.Ty ->      -- inferred type
--    Surface.Ty ->      -- output type/all evidences applied
--    Prop where
--   | nil : ImplicitSpineType G G' Δ Γ [] [] T T
--   | rcons_o :
--     G&Δ ⊢s i : `◯ ->
--     Core.Translation.SynthTerm G' Δ.translate Γ.translate .one (i.translate , η) ->
--     ImplicitSpineType G G' Δ Γ is ts T (i `=:> R) ->
--     ImplicitSpineType G G' Δ Γ (is ++ [i]) (ts ++ [η]) T R


inductive Mode : Type where | chk | inf

-- inductive Surface.Term.Elab (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) : Mode ->
--   Surface.KindEnv -> Surface.TyEnv -> Surface.Term -> Surface.Ty ->
--   Core.Term -> Prop where
-- | var  {Γ : Surface.TyEnv} :
--   Γ[x]? = some T ->
--   G&Δ ⊢s T : `★ ->
--   Surface.Term.Elab G G' .inf Δ Γ `#x T #x

-- | global (ηs_ext ηs_univ : List Term) (is : List Surface.Ty) :
--   Surface.lookup_type G x = some T ->
--   G&Δ ⊢s T : `★ ->
--   -- Surface.Ty.ImplicitSpineType G G' Δ Γ is ηs T B ->
--   Surface.Term.Elab G G' .inf Δ Γ g`#x B ((d#x).mkApps ⟦is⟧ ηs)
-- | app {is : List Surface.Ty}:
--   G&Δ ⊢s A : `★ ->
--   Surface.Term.Elab G G' .inf Δ Γ f (A `-:> B) f' ->
--   -- C = A `-:> B ->
--   -- Surface.Ty.ImplicitSpineType G G' Δ Γ is ηs Tinf C ->
--   Surface.Term.Elab G G' .chk Δ Γ a A a' ->
--   Surface.Term.Elab G G' .inf Δ Γ (f `• a) B (f' • a')
-- | appt :
--   G&Δ ⊢s A : K ->
--   -- (C = `∀[K] B) ->
--   -- Surface.Ty.ImplicitSpineType G G' Δ Γ is ts Tinf C ->
--   Surface.Term.Elab G G' .inf Δ Γ e (`∀[K] B) e' ->
--   C' = B[.su A :: Subst.id Ty] ->
--   Surface.Term.Elab G G' .inf Δ Γ (e `•[ A ]) C' (e' •[ ⟦A⟧ ])

-- | lam :
--   G&Δ ⊢s A : `★ ->
--   Surface.Term.Elab G G' .chk Δ (A::Γ) t B t' ->
--   Surface.Term.Elab G G' .chk Δ Γ (λˢ[A] t) (A `-:> B) (λ[A.translate] t')
-- | lamt :
--   G&(K::Δ) ⊢s P : `★ ->
--   Surface.Term.Elab G G' .chk (K::Δ) (Γ[Subst.succ Ty]) t P t' ->
--   Surface.Term.Elab G G' .chk Δ Γ (Λˢ[K] t) (`∀[K] P) (Λ[K.translate] t')

-- -- | mtch (CTy : Vect n Surface.Ty)
-- --        (PTy : Vect n Surface.Ty)
-- --        (pats : Vect n Surface.Term) (pats' : Vect n Core.Term)
-- --        (cs : Vect n Surface.Term) (cs' : Vect n Core.Term) :
-- --   Surface.Term.Elab G G' .inf Δ Γ s R s' ->
-- --   ValidTyHeadVariable R (is_data G) ->
-- --   Surface.Term.Elab G G' .inf  Δ Γ c T c' -> -- catch all term is of type T
-- --   (∀ i, ValidHeadVariable (pats i) (is_ctor G)) -> -- patterns are of the right shape
-- --   (∀ i, Surface.Term.Elab G G' .inf Δ Γ (pats i) (PTy i) (pats' i)) -> -- each pattern has a type
-- --   (∀ i, StableTypeMatch Δ (PTy i) R) -> -- the pattern type has a return type that matches datatype
-- --   (∀ i, Surface.Term.Elab G G' .chk Δ Γ (cs i) (CTy i) (cs' i)) -> -- each case match has a type
-- --   (∀ i, PrefixTypeMatch Δ (PTy i) (CTy i) T) -> -- patten type and case type
-- --   Surface.Term.Elab G G' .chk Δ Γ (matchˢ! n R s pats cs c) T (match! n s' pats' cs' c')

-- -- | sub :
-- --   Surface.Term.Elab G G' .inf Δ Γ t Tinf t' ->
-- --   Surface.Ty.ImplicitSpineType G G' Δ Γ is ts Tinf C ->
-- --   Core.Translation.SynthTerm G' Δ.translate Γ.translate .one (C.translate ~[★]~ T.translate, c) ->
-- --   Surface.Term.Elab G G' .chk Δ Γ t T (t'.mkApps ts ▹ c)

-- | annot :
--   Surface.Term.Elab G G' .chk Δ Γ t T t' ->
--   Surface.Term.Elab G G' .inf Δ Γ (.annot t T) T t'

-- notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢s " t:170 " -↪ " G':170 " ⊢ " t':170  " ∋ " A:170 => Surface.Term.Elab G G' Mode.chk Δ Γ t A t'

-- notation:170 G:170 "&" Δ:170 "," Γ:170 " ⊢s " t:170 " -↪ " G':170 " ⊢ " t':170 " ∈ " A:170 => Surface.Term.Elab G G' Mode.inf Δ Γ t A t'


-- @[simp, grind]
-- def Surface.Term.translate (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) :
--   Surface.Term -> Option Core.Term
-- | `#x => return #x
-- | g`#x => d#x
-- | .lamt K t => do
--   let t' <- t.translate G (K :: Δ) Γ[Subst.succ Core.Ty]
--   return (Λ[K] t')
-- | .lam A t => do
--   let t' <- t.translate G Δ (A :: Γ)
--   return λ[A] t'
-- | .app t1 t2 => do
--   let t1' <- t1.translate G Δ Γ
--   let t2' <- t2.translate G Δ Γ
--   return (t1' • t2')
-- | .appt t1 t2 => do
--   let t1' <- t1.translate G Δ Γ
--   let t2' <- t2
--   return (t1' •[ t2' ])
-- -- | .match (n := n) _ s ps cs d => do
-- --   let s' <- s.translate G Δ Γ
-- --   let ops' : Vect n (Option Core.Term) := (λ i => (ps i).translate G Δ Γ)
-- --   let ps' <- ops'.seq
-- --   let ocs' : Vect n (Option Core.Term) := (λ i => (cs i).translate G Δ Γ)
-- --   let cs' <- ocs'.seq
-- --   let d' <- d.translate G Δ Γ
-- --   return match! n s' ps' cs' d'
-- | .annot t _ => do
--   t.translate G Δ Γ
theorem Vec.sum_le {e : Surface.Term} {vs : Vec Surface.Term n}:
  e ∈ vs ->
  e.size < (vs.map (·.size)).sum + 1
:= by
  intro h
  induction h
  simp; omega
  case _ ih => simp; omega

theorem Vec.fun_sum_le {e : Surface.Term} {vs : Fun.Vec Surface.Term n}:
  e ∈ vs.to ->
  e.size < (Fun.Vec.to (Surface.Term.size <$> vs)).sum + 1
:= by
  intro h
  replace h := Vec.sum_le h
  simp at h;
  have lem : (Vec.map (fun x => x.size) vs.to) = (Fun.Vec.to (Surface.Term.size <$> vs)) := by
    apply Vec.ext_get; intro i
    simp [Vec.get_to]
  simp [<-lem]; apply h



-- @[simp, grind]
def Surface.Term.type_directed_translate
  (G : Core.GlobalEnv) (Δ : Core.KindEnv) (Γ : Core.TyEnv) (τ : Core.Ty) :
  Surface.Term -> TM Core.Term
| `#x =>
  match Γ[x]? with
  | some τ' => do
    if τ == τ' then
    return #x else
    let c <- Option.toTM ("var synth_coercion"
            ++ "G :" ++ G.repr max_prec ++  Std.Format.line
            ++ "Δ : " ++ Δ.repr max_prec ++ Std.Format.line
            ++ "Γ : " ++  Γ.repr max_prec ++ Std.Format.line
            ++ "τ' : " ++ τ'.repr max_prec ++ Std.Format.line
            ++ "τ : " ++  τ.repr max_prec ++ Std.Format.line)
           (Core.Ty.synth_coercion G Δ Γ τ' τ)
    return (.cast t#0 c #x)
  | _ => .error "var translate"

| .global (n := n) (m := m) (p := p) x τU τE as =>
  match Core.lookup x G with
  | .some (.ctor x' _ ⟨n', Ks1, m', Ks2, p', Ts, R⟩) => do
    -- TODO: Make sure τU and Ks line up
    let KsU <- Option.toTM "translation ctor kind check Us" (τU.map (Core.Ty.infer_kind G Δ ·)).sequence
    let KsE <- Option.toTM "translation ctor kind check Es" (τE.map (Core.Ty.infer_kind G Δ ·)).sequence
    let σ : Subst Core.Ty := (τU ++ τE).list.reverse.map su ++ Subst.id Core.Ty
    if h : (n == n' && m == m') && x == x' && p == p' && KsU.beq Ks1 && KsE.beq Ks2 then
      let c <- Option.toTM (".octor synth_coercion"
            ++ "G :" ++ G.repr max_prec ++  Std.Format.line
            ++ "Δ : " ++ Δ.repr max_prec ++ Std.Format.line
            ++ "Γ : " ++  Γ.repr max_prec ++ Std.Format.line
            ++ "R : " ++ R.repr max_prec ++ Std.Format.line
            ++ "τ : " ++  τ.repr max_prec ++ Std.Format.line)
            $ Core.Ty.synth_coercion G Δ Γ R[σ] τ
      let τs_ts := List.zip (Ts[σ].list) (as.to.list)
      let as' := τs_ts.attach.map (λ x => Term.type_directed_translate G Δ Γ x.val.1 x.val.2)
      let as' := Vec.from_list as'
      let as' <- as'.2.sequence
      return (.cast t#0 c (ctor! x τU τE as'.to))
    else .error "global translate"
  | .some (.openm x' ⟨n', Ks1, m', Ks2, _, Ts, R⟩) => do
    let KsU <- Option.toTM "translation ctor kind check Us" (τU.map (Core.Ty.infer_kind G Δ ·)).sequence
    let KsE <- Option.toTM "translation ctor kind check Es" (τE.map (Core.Ty.infer_kind G Δ ·)).sequence
    if ((n == n' && m' == 0) && x == x') && p == 0 && KsU.beq Ks1 && KsE.beq Ks2 then

    -- TODO: Make sure τU and Ks line up
      let σ : Subst Core.Ty := (τU ++ τE).list.reverse.map su ++ Subst.id Core.Ty
      let ιs := Ts[σ].map (λ x => Core.Ty.synth_term' G Δ Γ x)
      match ιs.sequence with
      | .ok ιs =>
        if h : ιs.map (·.2.1) == Ts[σ] then
        let c <- Option.toTM ("global openm synth_coercion" ++ Std.Format.line
            ++ "G :" ++ G.repr max_prec ++  Std.Format.line
            ++ "Δ : " ++ Δ.repr max_prec ++ Std.Format.line
            ++ "Γ : " ++  Γ.repr max_prec ++ Std.Format.line
            ++ "R : " ++ R.repr max_prec ++ Std.Format.line
            ++ "τ : " ++  τ.repr max_prec ++ Std.Format.line)
            $ Core.Ty.synth_coercion G Δ Γ R[σ] τ
        return (.cast t#0 c (openm! x τU τE (ιs.map (·.1)).to))
        else .error "translate synth"
      | .error c => .error c
    else .error $ "openm translate if " ++ m.repr ++ " " ++ " " ++ n.repr ++ " " ++ n'.repr -- ++ " " ++ p.repr ++ " " ++ p'.repr
  | _ => .error "openm translate"

| .lamt K t => do
  match τ with
  | .all K' τ' =>
    let t' <- type_directed_translate G (K :: Δ) Γ⟨Ren.succ Core.Ty⟩ τ' t
    if K == K' then return (Λ[K] t') else .error "lamt translate"
  | _ => .error "lamt translate"
| .lam A t => do
  match τ with
  | .arrow A' B =>
    let t' <- type_directed_translate G Δ (A :: Γ) B t
    let c <- Option.toTM ("lam synth_coercion" ++ Std.Format.line
            ++ "G :" ++ G.repr max_prec ++  Std.Format.line
            ++ "Δ : " ++ Δ.repr max_prec ++ Std.Format.line
            ++ "Γ : " ++  Γ.repr max_prec ++ Std.Format.line
            ++ "A -:> B : " ++ (A -:> B).repr max_prec ++ Std.Format.line
            ++ "A' -:> B : " ++  (A' -:> B).repr max_prec ++ Std.Format.line)
             $ Core.Ty.synth_coercion G Δ Γ (A -:> B) (A' -:> B)
    return (Core.Term.cast t#0 c (λ[A] t'))
  | _ => .error "lam translate"

-- Elimination forms are a little annoying

| .app t1 t2 τArg => do
  let t2' <- type_directed_translate G Δ Γ τArg t2
  let t1' <- type_directed_translate G Δ Γ (τArg -:> τ) t1
  return t1' • t2'
-- | .match (n := n) R s ps cs d => do
--   let s' <- s.type_directed_translate G Δ Γ R
--   let ops' : Vect n (Option Core.Term) := (λ i => (ps i).translate G Δ Γ)
--   let ps' <- ops'.seq
--   let ocs' : Vect n (Option Core.Term) := (λ i => (cs i).translate G Δ Γ)
--   let cs' <- ocs'.seq
--   let d' <- d.type_directed_translate G Δ Γ τ
--   return match! n s' ps' cs' d'
| .annot t τt => do
  let t' <- type_directed_translate G Δ Γ τt t
  let c <- Option.toTM ("synth_coercion"
            ++ "G :" ++ G.repr max_prec ++  Std.Format.line
            ++ "Δ : " ++ Δ.repr max_prec ++ Std.Format.line
            ++ "Γ : " ++  Γ.repr max_prec ++ Std.Format.line
            ++ "τt : " ++ τt.repr max_prec ++ Std.Format.line
            ++ "τ : " ++  τ.repr max_prec ++ Std.Format.line)
           $ Core.Ty.synth_coercion G Δ Γ τt τ
  return .cast t#0 c t'

| t => .error $ "translate doesn't handle" ++ t.repr max_prec

termination_by
  t => t.size
decreasing_by
  all_goals (try simp)
  all_goals (try omega)
  case _ =>
    simp [τs_ts] at x;
    have lem1 : x.val.2 ∈ as.to.list := by
      rcases x with ⟨v, p⟩
      simp; replace p := List.of_mem_zip p; apply p.2
    have lem : x.val.2 ∈ as.to := by
      simp [Vec.mem_list]; apply lem1
    apply Vec.fun_sum_le lem

-- | t =>
--   match sp_prf : t.spine with
--   | some (x, sp) => do
--     let sp := sp.attach

--     let hτ <- Core.lookup_type G x
--     let (t', r) <- List.foldlM (λ (acct, τ) x =>
--                match τ, x with
--                | .all K τ, ⟨.type A, prf⟩ =>
--                  -- K better be kind of A, but we can't do that yet.
--                  let A' := A.translate
--                  let σ : Subst Core.Ty := (su A')::+0
--                  return (acct •[ A' ], τ[σ])
--                | .arrow A B, ⟨.term t, prf⟩ => do
--                  let t' <- t.type_directed_translate G Δ Γ A
--                  return (acct • t', B)
--                | _ , _ => none)
--                (g#x, hτ) sp
--     if r == τ.translate then return t' else none
--   | none => none
-- termination_by t => t.size
-- decreasing_by (
-- all_goals try (simp at *)
-- · omega
-- · omega
-- · have lem := Spine.elem_size_le_term sp_prf (.term t) prf; simp [SpineElem.size] at lem; exact lem
-- )
-- def Surface.Ty.prefix_type_match (Δ : List Kind) : Ty -> Ty -> Option Ty
--   | (.arrow A B), (.arrow A' B') => do
--     if A == A'
--     then prefix_type_match Δ B B'
--     else none

--   | (.all K A), (.all K' A') => do
--     if K == K'
--     then let x <- prefix_type_match (K :: Δ) A A'
--          if x[-1][+1] == x
--          then return x[-1]
--          else none
--     else none
--   | A, T => do
--     let _ <- A.spine
--     return T

-- def Surface.Ty.stable_type_match : List Kind -> Ty -> Ty -> Option Unit
-- | Δ, (.all K A), R => Ty.stable_type_match (K::Δ) A R[+1]
-- | Δ, (.arrow _ B), R => Ty.stable_type_match Δ B R
-- | _, A, R =>
--  do
--   let _ <- R.spine
--   if A == R
--   then some ()
--   else none



-- mutual

--   def Surface.Term.type_inf_translate
--     (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv):
--     Surface.Term -> Option (Core.Term × Surface.Ty)

--   | `#x => do
--     let τ <- Γ[x]?
--     return (#x, τ)
--   | g`#x => do
--     let τ <- Surface.lookup_type G x
--     let (is, B) := τ.overloaded_type
--     let ts <- is.mapM (λ x => Core.Ty.synth_term G' Δ.translate Γ.translate x.translate)
--     return ((g#x).apply (ts.map (Core.SpineElem.oterm ·)), B)
--   | .annot t τt => do
--     let t' <- t.type_chk_translate G G' Δ Γ τt
--     return (t' , τt)
--   | .appt f a => do
--     let (f', T) <- f.type_inf_translate G G' Δ Γ
--     match T with
--     | .all K T =>
--       -- ensure a has kind K?
--       return (f' •[ a.translate ], T[su a ::+0])
--     | _ => none
--   | .app f a => do
--     let (f', T) <- f.type_inf_translate G G' Δ Γ
--     match T with
--     | A `-:> B =>
--       let a' <- a.type_chk_translate G G' Δ Γ A
--       -- ensure a has kind K?
--       return (f' • a', B)
--     | _ => none
--   | _ => none


--   def Surface.Term.type_chk_translate
--     (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv) (τ : Surface.Ty) :
--     Surface.Term -> Option Core.Term

--   | .lamt K t => do
--     match τ with
--     | .all K' τ' =>
--       let t' <- t.type_chk_translate G G' (K::Δ) (Γ.map (·[+1])) τ'
--       if K' == K then return (Λ[K.translate] t') else none
--     | _ => none
--   | .lam A' t => do
--     match τ with
--     | .arrow A B =>
--       let t' <- t.type_chk_translate G G' Δ (A::Γ) B
--       if A == A' then return λ[A.translate] t' else none
--     | _ => none

--   | .match (n := n) R s ps cs d => do
--     let s' <- s.type_chk_translate G G' Δ Γ R
--     let ops' : Vect n (Option (Core.Term × Ty)) := (λ i => (ps i).type_inf_translate G G' Δ Γ)
--     let ps' <- ops'.seq
--     let ocs' : Vect n (Option (Core.Term × Ty)) := (λ i => (cs i).type_inf_translate G G' Δ Γ)
--     let cs' <- ocs'.seq
--     let _ <- R.valid_data_type G
--     let ops' : Vect n (Option Unit) := λ i => Surface.Ty.stable_type_match Δ (ps' i).snd R
--     let _ <- ops'.seq
--     let ostm : Vect n (Option Surface.Ty) :=  λ i => Ty.prefix_type_match Δ ((ps' i).snd) (cs' i).snd
--     let _ <- ostm.seq
--     let d' <- d.type_chk_translate G G' Δ Γ τ
--     match! n s' ((λ x => x.fst) <$> ps') ((λ x => x.fst) <$> cs') d'
--   | _ => none
  -- | t => do
  --     let (x, sp) <- t.spine
  --     let hτ <- Surface.lookup_type G x
  --     let (sp', r) <- translate_spine G G' Δ Γ hτ sp
  --     if r == τ then (g#x).apply sp' else none
  -- decreasing_by
  --   case _ => sorry

  --   repeat sorry


  -- def Surface.Term.translate_spine
  --   (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv) :
  --   Surface.Ty -> List Surface.SpineElem -> Option (List Core.SpineElem × Surface.Ty)
  -- |  A `-:> B, (.cons (.term t) sp) => do
  --   let t' <- t.type_chk_translate G G' Δ Γ A
  --   let (sp', r) <- translate_spine G G' Δ Γ B sp
  --   return ((Core.SpineElem.term t' :: sp') , r)
  -- | A `=:> B, sp => do
  --   let d <- A.translate.synth_term G' Δ.translate Γ.translate
  --   let (sp', r) <- translate_spine G G' Δ Γ B sp
  --   return (Core.SpineElem.oterm d :: sp', r)
  -- | `∀[K] B, (.cons (.type t) sp) => do
  --   let (sp', r) <- translate_spine G G' Δ Γ (B[su t::+0]) sp
  --   return ((Core.SpineElem.type t.translate :: sp') , r)
  -- | _ , _ => none
  -- decreasing_by
  --   repeat sorry


-- | t =>
--   match sp_prf : t.spine with
--   | some (x, sp) => do
--     let sp := sp.attach

--     let hτ <- Core.lookup_type G x
--     let (t', r) <- List.foldlM (λ (acct, τ) x =>
--                match τ, x with
--                | .all K τ, ⟨.type A, prf⟩ =>
--                  -- K better be kind of A, but we can't do that yet.
--                  let A' := A.translate
--                  let σ : Subst Core.Ty := (su A')::+0
--                  return (acct •[ A' ], τ[σ])
--                | .arrow A B, ⟨.term t, prf⟩ => do
--                  let t' <- t.type_directed_translate G Δ Γ A
--                  return (acct • t', B)
--                | _ , _ => none)
--                (g#x, hτ) sp
--     if r == τ.translate then return t' else none
--   | none => none
-- termination_by t => t.size
-- decreasing_by (
-- all_goals try (simp at *)
-- · omega
-- · omega
-- · have lem := Spine.elem_size_le_term sp_prf (.term t) prf; simp [SpineElem.size] at lem; exact lem
-- )

-- end

-- @[simp]
-- abbrev ElabArgs : Mode -> Type
-- | .inf => Option (Core.Term × Surface.Ty)
-- | .chk => Surface.Ty -> Option (Core.Term)

-- def elab_term (G : Surface.GlobalEnv) (G' : Core.GlobalEnv) (Δ : Surface.KindEnv) (Γ : Surface.TyEnv) (t : Surface.Term) : (m : Mode) -> ElabArgs m
-- | .inf => Surface.Term.type_inf_translate G G' Δ Γ t
-- | .chk => λ (τ : Surface.Ty) => Surface.Term.type_chk_translate G G' Δ Γ τ t

end Translation
