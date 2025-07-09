import Hs.Algorithm
import SystemFD.Algorithm

set_option profiler true
set_option linter.unusedVariables false

-- Henry Ford Encode a type:
-- Takes a type of the form
-- ∀ αs. assms -> D τs
-- and converts it to
-- ∀βs. ∀αs. (βs ~ αs) -> assms -> D βs
-- ASSUMES all type binders are in front in the original type
-- It doesn't matter if αs have type variables, they would
-- just introduce a tyvar_new ~ tyvar_old rather than tyvar_new ~ Int
@[simp]
def encode_hf : Ctx Term -> (Ctx Term × Nat × List (SpineVariant × Term)) -> DsM (Term × Nat) :=
λ Γ data => do
  let (Γ_l, d, d_τs) := data

  let Γ_local := Γ_l.reverse
  let d_αs_kis <- List.mapM (λ x =>
      .toDsM ("hf encode infer_kind"
            ++ Std.Format.line ++ repr (Γ_local ++ Γ) ++ Std.Format.line ++ repr x)
      (infer_kind (Γ_local ++ Γ) x.2)) d_τs

  let (Γ_αs, Γ_assms) := Γ_l.partition (λ x => x.is_kind)

  let βs := fresh_vars d_τs.length
  let βs := βs.map ([S' Γ_αs.length]·)
  let βs := βs.reverse -- the largest index to appear closest to the head (convention)


  -- all the RHS of the equality types
  let d_αs' := d_τs.map (λ x => [λ n => .re (if n < Γ_local.length
                                        then n - Γ_assms.length
                                        else n + βs.length - Γ_assms.length)] x.2)

  let eqs := Term.mk_eqs (List.zip d_αs_kis (List.zip βs d_αs'))

  let Γ_assms := Γ_assms.map (λ f => f.apply (λ n =>
              .re (if n < Γ_local.length
                   then n + βs.length
                   else n + 2*βs.length)))

  let ty' := [S' eqs.length] Term.mk_kind_apps ([S' βs.length]#d) (βs.map (λ x => [S' Γ_assms.length] x))

  let ty' := ty'.from_telescope_rev Γ_assms

  let ty' := ty'.from_telescope_rev (Term.mk_type_telescope [] eqs)

  let ty' := ty'.from_telescope_rev Γ_αs

  let ty' := ty'.from_telescope_rev (Term.mk_kind_telescope [] d_αs_kis)

  .ok (ty', d_τs.length)


@[simp]
def mk_inst_type : Ctx Term -> Term -> DsM (Nat × Term × Nat) := λ Γ ty => do
  let (Γ_local, res_ty) := ty.to_telescope
  let (d, d_τs) <- .toDsM ("mk_inst_type neutral_form" ++ Std.Format.line ++ repr res_ty) res_ty.neutral_form
  let (ty', n) <- encode_hf Γ (Γ_local, d, d_τs)
  .ok (d - Γ_local.length, ty', n)

#guard (Term.shift_helper 10).take 5 == [0,1,2,3,4]

-- given a hf type returns a decoded type
def un_inst_type : Term -> DsM Term := λ ty => do
  let (tele_ty, ret_ty) := ty.to_telescope
  let (Γ_tyvars, Γ_vars) := tele_ty.partition (·.is_kind)

  let (_, sp) <- .toDsMq ret_ty.neutral_form

  let (Γ_βs, Γ_αs) := Γ_tyvars.splitAt sp.length

  let (Γ_eqs, Γ_assms) := Γ_vars.splitAt Γ_βs.length


  let σ : Subst Term <- .toDsM "un_inst_type eqs" (((Term.shift_helper Γ_eqs.length).zip Γ_eqs).foldlM (λ accσ τ =>
    match τ with
    | (si, .type (#n ~[_]~ t)) => .some (λ v => .su (if v == (n - si) then [P' si]t else [accσ](#v)))
    | _ => .none
    ) I)

  let ret_ty := ret_ty.from_telescope Γ_assms
  let ret_ty := [P' Γ_eqs.length] ret_ty

  let ret_ty := [σ] ret_ty
  let ret_ty := ret_ty.from_telescope Γ_αs

  let ret_ty := [P' Γ_βs.length] ret_ty

  -- .error ("unimplemented "
  --   ++ Std.Format.line ++ "τ: " ++ repr ty
  --   ++ Std.Format.line ++ "Γ_βs: " ++ repr Γ_βs
  --   ++ Std.Format.line ++ "Γ_αs: " ++ repr Γ_αs
  --   ++ Std.Format.line ++ "Γ_eqs: " ++ repr Γ_eqs
  --   ++ Std.Format.line ++ "Γ_assms: " ++ repr Γ_assms
  --   ++ Std.Format.line ++ "ret_ty: " ++ repr ret_ty)

  .ok ret_ty




partial def synth_instance_coercion (Γ : Ctx Term) (cls_idx : Nat) :
  Ctx Term -> Ctx Term -> Ctx Term -> Term -> DsM Term
| Γ_l, Γ_outer, Γ_inner, τ => do
  -- the two things that i want to find the coercion to equate will be in Γ_l
  -- Open methods for fundeps have a predetermined shape
  -- ∀βs ∀v. F βs -> F βs v -> u ~ v
  -- where u is one of the indices in βs


  -- find the functional dependencies associated with the subject class
  let Γ_g := Γ_inner ++ Γ_outer ++ Γ_l ++ Γ
  let fd_ids <- get_fundep_ids Γ_g cls_idx
  let fun_deps <- get_fundeps "synth_instance_coercion" Γ_g cls_idx

  let fd_ids := fd_ids.reverse
  let fun_deps := fun_deps.reverse


  let (Γ_outer_tyvars, Γ_outer_assms) :=
      Γ_outer.partition (λ x => x.is_kind)

   let (Γ_outer_assms, Γ_outer_eqs) :=
      Γ_outer_assms.partition (λ x =>
      match x.get_type with
      | .none => false
      | .some τ => not (Option.isSome (is_eq τ)))

   let (Γ_inner_tyvars, Γ_instτ_inner_assms) :=
       Γ_inner.partition (λ x => x.is_kind)

   let (Γ_inner_assms, Γ_inner_eqs) :=
       Γ_instτ_inner_assms.partition (λ x =>
       match x.get_type with
       | .none => false
       | .some τ => not (Option.isSome (is_eq τ)))

  -- rebase outer_assms and inner_assms to be relative to Γ_g
  let Γ_inner_assms := (Γ_inner_assms.zip (Term.shift_helper Γ_inner_assms.length)).map (λ x =>
      x.1.apply (S' (x.2 + 1)))
  let Γ_outer_assms := (Γ_outer_assms.zip (Term.shift_helper Γ_outer_assms.length)).map (λ x =>
      x.1.apply (S' (x.2 + 1 + Γ_inner.length)))

   -- Step 1. See if any of the determiners of the assumptions can be equated.
  let ηs_determiners : List (Term × Term) <- (Γ_inner_assms.product Γ_outer_assms).foldlM (λ acc x => do
    let (pred1, pred2) : Frame Term × Frame Term := x
    match (pred1, pred2) with
    | (.type τ1, .type τ2) =>
      match (τ1.neutral_form, τ2.neutral_form) with
      | (.some (τh1, τs1), .some (τh2, τs2)) =>
        if τh1 == τh2
        then do
          let fundeps <- get_fundeps "ηs_determiners" Γ_g τh1
          let determiners_coupled := (Term.shift_helper τs1.length).zip (τs1.reverse.zip τs2.reverse)
          -- for each fundep try to find the coercion that equates the determiners
          let ηs_tys := fundeps.map (λ (xs, _) => xs.map (λ x => determiners_coupled.lookup x))
          let ηs_l : List (Term × Term) := (ηs_tys.flatten.map (λ x =>
              match x with
              | .some ((SpineVariant.kind, τ1), (SpineVariant.kind, τ2)) => do
                let ki <- infer_kind Γ_g τ1
                let η <- synth_coercion Γ_g τ1 τ2
                .some (τ1 ~[ki]~ τ2, η)
              | _ => .none)).reduceOption
          return (ηs_l ++ acc)
        else return acc

      | _ => return acc
    | _ => return acc
   ) []


  ηs_determiners.forM (λ x => do let τ' <- .toDsM "infer failed" (infer_type Γ_g x.2)
                                 if x.1 == τ' then .ok () else .error "η failed"
                                 )

  let Γ_ηs := (ηs_determiners.zip (Term.shift_helper ηs_determiners.length)).map (λ ((τ, t), si) =>
           Frame.term ([S' si]τ) ([S' si]t))

  .toDsM "wf_ctx failed Γ_ηs" (wf_ctx (Γ_ηs ++ Γ_g))

  -- rebase outer_assms and inner_assms to be relative to Γ_g + Γ_ηs
  let Γ_inner_assms := Γ_inner_assms.map (λ x => x.apply (S' Γ_ηs.length))
  let Γ_outer_assms := Γ_outer_assms.map (λ x => x.apply (S' Γ_ηs.length))


  -- Step 2. Use pairwise improvement on local assumptions by taking into
  --         consideration the new equalities between determiners
  let Γ_assms_pairs := (Γ_outer_assms.product Γ_inner_assms).filter (λ x =>
    match x with
    | (.type x, .type y) =>
      match (x.neutral_form, y.neutral_form) with
      | (.some (τ1h, τs1), .some (τ2h, τs2)) => τ1h == τ2h && τ1h == cls_idx + Γ_ηs.length
      | _ => false
    | _ => false
  )

      -- outer vars relative to Γ_ηs
  let outer_vars := (fresh_vars Γ_outer.length).map
               ([S' (Γ_ηs.length + Γ_inner.length)]·)

  let inner_vars := (fresh_vars Γ_inner.length).map
               ([S' Γ_ηs.length]·)

  let (outer_tyvars, outer_vars) := outer_vars.reverse.splitAt Γ_outer_tyvars.length
  let (outer_vars_eqs, outer_vars_assms) := outer_vars.splitAt Γ_outer_eqs.length

      -- let inner_tyvars := (fresh_vars Γ_inner_tyvars.length).map
      --          ([S' (Γ_ηs.length + Γ_inner_eqs.length + Γ_inner_assms.length)]·)

  let (inner_tyvars, inner_vars) := inner_vars.reverse.splitAt Γ_inner_tyvars.length
  let (inner_vars_eqs, inner_vars_assms) := inner_vars.splitAt Γ_inner_eqs.length

  let pairwise_ηs : List (Term × Term) <- (fd_ids.zip fun_deps).foldlM (λ acc i =>
    let (i, fundep) := i
    match (Γ_g d@ i) with
    | .openm τ => do
      let τ := [S' Γ_ηs.length] τ  -- make it relative to Γ_ηs + Γ_g

      -- try to build a pairwise improvement by
      -- applying the fundep to the outer type variabes and the determinant of the
      -- inner type variable
      let t := (#(i + Γ_ηs.length)).mk_ty_apps outer_tyvars
      let τ <- .toDsM "pairwise impr instantiate" (instantiate_types τ outer_tyvars)

      let inner_determinant := inner_tyvars.reverse[fundep.2]?
      match inner_determinant with
      | .some det =>
        let t := t `@t det
        let τ <- .toDsM "pairwise impr instantiate det" (instantiate_type τ det)

        let (tele_τ, ret_ty) := τ.to_telescope
        let tele_τ := (tele_τ.zip (Term.shift_helper tele_τ.length)).map (λ (f, sid) => f.apply (P' sid))
        let args_outer := ((outer_vars_assms.zip Γ_outer_assms).zip tele_τ).mapM (λ ((v, τ), τ') => do
          let τ <- τ.get_type
          let τ' <- τ'.get_type
          if τ == τ' then v
          else do let η <- synth_coercion (Γ_ηs ++ Γ_g) τ τ'
                  .some (v ▹ η))
        let args_inner :=
          ((inner_vars_assms.zip Γ_inner_assms).zip
                  (tele_τ.drop outer_vars_assms.length)).mapM (λ ((v, τ), τ') => do
          let τ <- τ.get_type
          let τ' <- τ'.get_type
          if τ == τ' then v
          else do let η <- synth_coercion (Γ_ηs ++ Γ_g) τ τ'
                  .some (v ▹ η))

        match (args_outer, args_inner) with
        | (Option.some args_outer, Option.some args_inner) =>
          let args := args_outer ++ args_inner
          let t := t.mk_apps args
          let τ := [P' 2]ret_ty
          return ((τ, t) :: acc)

          -- .error ("pairwise impr"
          -- ++ Std.Format.line ++ "τ: " ++ repr τ
          -- ++ Std.Format.line ++ "t: " ++ repr t
          -- ++ Std.Format.line ++ "args_outer: " ++ repr args_outer ++ repr (tele_τ.take outer_vars_assms.length)
          -- ++ Std.Format.line ++ "args_inner: " ++ repr args_inner ++ repr (tele_τ.drop outer_vars_assms.length)
          -- ++ Std.Format.line ++ "outer_tyvars: " ++ repr outer_tyvars ++ repr Γ_outer_tyvars
          -- ++ Std.Format.line ++ "outer_vars_assms: " ++ repr outer_vars_assms ++ repr Γ_outer_assms
          -- ++ Std.Format.line ++ "inner_tyvars: " ++ repr inner_tyvars ++ repr Γ_inner_tyvars
          -- ++ Std.Format.line ++ "inner_vars_assms: " ++ repr inner_vars_assms ++ repr Γ_inner_assms

          -- ++ Std.Format.line ++ "tele_τ: " ++ repr tele_τ
          -- ++ Std.Format.line ++ "Γ_pairs: " ++ repr Γ_assms_pairs
          -- ++ Std.Format.line ++ "Γ_ηs: " ++ repr Γ_ηs
          -- ++ Std.Format.line ++ "Γ_g: " ++ repr Γ_g
          -- ++ Std.Format.line ++ "fundep_id: " ++ repr i
          -- ++ Std.Format.line ++ "fundep: " ++ repr fundep)
        | _ => return acc

      | .none => return acc
    | _ => return acc) []

  pairwise_ηs.forM (λ x => do let τ' <- .toDsM "infer failed" (infer_type (Γ_ηs ++ Γ_g) x.2)
                                 if x.1 == τ' then .ok () else .error "pairwise η failed"
                                 )

  let Γ_pairwise_ηs : Ctx Term :=
      (pairwise_ηs.zip (Term.shift_helper pairwise_ηs.length)).map (λ ((τ, t), si) =>
        .term ([S' si]τ) ([S' si]t))

  .toDsM "wf_ctx failed Γ_pairwise" (wf_ctx (Γ_pairwise_ηs ++ Γ_ηs ++ Γ_g))

  let τ := [S' (Γ_ηs.length + Γ_pairwise_ηs.length)]τ
  let t <- .toDsM ("synth_inst_coercion"
  ++ Std.Format.line ++ "τ: " ++ repr τ

  ++ Std.Format.line ++ "Γ_pairwise_ηs" ++ repr Γ_pairwise_ηs
  ++ Std.Format.line ++ "Γ_ηs" ++ repr Γ_ηs
--  ++ Std.Format.line ++ "Γ_inner: " ++ repr Γ_inner
--  ++ Std.Format.line ++ "Γ_inner_tyvars: " ++ repr Γ_inner_tyvars
--  ++ Std.Format.line ++ "Γ_outer: " ++ repr Γ_outer
--  ++ Std.Format.line ++ "Γ_outer_tyvars: " ++ repr Γ_outer_tyvars
--  ++ Std.Format.line ++ "Γ_l: " ++ repr Γ_l

  ++ Std.Format.line ++ "Γ_g: " ++ repr Γ_g
  -- ++ Std.Format.line ++ "Γ: " ++ repr Γ
  ++ Std.Format.line ++ "fd_ids: " ++ repr fd_ids
  ++ Std.Format.line ++ "fds: " ++ repr fun_deps
  ) (synth_term (Γ_pairwise_ηs ++ Γ_ηs ++ Γ_g) τ)
  let η := t.mk_lets_rev (Γ_pairwise_ηs ++ Γ_ηs)

  match η with
  | .some η => do
    .toDsM ("infer_type η"
      ++ Std.Format.line ++ repr η
      ++ Std.Format.line ++ repr Γ_g
      )
      (do let _ <- infer_type Γ_g η)
    return η
  | .none => .error ("instance coercion failed")


namespace Algorithm2.Test
  def Γ : Ctx Term := [
    .openm (∀[★](#5 `@k #0) -t> #1 -t> #2 -t> #9),
    .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
    .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
    .opent (★ -k> ★),
    .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
    .opent (★ -k> ★),
    .datatype ★ ]

  #guard wf_ctx Γ == .some ()
  -- #eval (#5 `@k #6)
  #guard (mk_inst_type Γ (#5 `@k #6)) == .ok (5, ∀[★](#0 ~[★]~ #7) -t> #7 `@k #1, 1)
  #guard (un_inst_type (∀[★](#0 ~[★]~ #7) -t> #7 `@k #1)) == .ok (#5 `@k #6)


  -- #eval (∀[★] (#4 `@k #0) -t> #7 `@k #1)
  #guard (mk_inst_type Γ (∀[★] #4 `@k #0 -t> #7 `@k #1))
             == .ok (5, ∀[★]∀[★](#1 ~[★]~ #0) -t> #6 `@k #1 -t> #9 `@k #3, 1)
  #guard (un_inst_type (∀[★]∀[★](#1 ~[★]~ #0) -t> #6 `@k #1 -t> #9 `@k #3)) == .ok (∀[★] #4 `@k #0 -t> #7 `@k #1)

  def Γ0 : Ctx Term := [.datatype ★, .datatype ★, .opent (★ -k> ★ -k> ★)]
  #guard (mk_inst_type Γ0 (#2 `@k #1 `@k #0)) == .ok (2, ∀[★]∀[★](#1 ~[★]~ #3) -t> (#1 ~[★]~ #3) -t> #6 `@k #3 `@k #2, 2)
  -- #eval DsM.run ((un_inst_type (∀[★]∀[★](#1 ~[★]~ #3) -t> (#1 ~[★]~ #3) -t> #6 `@k #3 `@k #2)))
  #guard (un_inst_type (∀[★]∀[★](#1 ~[★]~ #3) -t> (#1 ~[★]~ #3) -t> #6 `@k #3 `@k #2)) ==
         .ok (#2 `@k #1 `@k #0)

  def Γ1 : Ctx Term := [
 .inst #8
      (Λ[★]((Λ[★]((Λ[★]((`λ[((#13 `@k #2) `@k #1)]
      (`λ[((#14 `@k #1) `@k #2)]
        .guard (#6 `@t #4 `@t #3) #1
         (`λ[(#4 ~[★]~ #9)]
         (`λ[(#4 ~[★]~ #10)]
         .guard (#8 `@t #4 `@t #5)  #2
         (`λ[(#4 ~[★]~ #11)] (`λ[(#6 ~[★]~ #12)] (((refl! ★ #8) `;  #3) `;  (sym! #1)))))))))))))),
    .inst #8
      (Λ[★]((Λ[★]((Λ[★]((`λ[((#12 `@k #2) `@k #1)]
        (`λ[((#13 `@k #3) `@k #1)]
         .guard (#5 `@t #4 `@t #3) #1
          (`λ[(#4 ~[★]~ #8)]
          (`λ[(#4 ~[★]~ #9)]
           .guard (#7 `@t #6 `@t #4) #2
            (`λ[(#6 ~[★]~ #10)] (`λ[(#5 ~[★]~ #11)] (((refl! ★ #7) `;  #2) `;  (sym! #0)))))))))))))),
 .insttype (∀[★](∀[★]((#1 ~[★]~ #4) -t> ((#1 ~[★]~ #5) -t> (#12 `@k #3 `@k #2))))),
 .ctor #1,
 .ctor #0,
 .datatype ★,
 .ctor (∀[★](#0 -t> (#3 `@k #1))),
 .ctor (∀[★](#1 `@k #0)),
 .datatype (★ -k> ★),
 .openm (∀[★](∀[★](∀[★](((#4 `@k #2) `@k #1) -t> (((#5 `@k #1) `@k #2) -t> (#4 ~[★]~ #2)))))),
 .openm (∀[★](∀[★](∀[★](((#3 `@k #2) `@k #1) -t> (((#4 `@k #3) `@k #1) -t> (#3 ~[★]~ #2)))))),
 .opent (★ -k> (★ -k> ★)) ]


  --  #eval DsM.run (mk_inst_type Γ1 (∀[★]∀[★]((#13 `@k #1) `@k #0) -t> #14 `@k (#11 `@k #2) `@k (#11 `@k #1)))
  #guard (mk_inst_type Γ1 (∀[★]∀[★]((#13 `@k #1) `@k #0) -t> #14 `@k (#11 `@k #2) `@k (#11 `@k #1)))
       == .ok (11, ∀[★]∀[★]∀[★]∀[★](#3 ~[★]~ #12 `@k #1) -t> (#3 ~[★]~ #13 `@k #1) -t> #17 `@k #3 `@k #2 -t> #18 `@k #6 `@k #5, 2)

  -- #eval DsM.run (un_inst_type (∀[★]∀[★]∀[★]∀[★](#3 ~[★]~ #12 `@k #1) -t> (#3 ~[★]~ #13 `@k #1) -t> #17 `@k #3 `@k #2 -t> #18 `@k #6 `@k #5))
  #guard  un_inst_type (∀[★]∀[★]∀[★]∀[★](#3 ~[★]~ #12 `@k #1) -t> (#3 ~[★]~ #13 `@k #1) -t> #17 `@k #3 `@k #2 -t> #18 `@k #6 `@k #5) == .ok (∀[★]∀[★]((#13 `@k #1) `@k #0) -t> #14 `@k (#11 `@k #2) `@k (#11 `@k #1))



def ctx4 : Ctx Term := [

 .type (#18 `@k #3 `@k #2),      -- Eq a'' b''
 .type (#10 ~[★]~ (#14 `@k #1)), -- c ~ Maybe b''
 .type (#11 ~[★]~ (#13 `@k #1)), -- a ~ Maybe a''
 .kind (★),                 -- b''
 .kind (★),                 -- a''

 .type (#13 `@k #3 `@k #2),    -- Eq a' b'
 .type (#6 ~[★]~ (#9 `@k #1)), -- b ~ Maybe b'
 .type (#6 ~[★]~ (#8 `@k #1)), -- a ~ Maybe a'
 .kind (★), -- b'
 .kind (★), -- a'

 .type (#8 `@k #3 `@k #1), -- Eq a c
 .type (#7 `@k #2 `@k #1), -- Eq a b
 .kind (★), -- c
 .kind (★), -- b
 .kind (★), -- a

 .datatype ★,
 .datatype (★ -k> ★),
 .openm (∀[★]∀[★]∀[★]((#4 `@k #2) `@k #1) -t> ((#5 `@k #1) `@k #2) -t> #4 ~[★]~ #2),
 .openm (∀[★]∀[★]∀[★]((#3 `@k #2) `@k #1) -t> ((#4 `@k #3) `@k #1) -t> #3 ~[★]~ #2),
 .opent (★ -k> ★ -k> ★)]


def η : Term :=
  .letterm (#4 ~[★]~ #9) ((refl! ★ #4) `;
    (snd! ★ (sym! #2) `;
    #7)) (
  .letterm (#9 ~[★]~ #4) (#19 `@t #10 `@t #9 `@t #4 `@ #6 `@ (#1 ▹
         (((refl! (★ -k> (★ -k> ★)) #20) `@c ((refl! ★ #5) `;  #0)) `@c (refl! ★ #4))))
        (refl! ★ #15) `;
        #8 `;
        (refl! ★ #18) `@c #0 `;
        (sym! #3))

#guard wf_ctx (ctx4) == .some ()
-- #guard wf_ctx (.term (#4 ~[★]~ #9) (((refl! ★ #4) `; (snd! ★ (sym! #2) `;  #7))) :: ctx4) == .some ()


#eval DsM.run (synth_instance_coercion (ctx4.drop 15) 19 ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#3 ~[★]~ #8))

#guard (do let η <- synth_instance_coercion (ctx4.drop 15) 19
                       ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#3 ~[★]~ #8)
           .toDsMq (infer_type ctx4 η)
              ) == .ok (#3 ~[★]~ #8)

#eval DsM.run (synth_instance_coercion (ctx4.drop 15) 19 ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#13 ~[★]~ #12))

#guard (do let η <- synth_instance_coercion (ctx4.drop 15) 19
                ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#13 ~[★]~ #12)
           .toDsMq (infer_type ctx4 η)) == .ok (#13  ~[★]~ #12)

end Algorithm2.Test


@[simp]
def to_implicit_telescope_aux (Δ : Ctx Term) : (Ctx Term) -> Term -> Ctx Term × Term
| Γ, ∀[A] B =>
    let (Γ', r) := to_implicit_telescope_aux (.kind A :: Δ) Γ B
    (.kind A::Γ', r)
| Γ, .bind2 .arrow A B =>
    match A.neutral_form with
    | .some (h, _) =>
      if Δ.is_opent h
      then let (Γ', r) := to_implicit_telescope_aux (.type A :: Δ) Γ B
         (.type A::Γ', r)
      else (Γ, .bind2 .arrow A B)
    | .none =>
      let (Γ, r) := to_implicit_telescope_aux (.type A :: Δ) Γ B
      (.type A::Γ, r)
| Γ, t => (Γ, t)

@[simp]
def to_implicit_telescope (Δ : Ctx Term) : Term -> Ctx Term × Term := to_implicit_telescope_aux Δ []

def doConsistencyCheck (Γ : Ctx Term) (fd : FunDep): Term × Term -> DsM Unit := λ x => do
  -- TODO: Work with un_inst_type rather than inst_type
  let (instA, instB) := x
  -- -- Both the telescopes are henry forded
  -- -- ∀κs. (β1 ~ x) -> (β2 ~ y) -> F β1 β2
  let (teleA, _) := instA.to_telescope
  let (teleB, _) := instB.to_telescope

  let (teleA_tyvars, teleA_eqs) := teleA.partition (·.is_kind)
  let (teleB_tyvars, teleB_eqs) := teleB.partition (·.is_kind)

  let eqs := teleA_eqs.zip teleB_eqs


  let eqs : List (Nat × (Frame Term × Frame Term)) := ((Term.shift_helper eqs.length).zip eqs.reverse).foldl
    (λ acc x =>
    let (sidx, eq) := x
    ((if sidx > fd.2
      then (sidx, ((eq.1.apply (P) , (eq.2.apply (P)))))
      else (sidx, eq))
      :: acc)) []


  -- all the eqs are now indexed at Γ + teleA_tyvars
  let determiners : List (Frame Term × Frame Term) <- .toDsM "consistencyCheck determiners"
    (fd.1.mapM (λ n => eqs.lookup n))
  -- let determiners : List (Term × Term) <- .toDsM "consistencyCheck determiners2"
  --                    (determiners.mapM (λ x => do
  --                 let x1' <- x.1.get_type
  --                 let x2' <- x.2.get_type
  --                 (x1', x2')))

  let determinant : (Frame Term × Frame Term) <- .toDsM "consistencyCheck determinant" (eqs.lookup fd.2)
  let determinant : Term × Term <- .toDsM "consistencyCheck determinant2"
               (match determinant.map (·.get_type) (·.get_type) with
                 | (Option.some x, Option.some x') =>
                   .some ([S' (eqs.length - fd.2 - 1)]x, [S' (eqs.length - fd.2 - 1)]x')
                 | _ => .none)

  -- assume coverage condition has been satisfied
  let should_build_η : Option Unit := determiners.foldl (λ acc x =>
    let (eq1, eq2) := x
    match (eq1, eq2) with
    | (.type (_ ~[_]~ t1), .type (_ ~[_]~ t2)) =>
       -- This check is very basic. Need to have some more intelligent check here?
      if t1 == t2 then .some () else .none
    | _ => .none
  ) (.some ())

  -- TODO: merge with top map
  match should_build_η with
  | .none => .error "determiners eqs error" -- one of the instance type is borked
  | _ => do
    let determiners_ηs <- determiners.mapM (λ x => do
      let (eq1, eq2) := x
      match (eq1, eq2) with
      | (.type (_ ~[k]~ t1), .type (_ ~[_]~ t2)) => -- the first components are β vars anyway
        .ok (.type ([P' teleA_tyvars.length]t1 ~[k]~ [P' teleA_tyvars.length]t2))
      | _ => .error "determiners ηs error"
      )

    let η := synth_coercion (determiners_ηs.reverse ++ Γ) determinant.1 determinant.2

    match η with
    | .some _ => .ok ()
    | .none => do
             let instA' <- un_inst_type instA
             let instB' <- un_inst_type instB
             .error ("instances violate functional dependency"
               ++ Std.Format.line ++ repr instA'
               ++ Std.Format.line ++ repr instB')

def doCoverageChecks (Γ : Ctx Term) (fds: List FunDep) : List (Term × Term) -> DsM Unit := λ x => .ok ()

def doConsistencyChecks (Γ : Ctx Term) (fds: List FunDep) : List (Term × Term) -> DsM Unit := λ x =>
  x.forM (λ p => do

    -- First do the overlapping checks
    let (instA, instB) := p
    -- Both the insts are henry forded
    -- ∀κs. (β1 ~ x) -> (β2 ~ y) -> F β1 β2
    -- so we un-henry ford them

    let instA <- un_inst_type instA
    let instB <- un_inst_type instB


    let (teleA, ret_tyA) := instA.to_telescope
    let (teleB, ret_tyB) := instB.to_telescope

    -- Make sure there is atleast one eq that is different
    let (_, spA) <- .toDsM "instA neutral From" ret_tyA.neutral_form
    let (_, spB) <- .toDsM "instB neutral From" ret_tyB.neutral_form
    if (spA.zip spB).all (λ x =>
      let (argA, argB) := x
      argA == argB)
          then .error ("overlapping instances"  ++
           Std.Format.line ++ repr instA ++
           Std.Format.line ++ repr instB)


    -- Now do the consistency checks
    fds.forM (λ fd => doConsistencyCheck Γ fd p))


-- compiling declarations
partial def compile_ctx : HsCtx HsTerm -> DsM (Ctx Term)
| [] => .ok []
| .cons .empty Γ => do
  let Γ' <- compile_ctx Γ
  .ok (.empty :: Γ')
| .cons (.kind k) Γ => do
  let Γ' <- compile_ctx Γ
  let k' <- compile Γ' □ k
  .ok (.kind k' :: Γ')
| .cons (.type τ) Γ => do
  let Γ' <- compile_ctx Γ
  let τ' <- compile Γ' ★ τ
  .ok (.type τ' :: Γ')
| .cons (.term A t) Γ => do
  let Γ' <- compile_ctx Γ
  let A' <- compile Γ' ★ A
  let t' <- compile Γ' A' t
  .ok (.term A' t' :: Γ')

| .cons (.datatypeDecl k ctors) Γ => do
  let Γ' <- compile_ctx Γ
  let k' <- compile Γ' □ k
  List.foldlM
    (λ Γ τ => do
      let τ' <- compile Γ ★ τ
      .ok ((.ctor τ') ::  Γ)
    )
    (.datatype k' :: Γ') ctors

-- Compiling Classes
| .cons (.classDecl C scs fds oms) Γ => do
  let Γ' <- compile_ctx Γ
  let C' <- compile Γ' □ C


  -- Step 1. Add the open type
  let Γ' := .opent C' :: Γ'

  -- Step 2. Add SC constraints
  -- Produce the sc openm
  let (args_k, _) <- .toDsMq C'.split_kind_arrow

  let ty_vars_ctx : Ctx Term := List.map (Frame.kind ·) args_k
  let ty_vars := fresh_vars args_k.length


  let Γ' <- List.foldlM ( λ Γ sc_data => do

    let cls_con := sc_data.1 -- the current class constructor

    let sc := sc_data.2 -- Superclass type
    let (sc_tycon, ty_args) <- .toDsMq sc.neutral_form -- Split it into ctor and ty_args

    let class_type := Term.mk_kind_apps_rev ([S' ty_vars.length]cls_con) ty_vars.reverse

    let sc' <- compile (ty_vars_ctx ++ Γ) ★ sc

    let sc_fun : Term :=  class_type -t> ([S]sc') -- [S] becuase -t> is binder
    let sc_fun := sc_fun.from_telescope_rev ty_vars_ctx

    .ok (.openm sc_fun :: Γ)
    ) Γ' (List.zip (re_index_base scs.length) scs)


  -- let class_arity := ty_vars_ctx.length

  -- Step 3. Add fundeps open methods
  let Γ' <- List.foldlM (λ Γ fd_data => do

    let cls_con := fd_data.1
    let fd := fd_data.2

    let determiners := fd.1

    let det1 := fd.2

    let det2 := 0 -- the new determinant is always the innermost

    if det1 < ty_vars_ctx.length && (List.all determiners (λ x => x < ty_vars_ctx.length))
       -- check that the fun dep is well scoped
    then do
      let ki <- .toDsMq (ty_vars_ctx d@ det1).get_type
      let ret_ty := (#(det1 + 1) ~[ki]~ #det2)


      let ty_vars_inner := ((ty_vars.map ([S]·)).modify det1 (λ _ => #det2)).reverse
      let cls_ty_inner := Term.mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars_inner

      let ret_ty := cls_ty_inner -t> [S] ret_ty

      let ty_vars_outer := (ty_vars.map ([S]·)).reverse
      let cls_ty_outer := Term.mk_kind_apps ([S' (scs.length + ty_vars.length + 1)] cls_con) ty_vars_outer

      let ret_ty := cls_ty_outer -t> [S] ret_ty
      -- TODO: What if the fundep is partial? also vary the irrelevant type vars?

      let t_fun := ret_ty.from_telescope_rev (.kind ki :: ty_vars_ctx)

      .ok (.openm t_fun :: Γ)


    else .error ("fundeps: " ++ repr Γ ++ repr fd_data)

  ) Γ' ((List.zip (re_index_base fds.length) fds))


  -- Step 4. Add methods
  let Γ' <- List.foldlM
    (λ Γ om_data => do
      let (idx, τ) := om_data
      let τ' <- compile Γ ★ τ
      let (Γ_l, ret_ty) := τ'.to_telescope
      let (Γ_tyvars, Γ_rest) := Γ_l.partition (λ x => x.is_kind)
      let class_ty := Term.mk_kind_apps (#(scs.length + fds.length + Γ_tyvars.length + idx))
                       (ty_vars.reverse.map ([S' (Γ_tyvars.length - ty_vars.length)] ·))
      let Γ_rest := Γ_rest.map (λ f => f.apply S)
      let Γ_l := Γ_tyvars ++ (.type class_ty :: Γ_rest)
      let ret_ty := [S] ret_ty

      let τ' := ret_ty.from_telescope Γ_l

      .ok ((.openm τ') :: Γ))
      Γ' (List.zip (Term.shift_helper oms.length) oms)

  .ok Γ'

-- Compile Instances
| .cons (.inst ity mths) Γ => do
  let Γ'  <- compile_ctx Γ

  -- Step1: Compile instance type
  -- ity is of the form C τs ⇒ D τs
  let ity_orig' <- compile Γ' ★ ity
  let (cls_idx , ity', β_count) <- mk_inst_type Γ' ity_orig'


  -- Step1 : Check fundeps validity

  -- First we need to get all the instances that belong to the class/opent that are
  -- in the context
  --
  let fundeps : List FunDep <- get_fundeps "compile instances" Γ' cls_idx

  let insts <- get_insts Γ' cls_idx
  let instss : List (Term × Term) := insts.map (λ x => (ity', x.2))

  -- TODO: Assume that the quantifiers do not mess things up (.i.e no constrained instances)
  -- 1. Coverage check
  doCoverageChecks Γ' fundeps instss
  -- 2. Consistency condition
  -- If the determiners are the the same, then the determinants can be "unified"
  -- Or a coercion can be produced
  doConsistencyChecks Γ' fundeps instss

  let Γ' := .insttype ity' :: Γ'

  let cls_idx := cls_idx + 1 -- account for insttype at head
  -- let instty_idx := 0

  let openm_ids <- get_openm_ids Γ' cls_idx
  -- open_ids are class omτs ++ sc omτ ++ fundeps omτ


  let (fd_ids, openm_ids) := openm_ids.partition (λ x =>
      let f := Γ' d@ x
      if f.is_openm then
        match f.get_type with
        | .some τ =>
          let (_, ret_ty) := Term.to_telescope τ;
          Option.isSome (is_eq ret_ty)
        | .none => false
      else false )


  let (sc_ids, openm_ids) := openm_ids.partition (λ x =>
       let f := Γ' d@ x
       if f.is_openm then
         match f.get_type with
         | .some τ =>
           let (tele, ret_ty) := Term.to_telescope τ;
           match ret_ty.neutral_form with
           | .none => true
           | .some (h, _) => (tele ++ Γ').is_opent h
         | .none => false
       else false)

  -- .error (repr cls_idx
  --        ++ repr fd_ids
  --        ++ repr sc_ids
  --        ++ repr openm_ids
  --        ++ repr Γ')

  -- Step2 : Add fundeps instances
  let Γ' <- List.foldlM (λ Γ fd_id => do

    let omτ <- .toDsM "get fd type"
               (Γ d@ (cls_idx - 1)).get_type
    let (Γ_l, ret_ty) := omτ.to_telescope

    -- fd openmethod is of the form: i.e. the varied tyvar is inner most ty var
    -- ∀αs t' F αs t -> F αs t' -> (t ~ t')
    let (Γ_tyvars, Γ_insts) := Γ_l.partition (λ x => x.is_kind)
    if Γ_insts.length == 2
    then
      match is_eq ret_ty with
      | .none => .error ("fd om broken" ++ repr omτ)
      | .some (_, #A, #B) =>
        let new_vars := (fresh_vars Γ_l.length).reverse
        let (ty_vars, inst_vars) := new_vars.splitAt Γ_tyvars.length

        let ty_vars_outer := ty_vars.take (ty_vars.length - 1) -- drop the last elem of the list
        -- let temp := (ty_vars.take (ty_vars.length - 1)).splitAt (ty_vars.length - 1) -- drop the last elem of the list

        let ty_vars_inner := ty_vars.take (ty_vars.length - 1)  -- drop the last elem of the list and put it up front
        let inst_1 : Frame Term <- .toDsM "inst 1 failed" (Γ_insts[0]?)
        let inst_1 <- .toDsMq inst_1.get_type

        let inst_2 : Frame Term <- .toDsM "inst 2 failed" (Γ_insts[1]?)
        let inst_2 <- .toDsMq inst_2.get_type
        let inst_2 := [P] inst_2 -- rebase it relative to Γ_tyvars

        let (h_1, τs_1) <- .toDsM ("inst_1 neutral form" ++ repr inst_1)
                           inst_1.neutral_form
        let (h_2, τs_2) <- .toDsM ("inst_2 neutral form" ++ repr inst_2)
                           inst_2.neutral_form

        -- find the index that differs in τs_1 and τs_2
        let idx_diff : List Nat :=
            ((List.zip (Term.shift_helper τs_1.length) (List.zip τs_1 τs_2)).foldl
              (λ acc x =>
                    if acc.isEmpty
                    then let (n, (t1, t2)) := x
                       if t1 == t2 then acc else [n]
                                   else acc) [])
        match idx_diff[0]? with
        | .none => .error ("index diff" ++ repr τs_1 ++ repr τs_2)
        | .some ι =>

          -- build the term from inside out
        let ty_vars_inner := ty_vars_inner.modify ι (λ _ => #inst_vars.length) -- set the determinant to the correct idx
        let instτ : Term <- .toDsM "fd gettype" ((Γ d@ fd_id).get_type)
        let instτ := ([S' Γ_l.length]instτ) -- shift to be relative to Γ_l ++ Γ


        -- TODO : find a fix for general case where some variables are locally bound in the instance
        -- constraint
        let outer_pat_tyvars := ty_vars_outer
        let guard_pat_outer := Term.mk_ty_apps #(fd_id + Γ_l.length) outer_pat_tyvars
        let inst_ty_outer <- .toDsM "instantate instτ outer" (instantiate_types instτ outer_pat_tyvars)
        let (Γ_instτ_outer, _) := inst_ty_outer.to_telescope

        let inner_pat_tyvars := ty_vars_inner.map ([S' Γ_instτ_outer.length] ·)
        let guard_pat_inner := Term.mk_ty_apps #(fd_id + Γ_l.length + Γ_instτ_outer.length) inner_pat_tyvars
        let inst_ty_inner <- .toDsM "instantiate instτ inner"
                             (instantiate_types ([S' Γ_instτ_outer.length]instτ) inner_pat_tyvars)
        let (Γ_instτ_inner, _) := inst_ty_inner.to_telescope

        -- ANI: I suspect there is an easier way to do it given that
        -- we have committed to do improvements everytime there is
        -- a lambda abstraction. I should be able to just call the compile function here?
        -- ANI Counter: Maybe not, as the compile function currently does not produce guards.
        -- and probably shouldn't to keep the term compilation complexity low


        let Γ_instτ_inner := Γ_instτ_inner.reverse
        let Γ_instτ_outer := Γ_instτ_outer.reverse

        let Γ_l := Γ_l.reverse

        let τ := [S' (Γ_instτ_inner.length + Γ_instτ_outer.length)]ret_ty

        let η <- synth_instance_coercion Γ (cls_idx + fd_id + Γ_l.length + Γ_instτ_outer.length + Γ_instτ_outer.length)
                 Γ_l Γ_instτ_outer Γ_instτ_inner τ

          -- let η := ([S' (Γ_instτ_inner ++ Γ_instτ_outer).length]ret_ty)

        let iterm <- .toDsM ("fd mk_lams inner pat") (η.mk_lams_rev Γ_instτ_inner)
        let iterm := .guard guard_pat_inner (#Γ_instτ_outer.length) iterm

        let iterm <- .toDsM ("fd mk_lams outer pat")
                         (Term.mk_lams_rev iterm Γ_instτ_outer)

        let iterm := .guard guard_pat_outer #1 iterm

        let iterm <- .toDsM ("fd mk_lams" ++ repr Γ_insts)
                            (Term.mk_lams_rev iterm Γ_l)

        let Γ_new := .inst #(cls_idx - 1) iterm :: Γ
        .ok Γ_new
      | _ => .error ("fd ret eq non variables" ++ repr omτ)

    else .error ("fd inst failure" ++ repr omτ)

  ) Γ' (Term.shift_helper fd_ids.length)


  -- Step 4: Compile superclass insts
  let Γ' <- List.foldlM (λ Γ sc_id => do

    let omτ <- .toDsM "sc get_type omτ" (Γ d@ (cls_idx - (1 + fd_ids.length))).get_type
    let (Γ_l, ret_ty) := omτ.to_telescope

    let (ty_args_ctx, _) := List.partition (λ x => Frame.is_kind x) Γ_l
    let new_vars := fresh_vars Γ_l.length
    let ty_vars : List Term := new_vars.reverse.take (ty_args_ctx.length)

    let g_pat := Term.mk_ty_apps #(sc_id + fd_ids.length + Γ_l.length) ty_vars
    let g_pat_ty <- .toDsM "sc get_type g_pat_ty" ((Γ_l ++ Γ) d@ (sc_id + fd_ids.length + Γ_l.length)).get_type
    let g_pat_ty <- .toDsM "sc inst type g_pat_ty" (instantiate_types g_pat_ty ty_vars)
    let (eqs, _) := g_pat_ty.to_telescope

    let t' <- .toDsM ("synth_sc_inst")
              (synth_superclass_inst (Γ_l  ++ Γ) ty_vars (([S' eqs.length] ret_ty).from_telescope eqs))
    let sc_fun <- .toDsM "sc insts mk_lams" (Term.mk_lams (Term.guard g_pat #0 t') Γ_l)
    let new_Γ := .inst #(cls_idx - (1 + fd_ids.length)) sc_fun :: Γ
    .ok new_Γ

  ) Γ' (Term.shift_helper sc_ids.length)

  let cls_idx := cls_idx + sc_ids.length

  -- Step3 : compile open method
  let Γ' <- if  mths.length == openm_ids.length -- insist on all methods being implemented
  then

    List.foldlM (λ Γ x => do
      let (mth, idx) := x

      let instty <- .toDsM "om instty" (Γ d@ (idx + sc_ids.length + fd_ids.length)).get_type

      let (Γ_inst, _) := instty.to_telescope
      let (Γ_tyvars, Γ_rest) := Γ_inst.partition (λ x => x.is_kind)
      let (Γ_tyvars_βs, Γ_tyvars_αs) := Γ_tyvars.splitAt β_count
      let (Γ_eqs, Γ_assms) := Γ_rest.partition (λ x =>
        match x with
        | .type x => (Option.isSome (is_eq x))
        | _ => false
        )

      let new_vars := (fresh_vars Γ_inst.length).reverse

      let (ty_vars, rest_new_vars) := new_vars.splitAt Γ_tyvars.length
      let (vars_eq, vars_assms) := rest_new_vars.splitAt Γ_eqs.length

      let (ty_vars_βs, ty_vars_αs) := ty_vars.splitAt β_count

      let Γ_local := Γ_inst.reverse

      /-  insttype is of the form ∀βs ∀αs. (βs ~ αs) -> C αs -> D βs
                   where C and D are opent's
          the openm type is of the form ∀βs A βs -> τs -> ret_τ
                   where A is an opent
          the inst binding type is of the form ∀δs B δs -> τs' -> ret_τ'

          the generated instance looks like
                  Λβs. λD βs
                    Guard #inst [βs] <- #0
                      Λαs. λ(βs ~ αs) λ C αs
                           mth[βs] γs ▹ η

                  where γ : B βs
                        η : ((τs' -> ret_τ)[δs ↦ βs]) ~ τs -> ret_τ
                  and γ and η are synthesized
      -/


      let omτ <- .toDsM "omτ get_type2" (Γ d@ (cls_idx - (1 + sc_ids.length + fd_ids.length))).get_type
      let omτ := [S' (Γ_local.length)] omτ
      let inst_omτ <- .toDsM ("instantate omτ"
                             ++ Std.Format.line ++ repr omτ
                             ++ Std.Format.line ++ repr ty_vars_βs
                             )
                             (instantiate_types omτ ty_vars_βs)
      let (omτ_assms, omτ_ret_ty) := to_implicit_telescope (Γ_local ++ Γ) inst_omτ
      -- TODO: make sure all omτ_assms (sans current instance constraints) are satisfied with the assumptions we have


      let (mth_τ', mth') <- match mth with
      | .HsAnnotate τ mth  => do
        let τ' <- compile Γ ★ τ
        let mth' <- compile Γ τ' mth
        .ok (τ', mth')
      | .HsVar n => do
        let τ' <- .toDsMq (Γ d@ n).get_type
        let mth' <- compile Γ τ' mth
        .ok (τ', mth')
      | _ => .error ("unsupported method decl: " ++ repr mth)

      let mth_τ' := [S' Γ_local.length] mth_τ'
      let mth_τ' <- .toDsM "instantate mth_τ"
                    (instantiate_types mth_τ' ty_vars_αs)

      let (Γ_mthτ'_θ, ret_mth_τ') := to_implicit_telescope (Γ_local ++ Γ) mth_τ'

      let mth' := [S' Γ_local.length] mth'


      let ctx_l := Γ_local ++ Γ

      -- TODO: omτ may give us more assumptions to be added into the context
      -- let omτ_assms' <- omτ_assms.tail.mapM (λ x => .toDsMq (x.get_type))
      -- let (_, inst_mth_assms) <- List.foldlM (λ acc τ => do
      --     let (ctx_l', ts) := acc
      --     let t <- DsM.toDsM ("") (synth_term ctx_l' τ)
      --     .ok ((Frame.empty :: ctx_l'), t :: ts)
      --     ) (ctx_l, []) omτ_assms'

      let mthτ'_θ <- Γ_mthτ'_θ.mapM (λ x => .toDsMq x.get_type)
      let (inst_mth_assms) <- List.foldlM (λ ts (idx, θτ) => do
          let θτ := [P' idx]θτ -- need all the implicit pred evidences relative to ctx_l
          let t <- .toDsM ("mth_θ synth_term"
                    ++ Std.Format.line ++ "θτ: " ++ repr θτ
                    ++ Std.Format.line ++ "ctx Γ: " ++ repr ctx_l
                    ++ Std.Format.line ++ "ts: " ++ repr ts
                   )
                   (synth_term ctx_l θτ)
          .ok (t :: ts)
          ) [] (List.zip (Term.shift_helper mthτ'_θ.length) mthτ'_θ)

      let mth' := Term.mk_ty_apps mth' ty_vars_αs

      let mth' := mth'.mk_apps inst_mth_assms

      -- TODO : apply mth' to the omτ assumptions?

      let Aτ := [P' Γ_mthτ'_θ.length]ret_mth_τ' -- rebase to ctx_l
      let Bτ := [P]omτ_ret_ty -- we take away the first omτ_assms as its the implicitly introduced class constraint
      let η <- .toDsM ("synth_coercion mth"
                        ++ Std.Format.line ++ "insttype: " ++ repr instty
                        ++ Std.Format.line ++ "omτ_assms: " ++ repr omτ_assms

                        ++ Std.Format.line ++ "Γ_inst_assms: " ++ repr Γ_assms ++ repr vars_assms
                        ++ Std.Format.line ++ "Γ_inst_eqs" ++ repr Γ_eqs ++ repr vars_eq
                        ++ Std.Format.line ++ "Γ_inst_αs: " ++ repr (Γ_tyvars.drop β_count)  ++ repr ty_vars_αs
                        ++ Std.Format.line ++ "Γ_inst_βs: " ++ repr (Γ_tyvars.take β_count) ++ repr ty_vars_βs
                        ++ Std.Format.line ++ "Γ: " ++ repr Γ

                        ++ Std.Format.line ++ "ctx Γ: " ++ repr ctx_l
                        ++ Std.Format.line  ++ "Eq: " ++ repr (Aτ ~[★]~ Bτ)
                        ++ Std.Format.line ++ "mth_τ': " ++ repr mth_τ'
                        ++ Std.Format.line ++ "omτ: " ++ repr omτ ++ " inst: " ++ repr inst_omτ
                        ++ Std.Format.line ++ "mth': " ++ repr mth'
                        ++ Std.Format.line ++ "cls_idx: " ++ repr cls_idx
                      )
                      (synth_coercion ctx_l Aτ Bτ)

      let mth' := mth' ▹ η

      -- let Γ_assms' := (Γ_assms.map (λ f => f.apply S)).reverse
      let mth' <- .toDsM ("Term.mk_lams Γ_assms" ++ repr mth' ++ Std.Format.line ++ repr Γ_assms)
                         (Term.mk_lams mth' Γ_assms)

      -- let Γ_eqs' := (Γ_eqs.map (λ f => f.apply S)).reverse
      let mth' <- .toDsM ("Term.mk_lams Γ_eqs" ++ repr mth' ++ Std.Format.line ++ repr Γ_eqs)
                         (Term.mk_lams mth' Γ_eqs.reverse)

      let mth' <- .toDsM ("Term.mk_lams Γ_eqs" ++ repr mth' ++ Std.Format.line ++ repr Γ_eqs)
                         (Term.mk_lams mth' Γ_tyvars_αs.reverse)

      let mth' := [S] mth' -- account for instance constraint

      let g_pat := Term.mk_ty_apps #(idx + sc_ids.length + fd_ids.length + ty_vars_βs.length + 1)
                           (ty_vars_βs.map ([P' (Γ_assms.length + ty_vars_αs.length)] ·))

      let mth' := Term.guard g_pat #0 mth'

      let cls_ty := (#(cls_idx + ty_vars_βs.length + idx)).mk_kind_apps
                           (ty_vars_βs.map ([P' (Γ_assms.length + ty_vars_αs.length + Γ_eqs.length)]· ))
      let mth' <- .toDsM ("Term.mk_lams" ++ repr mth'
                         ++ Std.Format.line ++ repr (.type cls_ty :: Γ_tyvars_βs).reverse)
                         (Term.mk_lams mth' (.type cls_ty :: Γ_tyvars_βs).reverse)

      let new_Γ := ((Frame.inst #(cls_idx - (1 + sc_ids.length + fd_ids.length)) mth') :: Γ)

      .ok new_Γ

    )  Γ' (List.zip mths (Term.shift_helper openm_ids.length))
  else .error ("Not all methods implemented" ++ repr mths ++ Std.Format.line ++ repr openm_ids)

  .ok Γ'

-- #eval instantiate_type (∀[★] ((#0 ~[★]~ #4) -t> #7 `@k #1)) #100
-- #eval [0,1].splitAt 1
-- #eval [0,1,2,3].take 3

-- #eval do
--   let (h, sp) <- (#0 `@t #1 `@t #2).neutral_form
--   let sp' : List Term := sp.map (λ x =>
--           let (_ , x') : (SpineVariant × Term) := x
--           x')
--   .some (Term.mk_ty_apps #h sp')
