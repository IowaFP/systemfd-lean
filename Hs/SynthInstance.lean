
import SystemFD
import Hs.EqGraph
import Batteries.Data.List
import Hs.Monad

set_option linter.unusedVariables false


@[simp]
def instantiate_type : Term -> Term -> Option Term
| (.bind2 .arrow _ t), _ => .some ([P] t)
| (.bind2 .all _ t), s
| (.bind2 .arrowc _ t), s =>
  .some (t β[s])
| _, _ => .none

@[simp]
def instantiate_types : Term -> List Term -> Option Term :=
  List.foldlM (λ acc s => instantiate_type acc s)


-- TODO: add coercions built from ∀[K] A ~[★]~ ∀[K] B
def deconstruct_coercion_type (Γ : Ctx Term) (t : Term) : Term -> Term -> List (Term × Term × Term)
| A1 `@k B1, A2 `@k B2 =>
  let K := infer_kind Γ B1
  match K with
  | .some K =>
    let c1 := deconstruct_coercion_type Γ (fst! K t) A1 A2
    let c2 := deconstruct_coercion_type Γ (snd! K t) B1 B2
    c1 ++ c2
  | .none => []
| #lhs, #rhs =>
  let klhs := infer_kind Γ #lhs
  let new_edges : List (Term × Term × Term) := ((Term.shift_helper Γ.length).zip Γ).flatMap (λ (i, f) =>
    match f with
    | .datatype k
    | .kind k =>
      match k.split_kind_arrow with
      | .some (.cons k' ks, ret_k) =>
        if k' == klhs then
          [((refl! k #i) `@c t , #i `@k #lhs, #i `@k #rhs)]
        else []
      | _ => []
    | _ => [])

  (t, #lhs, #rhs) :: (sym! t, #rhs, #lhs) :: new_edges.flatMap (λ (t, l, r) => [(t, l, r), (sym! t, r, l)])
| lhs, rhs => [(t, lhs, rhs), (sym! t, rhs, lhs)]


def discover_eqs (Γ : Ctx Term) (t : Term) : Term -> Term -> List (Term × Term × Term)
| A1 `@k B1, A2 `@k B2 =>
  let K := infer_kind Γ B1
  match K with
  | .some K =>
    let c1 := discover_eqs Γ (fst! K t) A1 A2
    let c2 := discover_eqs Γ (snd! K t) B1 B2
    c1 ++ c2
  | .none => []
| lhs, rhs => if rhs != lhs then [(t, lhs, rhs)] else []

def find_transitive_eqs (g :  EqGraph Term) : List (Nat × Nat × Term) :=
  let es := List.product g.edges g.edges
  let new_edges := es.foldl (λ acc (e1, e2) =>
      let (na1, na2, ηa) := e1
      let (nb1, nb2, ηb) := e2
      if na1 != nb2 && nb1 == na2
      then if
        (g.edges.filter (λ (x : Nat × Nat × Term) =>
          let (ea, eb, _) := x
          ea == na1 && eb == nb2)).isEmpty
        then (na1, nb2, (ηa `; ηb)) :: acc
        else acc
      else acc
      ) []
  new_edges


def construct_coercion_graph (Γ : Ctx Term) := (Term.shift_helper Γ.length).foldl (λ acc n =>
  match Γ d@ n with
  | .type t
  | .ctor t
  | .term t _ =>
    match t with
    | lhs ~[_]~ rhs =>
      let edges := deconstruct_coercion_type Γ #n lhs rhs
      let acc := List.foldl (λ g (l, s, t) => (g.add_edge l s t)) acc edges
      let more_edges := find_transitive_eqs acc

      let new_eqs := more_edges.map (λ e =>
        let (sn, tn, η) := e
        match (acc.nodes[sn]?, acc.nodes[tn]?) with
        | (.some τ1, .some τ2) => discover_eqs Γ η τ1 τ2
        | _ => []
      )
      new_eqs.flatten.foldl (λ g (l, s, t) => g.add_edge l s t) acc
    | _ => acc
  | _ => acc
  ) EqGraph.empty_graph


def synth_coercion (Γ : Ctx Term) : Term -> Term -> Option Term
| A1 `@k B1, A2 `@k B2 => do
  let ac <- synth_coercion Γ A1 A2
  let bc <- synth_coercion Γ B1 B2
  return ac `@c bc
| A1 -t> B1, A2 -t> B2 => do
  let ac <- synth_coercion Γ A1 A2
  let bc <- synth_coercion (.empty::Γ) B1 B2
  return ac -c> bc
| ∀[K1] A1, ∀[K2] A2 => do
  let ac <- synth_coercion (.kind K1 :: Γ) A1 A2
  if K1 == K2 then .some (∀c[K1] ac)
  else .none
| lhs, rhs => do
  let K <- infer_kind Γ lhs
  if lhs == rhs then return refl! K lhs
  let graph := construct_coercion_graph Γ
  let path <- graph.find_path_by_label (λ _ => false) lhs rhs
  List.foldlM (· `; ·) (refl! K lhs) path

#guard synth_coercion [.type (#0 ~[★]~ #3), .kind ★, .ctor #1,  .ctor #0, .datatype ★]
                      (#4 -t> #5 -t> #3) (#1 -t> #2 -t> #6)
       == .some ((refl! ★ #4) `; (sym! #0) -c> (refl! ★ #5) `; (sym! #1) -c> (refl! ★ #3) `; #2)


#guard synth_coercion [.type (#0 ~[★]~ #3), .kind ★, .ctor #1,  .ctor #0, .datatype ★] #4 #1
       == .some ((refl! ★ #4) `; sym! #0)
#guard synth_coercion [.type (#0 ~[★]~ #3), .kind ★, .ctor #1,  .ctor #0, .datatype ★] #1 #4
       == .some ((refl! ★ #1) `; #0)

#guard synth_coercion [.term (#0 ~[★]~ #3) #0, .kind ★, .ctor #1,  .ctor #0, .datatype ★] #1 #4
       == .some ((refl! ★ #1) `; #0)


def synth_coercion_dummy (_ : Ctx Term) : Term -> Term -> Option Term := λ a b => do
  .some (a ~[★]~ b)
def synth_term_dummy (_: Ctx Term) : Term -> Option Term := λ a => .some a

-- Synthesizes term of a given type, if one exists, and can be found
partial def synth_term (Γ : Ctx Term): Term -> Option Term := λ τ =>
match τ with
| .eq _ A B => synth_coercion Γ A B
| .bind2 .arrow givenτ wantedτ => do
  let kg <- infer_kind Γ givenτ
  let kw <- infer_kind Γ ([P]wantedτ)
  if kg == kw then
    let mb_η := synth_term Γ (givenτ ~[kg]~ [P]wantedτ)
    match mb_η with
    | .some η => .some (`λ[givenτ] #0 ▹ [S]η)
    | .none => -- TODO what tyvars do i need to use to instantiate omτ?
               -- ideally we need to pass it the caller function synth_term,
               -- but for now i have fixed them
               -- to be exactly the ones that givenτ has
      let (gh, gτs) <- ([S]givenτ).neutral_form -- make givenτ index with respect to (givenτ :: Γ)
      let (wh, wτs) <- wantedτ.neutral_form
      let gτs' <- List.mapM (λ x =>
         match x with
         | (.kind, τ) => .some τ
         | _ => .none
         ) gτs
      let wτs' <- List.mapM (λ x =>
         match x with
         | (.kind, τ) => .some τ
         | _ => .none
         ) wτs
      if gτs' != wτs' then .none
      -- TODO: what if the type variables are different? this may happen with fundeps
      let candidate_instances : List Term <- List.foldlM (λ acc idx =>
        match (.type givenτ :: Γ) d@ idx with
        | Frame.openm iτ => do
            -- iτ is of the form ∀αs. C αs → iτh αs
            match instantiate_types iτ wτs' with
            | .none => .some acc
            | .some iτ' => -- iτ is of the form C τs -> iτh τs
              let ((Γ_cτs, res_τ) : Ctx Term × Term) <- Term.to_telescope iτ'
              if ([S' Γ_cτs.length] wantedτ) == res_τ --
              then do
                let mb_ts : Option (List Term) :=
                  List.foldlM (λ (acc : List Term) (f : Frame Term × Nat) =>
                    match f with
                    | (Frame.type x, shift_idx) => do
                        let t <- synth_term Γ (givenτ -t> [P' shift_idx]x)
                            -- remember x is actually wrt (givenτ::Γ) so no [S]
                        .some (t :: acc)
                    | _ => .none
                  ) [] (Γ_cτs.zip (Term.shift_helper Γ_cτs.length))

                match mb_ts with
                | .some ts =>
                  .some ((`λ[givenτ] ((#idx).mk_ty_apps wτs').mk_apps (ts.map (λ t => ([S] t) `@ #0))) :: acc)
                | .none => .some acc
              else .some acc
         | _ => .some acc
         ) [] ((Term.shift_helper Γ.length).map (· + 1))
              -- start with 1 .. Γ.length + 1 as we have givenτ at head which
              -- will be abstracted over in the end

         if candidate_instances.length == 0 then .none
         -- else candidate_instances.head?
         else if candidate_instances.length == 1
              then candidate_instances.head?
              else .some (candidate_instances.foldl (· ⊕ ·) `0)
  else .none

| τ => do
     let (h, τs) <- τ.neutral_form
     let τs' <- List.mapM (λ x =>
         match x with
         | (.kind, τ) => .some τ
         | _ => .none
         ) τs

  -- solve for a very simple case where instance is readily available in the context
  -- try to find one instance with open type hτ
     let candidate_instances : List Term <- List.foldlM (λ acc idx =>
       match Γ d@ idx with
       | Frame.type iτ => do -- if we have an instance in our assumptions use it
         match iτ.neutral_form with
         | .none => .some acc
         | .some (h', iτs') =>
           if (h == h')
           then
             if iτs' == τs then .some (#idx :: acc)
             else do
               let mb_η := synth_coercion Γ iτ τ
               match mb_η with
               | .some η => .some ((#idx ▹ η) :: acc)
               | .none => .some acc
           else .some acc
       | Frame.insttype iτ => do
     -- iτ is of the form ∀τs. C τs → iτh τs
           match instantiate_types iτ τs' with
           | .none => .some acc
           | .some iτ' =>
             let ((Γ_eqs, res_τ) : Ctx Term × Term) <- Term.to_telescope iτ'
             if ([S' Γ_eqs.length] τ) == res_τ
             then do
               let mb_ηs : Option (List Term) :=
                 ((Term.shift_helper Γ_eqs.length).zip Γ_eqs).foldlM
                   (λ (ts : List Term) (f : Nat × Frame Term) =>
                   match f with
                   | (idx, Frame.type x) => do
                       let t <- synth_term Γ ([P' idx]x)
                       .some (t::ts)
                   | _ => .none
                 ) []
               match mb_ηs with
               | .some ηs =>
                 .some (((#idx).mk_ty_apps τs').mk_apps_rev ηs :: acc)
               | .none => .some acc
             else .some acc
        | _ => .some acc
        ) [] (Term.shift_helper Γ.length)

        if candidate_instances.length == 0 then .none
        -- else candidate_instances.head?
        else if candidate_instances.length == 1
             then candidate_instances.head?
             else .some (candidate_instances.foldl (· ⊕ ·) `0)


-- TODO: Can this be merged with synth_term?
def synth_superclass_inst (Γ : Ctx Term) : List Term -> Term -> Option Term := λ iτs ret_ty => do
  let cand_insts : List Term := List.foldl (λ acc idx =>
    match Γ d@ idx with
    | .insttype τ =>
      match instantiate_types τ iτs with
      | .none => acc
      | some τ' =>
        if τ' == ret_ty
        then (((#idx).mk_ty_apps iτs) :: acc)
        else
          let η := synth_coercion Γ τ' ret_ty
          match η with
          | .some η => (((#idx).mk_ty_apps iτs) ▹ η) :: acc
          | .none => acc
    | _ => acc
  )  [] (Term.shift_helper Γ.length)
  if cand_insts.length == 1 then cand_insts[0]?
  else if cand_insts.length >= 1 then .some (cand_insts.foldl (λ x y => x ⊕ y) `0) -- is this right?
  else .none

namespace SynthInstance.Test

def Γ : Ctx Term :=
  [ .term (#7 ~[★]~ #1) (#12 `@t #7 `@t #7 `@t #1 `@ (#4 `@t #7 `@t #7) `@ (refl! ★ #7) `@ (refl! ★ #7) `@ #0),
    .type (#12 `@k #6 `@k #0),
    .kind ★,
    .term (#4 -t> #5 -t> #6) (`λ[#4] `λ[#5] #5),
    .inst #8
      (Λ[★]Λ[★]Λ[★]`λ[#12 `@k #2 `@k #1]
      `λ[#13 `@k #3 `@k #1]
      .guard (#5 `@t #4 `@t #3) #1 (
          `λ[(#4 ~[★]~ #8)]
          `λ[(#4 ~[★]~ #9)]
          .guard (#7 `@t #6 `@t #4) #2 (
              `λ[(#6 ~[★]~ #10)]
              `λ[(#5 ~[★]~ #11)]
              (refl! ★ #7) `;
              #2 `;
              (sym! #0)))),
  .insttype (∀[★]∀[★](#1 ~[★]~ #4) -t> (#1 ~[★]~ #5) -t> #12 `@k #3 `@k #2),
  .ctor #1,
  .ctor #0,
  .datatype ★,
  .ctor #2,
  .ctor #1,
  .ctor #0,
  .datatype ★,
  .openm (∀[★]∀[★]∀[★]#3 `@k #2 `@k #1 -t> #4 `@k #3 `@k #1 -t> (#3 ~[★]~ #2)),
  .opent (★ -k> ★ -k> ★) ]

-- #eval mk_eq_graph Γ
-- #eval construct_coercion_graph Γ

#guard synth_coercion Γ (#8 -t> #9 -t> #10) (#2 -t> #3 -t> #4) == .some (((refl! ★ #8) `;  #0) -c> (((refl! ★ #9) `;  #1) -c> ((refl! ★ #10) `;  #2)))

#guard synth_term Γ ((#8 -t> #9 -t> #10) ~[★]~ (#2 -t> #3 -t> #4)) == .some (((refl! ★ #8) `;  #0) -c> (((refl! ★ #9) `;  #1) -c> ((refl! ★ #10) `;  #2)))

-- #eval synth_term Γ (#8 ~[★]~ #2) -- == .some ((refl!  ★ #8) `;  #0)
#guard synth_term Γ (#8 ~[★]~ #2) == .some ((refl!  ★ #8) `;  #0)

#guard synth_coercion Γ (#8 -t> #9) (#2 -t> #3) == .some (((refl! ★ #8) `;  #0) -c> ((refl! ★ #9) `;  #1))


def ctx0 : Ctx Term := [
 .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
 .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
 .opent (★ -k> ★),
 .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
 .opent (★ -k> ★),
 .datatype ★ ]
#guard wf_ctx ctx0 == .some ()

#guard synth_term ctx0 (#4 `@k #5) == .some (#3 `@t #5 `@ (refl! ★ #5))
-- #eval synth_term ctx0 (#2 `@k #5 -t> #3 `@k #6)

#guard infer_type ctx0 (`λ[#2 `@k #5] (#0 ▹ (refl! (★ -k> ★) #3 `@c (refl! ★ #6))) ) == .some ((#2 `@k #5) -t> (#3 `@k #6))

#guard synth_term ctx0 (#2 `@k #5 -t> #3 `@k #6) == .some (`λ[#2 `@k #5] (#0 ▹ (refl! (★ -k> ★) #3 `@c (refl! ★ #6))))

#guard (do let t <- synth_term ctx0 (#2 `@k #5 -t> #5 `@k #6)
           infer_type ctx0 t) == .some (#2 `@k #5 -t> #5 `@k #6)


#guard infer_type (.type (#2 `@k #5) :: ctx0) (#2 `@t #6) == .some ((#3 `@k #6) -t> (#6 `@k #7))

#guard infer_type (.type (#2 `@k #5) :: ctx0) ((`λ[#3 `@k #6] (#0 ▹  (refl! (★ -k> ★) #4) `@c (refl! ★ #7))) `@ #0) ==
       .some (#3 `@k #6)

-- #eval do let x <- synth_term ctx0 (#2 `@k #5 -t> #5 `@k #6)
--          infer_type ctx0 x
-- #guard synth_term ctx0 (#2 `@k #5) == .some (#0 `@t #5 `@ (refl! ★ #5))
-- #guard synth_term [.type (#2 `@k #3), .type (#1 `@k #0), .kind ★, .opent (★ -t> ★), .datatype ★] (#3 `@k #2) == .some #1

def ctx1 : Ctx Term := [
 .type (#3 `@k #0),  -- Telescope of open method
 .kind ★,            --
 .insttype (∀[★] (#0 ~[★]~ #5) -t> (#3 `@k #6)),
 .openm (∀[★] (#1 `@k #0) -t> (#4 `@k #1)),
 .opent (★ -k> ★),
 .insttype (∀[★](#0 ~[★]~ #2) -t> (#2 `@k #3)),
 .opent (★ -k> ★),
 .datatype ★ ]
#guard wf_ctx ctx1 == .some ()

#guard synth_term ctx1 (#4 `@k #1) == .some #0
#guard synth_term [.type (#13 `@k #1)] (#14 `@k #2) == .some #0

#guard synth_superclass_inst ctx1 [#1] (#1 ~[★]~ #7 -t> #7 `@k #8) == (#5 `@t #1)


def ctx2 : Ctx Term := [
 .type (#15 `@k #3 `@k #2),
 .type (#10 ~[★]~ (#13 `@k #1)), -- c ~ Maybe b''
 .type (#11 ~[★]~ (#12 `@k #1)), -- a ~ Maybe a''
 .kind (★), -- b''
 .kind (★), -- a''
 .type (#10 `@k #3 `@k #2),
 .type (#6 ~[★]~ (#8 `@k #1)), -- b ~ Maybe b'
 .type (#6 ~[★]~ (#7 `@k #1)), -- a ~ Maybe a'
 .kind (★), -- b'
 .kind (★), -- a'
 .type (#5 `@k #3 `@k #1),
 .type (#4 `@k #2 `@k #1),
 .kind (★), -- c
 .kind (★), -- b
 .kind (★), -- a
 .datatype (★ -k> ★), -- Maybe
 .opent (★ -k> ★ -k> ★) -- F
]

#guard wf_ctx ctx2 == .some ()
-- #eval construct_coercion_graph ctx2
#guard (synth_coercion ctx2 #4 #9) == .some ((refl! ★ #4) `;  (snd! ★ ((sym! #2) `;  #7)))
#guard (infer_type ctx2 ((refl! ★ #4) `;  (snd! ★ ((sym! #2) `;  #7)))) == .some (#4 ~[★]~ #9)

def ctx3 : Ctx Term := [
 .type (#3 ~[★]~ (#4 `@k #0)), -- a ~ Maybe a''
 .kind ★, -- a''
 .type (#1 ~[★]~ (#2 `@k #0)), -- a ~ Maybe a'
 .kind ★, -- a'
 .kind ★, -- a
 .datatype (★ -k> ★), -- Maybe
]

#guard wf_ctx ctx3 == .some ()
#guard synth_coercion ctx3 #1 #3 == .some ((refl! ★ #1) `;  (snd! ★ ((sym! #0) `;  #2)))
#guard infer_type ctx3 ((refl! ★ #1) `;  (snd! ★ ((sym! #0) `;  #2))) == .some (#1 ~[★]~ #3)


def ctx4 : Ctx Term := [
  .type (#2 ~[★]~ #3), -- b ~ b'
  .type (#3 ~[★]~ (#5 `@k #1)), -- v ~ Maybe b'
  .type (#3 ~[★]~ (#4 `@k #1)), -- u ~ Maybe b
  .kind ★, -- b'
  .kind ★, -- b
  .kind ★, -- v
  .kind ★, -- u
  .datatype (★ -k> ★)
  ]
#guard wf_ctx ctx4 == .some ()
-- #eval construct_coercion_graph ctx4

-- #eval synth_coercion ctx4 (#7 `@k #3) (#7 `@k #4) -- Maybe b' ~ Maybe b
#guard synth_coercion ctx4 (#7 `@k #3) (#7 `@k #4) == .some ((refl! (★ -k> ★) #7) `@c ((refl! ★ #3) `;  #0))
#guard infer_type ctx4 ((refl! (★ -k> ★) #7) `@c ((refl! ★ #3) `;  #0)) ==
       .some ((#7 `@k #3) ~[★]~ (#7 `@k #4))

-- #eval synth_coercion ctx4 #6 (#7 `@k #4) -- u ~ Maybe b

-- #eval synth_coercion ctx4 #6 (#7 `@k #3) -- u ~ Maybe b'

#guard infer_type ctx4 ((((refl! ★ #6) `;  (#2 `;  ((sym! ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #1)))) `;
  (#1 `;  ((refl! (★ -k> ★) #7) `@c #0))) `; (sym! ((refl! (★ -k> ★) #7) `@c #0))) == .some (#6 ~[★]~ (#7 `@k #3))

 -- v ~ u
#guard synth_coercion ctx4 #5 #6 == .some ((refl! ★ #5) `;  ((#1 `;  ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #2)))
#guard infer_type ctx4 ((refl! ★ #5) `;  ((#1 `;  ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #2))) == .some (#5 ~[★]~ #6)

#guard synth_coercion ctx4 #6 #5 == .some ((refl! ★ #6) `;  (#2 `;  ((sym! ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #1))))
#guard infer_type ctx4 ((refl! ★ #6) `;  (#2 `;  ((sym! ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #1)))) ==
       .some (#6 ~[★]~ #5)

end SynthInstance.Test


namespace SynthInstTest

def ctx : Ctx Term := [
 .type (#13 `@k #1),
 .type (#1 ~[★]~ #6 `@k #0),
 .kind ★,
 .kind ★,
 .insttype (∀[★]∀[★](#1 ~[★]~ #5 `@k #0) -t> #12 `@k #1 -t> #13 `@k #3) ,
 .term #13 #11,
 .ctor (∀[★]#0 -t> #3 `@k #1),
 .ctor (∀[★]#1 `@k #0),
 .datatype (★ -k> ★),
 .inst #2 (
      Λ[★]`λ[#5 `@k #0]
      .guard (#3 `@t #1) #0 (
          `λ[(#1 ~[★]~ #11)]
          ((`λ[#12] (`λ[#13] (#11 `@ ((#10 `@ #0) `@ #1)))) ▹
           (((refl! ★ #12) `;  (sym! #0)) -c> (((refl! ★ #13) `;  (sym! #1)) -c> (refl! ★ #14)))))),
 .inst #2 (
      Λ[★]`λ[#4 `@k #0]
      .guard (#2 `@t #1) #0 (
          `λ[(#1 ~[★]~ #10)]
          (#7 ▹  (((refl! ★ #11) `;  (sym! #0)) -c> (((refl! ★ #12) `;  (sym! #1)) -c> (refl! ★ #13)))))),
 .insttype (∀[★](#0 ~[★]~ #8) -t> #4 `@k #1),
 .openm (∀[★]#2 `@k #0 -t> #1 -t> #2 -t> #10),
 .openm (∀[★]#1 `@k #0 -t> #1 -t> #2 -t> #9),
 .opent (★ -k> ★),
 .term #2 #3,
 .term #2 #0,
 .ctor #1,
 .ctor #0,
 .datatype ★
 ]

#guard synth_term ctx (#14 `@k #2) == .some #0
#guard infer_type ctx #0 == .some (#14 `@k #2)

-- Test for improvements
  def Γ1 : Ctx Term := [
  .type (#12 `@k #6 `@k #0),
  .kind ★,
  .term (#4 -t> #5 -t> #6) (`λ[#4] `λ[#5] #5),
  .inst #8
    (Λ[★]Λ[★]Λ[★]`λ[#12 `@k #2 `@k #1]
      `λ[#13 `@k #3 `@k #1]
      .guard (#5 `@t #4 `@t #3) #1 (
          `λ[(#4 ~[★]~ #8)]
          `λ[(#4 ~[★]~ #9)]
          .guard (#7 `@t #6 `@t #4) #2 (
              `λ[(#6 ~[★]~ #10)]
              `λ[(#5 ~[★]~ #11)]
              (refl! ★ #7) `;
              #2 `;
              (sym! #0)))),
 .insttype (∀[★]∀[★](#1 ~[★]~ #4) -t> (#1 ~[★]~ #5) -t> #12 `@k #3 `@k #2),
 .ctor #1,
 .ctor #0,
 .datatype ★,
 .ctor #2,
 .ctor #1,
 .ctor #0,
 .datatype ★,
 .openm (∀[★]∀[★]∀[★]#3 `@k #2 `@k #1 -t> #4 `@k #3 `@k #1 -t> (#3 ~[★]~ #2)),
 .opent (★ -k> ★ -k> ★)]

#guard synth_term Γ1 (#13 `@k #7 `@k #1) == .some #0
#guard infer_type Γ1 #0 == .some (#13 `@k #7 `@k #1)

#guard synth_term Γ1 (#13 `@k #7 `@k #7) == .some ((#4 `@t #7 `@t #7 `@ (refl! ★ #7)) `@ (refl! ★ #7))
#guard infer_type Γ1 ((#4 `@t #7 `@t #7 `@ (refl! ★ #7)) `@ (refl! ★ #7)) == .some (#13 `@k #7 `@k #7)




def ctx4 : Ctx Term := [

 .type (#4 ~[★]~ #9),
 .type (#4 ~[★]~ #9),

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

#guard (wf_ctx ctx4) == .some ()
-- #eval construct_coercion_graph ctx4

-- #eval synth_term ctx4 (#15 ~[★]~ #14)

end SynthInstTest


-- Problem 1: filling in a hole
-- There is a goal that is an instance, say `C a b c`
-- We need to synthesize the evidence of this instance
-- Suppose the problem looks like this:

-- `class A; class B; class C; f : ∀ b c, B b c -> A b; g : ∀ a b c, A a -> C a b c; a; b; c; x : B a b ⊢ ? : C a b c`

-- First lets change the context to compute the telescopes:
-- `class A; class B; class C; f : (A b, [b, c, B b c]); g : (C a b c, [a, b, c, A a]); a; b; c; x : B a b ⊢ ? : C a b c`

-- Now we will exhaustively try every contextual telescope that matches the goal, in this case this is only one:
-- `Γ ⊢ g ?1 ?2 ?3 ?4` this produces four new goals, but it forces a = a, b = b, and c = c in the telescope

-- That means that `?1 = a`, `?2 = b`, and `?3 = c`, hence:
-- `Γ ⊢ g a b c ?4` with the goal: `Γ ⊢ ?4 : A a`

-- Now we recurse, exhaustively trying every contextual telescope that matches the goal, in this case this is only one:
-- `Γ ⊢ f ?5 ?6 ?7` this produces three new goals, but it forces b = a in the telescope

-- That means `?5 = a` giving us: `Γ ⊢ f a ?6 ?7`
-- Now we work on the _largest_ goal because it has the best chance of forcing other goals
-- We have: `Γ ⊢ ?7 : B a c` (note this c is indexed in the telescope, not the context)

-- Repeating the process again we get: `?7 = x` where `a = a` matches in the context, and it forces `c = b`
-- This gives us: `Γ ⊢ f a b x : A a` and finally `Γ ⊢ g a b c (f a b x) : C a b c`

  -- EqMaybe : ∀ t u. t ~ Maybe u → Eq u → Eq t
  -- Eq (Maybe Int) <- Goal
  -- t => Maybe Int -- Matching the goal type
  -- ∀ u. Maybe Int ~ Maybe u -> Eq u
  -- u  => Int -- Matching the coercion lhs & rhs
  -- Maybe Int ~ Maybe Int -> Eq Int
  -- refl @ refl -- by coercion synthesis
  -- Eq Int -- recurse

  -- match the goal type with the required type
  --     this ought to force all the "universally quantified variables"
  -- iterate over coercions, trying to find more forced stuff
  --     this ought to force all the "existentially quantified variables"
  --     might need to repeat this to compute a fixed point
  -- recurse on instance assumptions

-- surface: datatype Bool (tt, ff); #0 = ff, #1 = tt, #2 = Bool <-- defined by hs_nth


@[simp]
def fresh_vars_aux : Nat -> List Term -> List Term
| 0, acc => acc
| n + 1, acc => fresh_vars_aux n (#n :: acc)

@[simp]
def fresh_vars : Nat -> List Term := λ n => fresh_vars_aux n []
@[simp]
def re_index_base := fresh_vars

#eval fresh_vars 3


-- Get all the open methods for a given term
/- Caution: The ids themselves are meaningless (sort of),
  just depend on the size of the list. thats the width of the class-/
@[simp]
def get_openm_ids (Γ : Ctx Term) (cls_idx : Nat) : DsM (List Nat) :=
  if (Γ.is_opent cls_idx)
  then
    let ids := ((Term.shift_helper Γ.length).take cls_idx).reverse
    .ok ((ids.takeWhile (Γ.is_openm ·)).reverse)
  else .error ("get_open_ids" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr cls_idx)

-- Get all the instances for a given opent
@[simp]
def get_insts (Γ : Ctx Term) (cls_idx : Nat) : DsM (List (Nat × Term)) := do
  if (Γ.is_opent cls_idx)
  then
    let ids := ((Term.shift_helper Γ.length).take cls_idx).reverse
    .ok (ids.foldl (λ acc i =>
    match (Γ d@ i) with
    | .insttype iτ =>
      let (Γ_l, ret_ty) := iτ.to_telescope
      match (ret_ty.neutral_form) with
      | .none => acc
      | .some (h, _) => if h == Γ_l.length + cls_idx then ((i, iτ) :: acc) else acc
    | _ => acc
    ) [])
  else .error ("get_inst_ids" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr cls_idx)

abbrev FunDep := (List Nat) × Nat

def get_fundep_ids (Γ : Ctx Term) (cls_idx : Nat) : DsM (List Nat) :=
  if Γ.is_opent cls_idx
  then do
    let ids := ((Term.shift_helper Γ.length).take cls_idx).reverse
    let fd_ids := ids.foldl (λ acc i =>
      match (Γ d@ i) with
      | .openm mτ =>
        let (Γ_l, ret_ty) := mτ.to_telescope
        let (Γ_tyvars, Γ_assms) := Γ_l.partition (·.is_kind)
        if Γ_assms.length == 2
        then
          match Γ_assms with
          | .cons (.type τ1) (.cons (.type τ2) .nil) =>
            let τ1nf := τ1.neutral_form
            let τ2nf := τ2.neutral_form
            match (τ1nf, τ2nf) with
            | (.some (h1, _), .some (h2, _)) =>
              if h1 + 1 == h2 && h1 == cls_idx + Γ_tyvars.length
                && Option.isSome (is_eq ret_ty)
              then (i :: acc) else acc
            | _ => acc
          | _ => acc
        else acc
      | _ => acc
      ) []
    .ok fd_ids
  else .ok []


def get_fundeps (pfix : Std.Format) (Γ : Ctx Term) (cls_idx : Nat) : DsM (List FunDep) :=
  if Γ.is_opent cls_idx
  then do
      let ids := ((Term.shift_helper Γ.length).take cls_idx).reverse
      let fd_oms := ids.foldl (λ acc i =>
      match (Γ d@ i) with
      | .openm mτ =>
        let (Γ_l, ret_ty) := mτ.to_telescope
        if Option.isSome (is_eq ret_ty)
        then (mτ :: acc) else acc
      | _ => acc
      ) []
      -- each fd_om is of the form ∀αs. F αs -> F αs' -> α ~ α'
      --
      fd_oms.foldlM (λ acc τ => do
        let (tele, _) := τ.to_telescope
        let (tele_tyvars, tele_cls) := tele.partition (·.is_kind)
        if tele_cls.length != 2 then .error (pfix ++ " get_fundeps error") else

        let cls1 <- .toDsMq tele_cls[0]? -- F αs
        let cls1 : Term <- .toDsMq cls1.get_type
        let cls2 <- .toDsMq tele_cls[1]? -- F αs'
        let cls2 : Term <- .toDsMq cls2.get_type

        -- TODO: But what if we have a partial fundep?
        let det_idx : Option Nat :=
          match (([S] cls1).neutral_form, cls2.neutral_form) with
          | (Option.some (_, αs), Option.some (_, αs')) =>
              (List.zip αs αs').findIdx (λ (x : ((SpineVariant × Term) × (SpineVariant × Term))) =>
                match x with
                | ((.kind, t1), (.kind, t2)) => if t1 == t2 then false else true
                | _ => false)
            -- .some 0
          | _ => .none

          match det_idx with
          | Option.some determinant =>
            -- TODO: But what if we have a partial fundep?
            let determiners := (Term.shift_helper (tele_tyvars.length - 1)).filter (λ x => x != determinant)
            if determinant < tele_tyvars.length then .ok ((determiners, determinant) :: acc)
            else .error ("cannot find determinant for class" ++ repr cls_idx ++ " det_idx:" ++ repr det_idx)
          | .none => .error ("cannot find determinant for class" ++ " det_idx:" ++ repr det_idx)
        ) []
  else
  .error (pfix ++ " get_fundeps not class id" ++ Std.Format.line ++ repr Γ ++ Std.Format.line ++ repr cls_idx)



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


namespace SynthInst.Test


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


#eval DsM.run (synth_instance_coercion (ctx4.drop 15) 19 ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#3 ~[★]~ #8))

#guard (do let η <- synth_instance_coercion (ctx4.drop 15) 19
                       ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#3 ~[★]~ #8)
           .toDsMq (infer_type ctx4 η)
              ) == .ok (#3 ~[★]~ #8)

#eval DsM.run (synth_instance_coercion (ctx4.drop 15) 19 ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#13 ~[★]~ #12))

#guard (do let η <- synth_instance_coercion (ctx4.drop 15) 19
                ((ctx4.drop 10).take 5) ((ctx4.drop 5).take 5) (ctx4.take 5) (#13 ~[★]~ #12)
           .toDsMq (infer_type ctx4 η)) == .ok (#13  ~[★]~ #12)


end SynthInst.Test



partial def try_type_improvement (Γ : Ctx Term) : Nat -> DsM (List (Term × Term)) := λ i => do
let τ <- .toDsM "try_type_impr" (Γ d@ i).get_type
let Γ_local_tyvars := Γ.tail.takeWhile (·.is_kind)
let local_tyvars := (fresh_vars Γ_local_tyvars.length).reverse.map ([S]·)
match τ.neutral_form with
| .some (τh, τs) => do
  if not (Γ.is_opent τh) then .ok [] else
  -- get all the fundep open method indices
  -- .ok ((fd_ids.zip fd_ids).map (λ x => (#x.1, #x.2)))
  let fd_ids <- get_fundep_ids Γ τh

  -- find all the available instances of the opentype
  let insts <- get_insts Γ τh
  -- .ok ((inst_ids.zip inst_ids).map (λ x => (#x.1, #x.2)))
  -- Extract the type instances

  -- TODO: assuming that I do not have any quantified types.
  -- That would require some more work

  let new_eqs : List (Term × Term) <- insts.foldlM (λ acc x => do
    let (idx, iτ) := x
    let τs := τs.map (·.2)
    -- find the types that this instance type is applied to
    let (Γ_iτ, ret_τ) := iτ.to_telescope
    let (Γ_tyvars, Γ_assms) := Γ_iτ.partition (λ x => x.is_kind)

    -- let (_, ret_τ_τs) <- .toDsM "ret_τ neutral form try_type_improvement" ret_τ.neutral_form
    if Γ_tyvars.length != Γ_assms.length
    then .error ("quantified instances are not supported for fundeps (yet)"
         ++ Std.Format.line ++ "Γ_assms: " ++ repr Γ_assms
         ++ Std.Format.line ++ "Γ_tyvars: " ++ repr Γ_tyvars
         ++ Std.Format.line ++ "Γ: " ++ repr Γ
         )

    let inst_τs : (List Term) := ((Term.shift_helper Γ_assms.length).zip Γ_assms).foldl
      (λ (acc : List Term) (x : Nat × Frame Term) =>
      match x with
      | (si, .type x) =>
        match (is_eq x) with
        -- all (A ~ B) in inst types have first tyvar as β bound, second tyvar the actual type instance
        | .some (_, _, B) => ([P' (si + Γ_tyvars.length)]B) :: acc -- reindex it wrt input Γ
        | _ => acc
      | _ => []) []

    let inst_τs := inst_τs.reverse
    -- instantiate the fd function with the inst_τs
    let fd_terms <- fd_ids.mapM (λ fd_id => do
      let t := Term.mk_ty_apps #fd_id inst_τs
      let fd_τ <- .toDsM "fd_τ get_type" (Γ d@ fd_id).get_type
      let τ <- .toDsM "fd_τ instantiate types" (instantiate_types fd_τ inst_τs)
      .ok (τ, t)
      )

    -- .error (repr fd_terms)
    -- instantiate the fd_terms with the free vars in the context (Γ_tyvars)
    let fd_terms <- fd_terms.mapM (λ x => do
       let t := Term.mk_ty_apps x.2 local_tyvars
       let fd_τ <- .toDsM "fd_τ instantiate types 2" (instantiate_types x.1 local_tyvars)
       .ok (fd_τ, t)
    )

    -- synthesize all the arguments to the fd_open method to get all the equalities
    let fd_terms <- fd_terms.mapM (λ x => do
      let τ := x.1
      let t := x.2
      let (Γ_tele, ret_ty) := τ.to_telescope

      ((Term.shift_helper Γ_tele.length).zip Γ_tele).foldlM (λ acc x => do
        let (τ, t) := acc
        match x with
        | (idx, .type argτ) =>
          let argτ := [P' idx] argτ -- make τ wrt input Γ
          let arg <- .toDsM ("synth_term failed in fd_terms"
                  ++ Std.Format.line ++ "argτ: " ++ repr argτ
                  ++ Std.Format.line ++ "rn argτ: " ++ repr ([P' idx]argτ)
                  ++ Std.Format.line ++ "iτ: " ++ repr iτ
                  ++ Std.Format.line ++ "Γ: " ++ repr Γ
                  ++ Std.Format.line ++ "t: " ++ repr t
                  ++ Std.Format.line ++ "τ: " ++ repr τ
                  ++ Std.Format.line ++ "inst_τs: " ++ repr insts ++ repr inst_τs
                  ++ Std.Format.line ++ "tyvars: " ++ repr Γ_local_tyvars ++ repr local_tyvars
                  ++ Std.Format.line ++ "acc: " ++ repr acc
                  ) (synth_term Γ argτ)
          let τ' <- .toDsM "instantiate types failed in fd_terms" (instantiate_type τ argτ)
          let t' := t `@ arg
          .ok (τ', t')
        | _ => .error ("urk! fd_term not instantiated completely")
      ) (τ, t)

    )

    .ok (fd_terms ++ acc)
    ) []
  .ok (new_eqs)
  -- .ok []

-- No type improvements possible
| _ => .ok []


namespace TypeImpr.Test

-- Test for improvements
  def Γ1 : Ctx Term := [
  .type (#12 `@k #6 `@k #0),
  .kind ★,
  .term (#4 -t> #5 -t> #6) (`λ[#4] `λ[#5] #5),
  .inst #8
    (Λ[★]Λ[★]Λ[★]`λ[#12 `@k #2 `@k #1]
      `λ[#13 `@k #3 `@k #1]
      .guard (#5 `@t #4 `@t #3) #1 (
          `λ[(#4 ~[★]~ #8)]
          `λ[(#4 ~[★]~ #9)]
          .guard (#7 `@t #6 `@t #4) #2 (
              `λ[(#6 ~[★]~ #10)]
              `λ[(#5 ~[★]~ #11)]
              (refl! ★ #7) `;
              #2 `;
              (sym! #0)))),
 .insttype (∀[★]∀[★](#1 ~[★]~ #4) -t> (#1 ~[★]~ #5) -t> #12 `@k #3 `@k #2),
 .ctor #1,
 .ctor #0,
 .datatype ★,
 .ctor #2,
 .ctor #1,
 .ctor #0,
 .datatype ★,
 .openm (∀[★]∀[★]∀[★]#3 `@k #2 `@k #1 -t> #4 `@k #3 `@k #1 -t> (#3 ~[★]~ #2)),
 .opent (★ -k> ★ -k> ★)]

 #guard wf_ctx Γ1 == .some ()

 -- #eval DsM.run (try_type_improvement Γ1 0)
 #guard try_type_improvement Γ1 0 == .ok
       [(#7 ~[★]~ #1,
         (#12 `@t #7 `@t #7 `@t #1) `@ (((#4 `@t #7 `@t #7) `@ (refl! ★ #7)) `@ (refl! ★ #7)) `@ #0)]

--  #eval get_fundeps "type impr test" Γ1 13
--  #guard (try_type_improvement Γ1 (#12 `@k #6 `@k #0)) == .ok ([(#6 ~[★]~ #0, #11 `@t #6 `@t #0 )])
 #eval infer_type Γ1 (#12 `@t #7 `@t #1 `@t #7 `@ #0)


def Γ2 : Ctx Term := [.type (#12 `@k #13 `@k #0),
 .kind (★),
 .term (#4 -t> #5) (`λ[#4] .ite #4 #0  #3 #4),
 .inst #8
      (Λ[★]Λ[★]Λ[★]`λ[#12 `@k #2 `@k #1]
       `λ[#13 `@k #3 `@k #1]
       .guard (#5 `@t #4 `@t #3) #1 (
           `λ[#4 ~[★]~ #15]
           `λ[#4 ~[★]~ #9]
           .guard (#7 `@t #6 `@t #4) #2 (
               `λ[#6 ~[★]~ #17]
               `λ[#5 ~[★]~ #11]
               (refl! ★ #7) `;
               #2 `;
               (sym! #0)))),
 .insttype (∀[★]∀[★](#1 ~[★]~ #11) -t> (#1 ~[★]~ #5) -t> #12 `@k #3 `@k #2),
 .ctor (#1),
 .ctor (#0),
 .datatype (★),
 .ctor (#2),
 .ctor (#1),
 .ctor (#0),
 .datatype (★),
 .openm (∀[★]∀[★]∀[★]((#3 `@k #2) `@k #1) -t> ((#4 `@k #3) `@k #1) -t> #3 ~[★]~ #2),
 .opent (★ -k> ★ -k> ★),
 .datatype (★)]
 #eval DsM.run (try_type_improvement Γ2 0)

end TypeImpr.Test
