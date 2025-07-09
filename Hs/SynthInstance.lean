
import SystemFD
import Hs.EqGraph
import Batteries.Data.List


-- Problem 2: producing a coercion
-- There is a term with a type `u : U` but the goal type is `V`
-- We need to try and find a coercion term `t : U ~ V` so that we can produce `u ▹ t : V`
-- The approach is two fold: refine the goal based off the structure of the coercion we need
--    and construct a graph of all possible coercions to search for a path from one type to another

-- For example, if we need `t : U1 -> U2 ~ V1 -> V2`, then we should immediately use the arrow coercion rule:
-- `?1 -c> ?2` with `?1 : U1 ~ V1` and `?2 : U2 ~ V2`
-- We also do this for the refl case

-- We use some semantic information to add instantiations of coercions (particularly for functional dependencies)
-- For example, if we know `u -> v` (u determines v) then we know that we ought to have three universally quantified
-- variables: `u`, `v1`, and `v2` with the equation `v1 ~ v2`
-- So, if we know that `F Int Bool` and `F Int b` then we "heuristically" produce the equation `Bool ~ b`
-- I say heuristically because you could imagine searching the context and producing all possible instantiations

-- For most situations when we are constructing instances it should be enough to just look at the available coercions
-- without having to do instantiations in the context.

-- The graph is constructed in the following way:
-- A coercion `t : U ~ V` becomes two edges `U -> V` with label `t` and `V -> U` with label `sym t`
-- A coercion `t : A B ~ C D` becomes two edges `A -> C` with label `t.1` and `B -> D` with label `t.2` (and of course the sym counterparts)
-- A coercion `t : ∀ K, A ~ B` searches for all instantiations of `K` and adds coercions recursively from there.

-- The instantiations are the worst issue here as it could theoretically explode.
-- A depth-first search is then run on the graph and the labels of the graph are returned.
-- These labels are joined by coercion sequencing: `t1 ; t2 ; ... ; tn` which produces the final coercion

-- TODO: Fix this, for now it assumes the argument list must be empty
def compute_argument_instantiation (_ : Ctx Term) : Ctx Term -> List (SpineVariant × Term)
| _ => []


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
    let (args, ret) := t.to_telescope
    let sp := compute_argument_instantiation Γ args
    match ret.apply_spine sp with
    | lhs ~[_]~ rhs =>
      let v := Term.apply_spine #n sp
      let edges := deconstruct_coercion_type Γ v lhs rhs
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
#eval synth_coercion ctx2 #4 #9


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
#eval construct_coercion_graph ctx4

#eval synth_coercion ctx4 (#7 `@k #3) (#7 `@k #4) -- Maybe b' ~ Maybe b
#guard synth_coercion ctx4 (#7 `@k #3) (#7 `@k #4) == .some ((refl! (★ -k> ★) #7) `@c ((refl! ★ #3) `;  #0))
#guard infer_type ctx4 ((refl! (★ -k> ★) #7) `@c ((refl! ★ #3) `;  #0)) ==
       .some ((#7 `@k #3) ~[★]~ (#7 `@k #4))

-- #eval synth_coercion ctx4 #6 (#7 `@k #4) -- u ~ Maybe b

#eval synth_coercion ctx4 #6 (#7 `@k #3) -- u ~ Maybe b'

#eval infer_type ctx4 ((((refl! ★ #6) `;  (#2 `;  ((sym! ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #1)))) `;
  (#1 `;  ((refl! (★ -k> ★) #7) `@c #0))) `; (sym! ((refl! (★ -k> ★) #7) `@c #0)))

 -- v ~ u
#guard synth_coercion ctx4 #5 #6 == .some ((refl! ★ #5) `;  ((#1 `;  ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #2)))
#guard infer_type ctx4 ((refl! ★ #5) `;  ((#1 `;  ((refl! (★ -k> ★) #7) `@c #0)) `;  (sym! #2))) == .some (#5 ~[★]~ #6)

#eval synth_coercion ctx4 #6 #5 -- u ~ v


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

-- #eval synth_term (ctx4.drop 2) (#4 ~[★]~ #9)
-- #eval synth_term (ctx4.drop 1) (#4 ~[★]~ #9) -- fails to produce coercion
-- #eval synth_coercion ctx4 (#18 `@k #5) (#18 `@k #10)

#eval synth_term ctx4 (#15 ~[★]~ #14)



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

-- def synth_instance (Γ : Ctx Term) (T : (Nat × List (SpineVariant × Term))) : Option Term := sorry
