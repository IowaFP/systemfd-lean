import Hs.SynthInstance


theorem coercion_graph_kind_soundness (Γ : Ctx Term) :
  ⊢ Γ ->
  Γ ⊢ A : k ->
  Γ ⊢ B : k ->
  construct_coercion_graph Γ = g ->
  g.find_path_by_label A B = .some w ->
  ∀ x ∈ w, Γ ⊢ x : k := sorry
-- what does w satsify?
-- what does it mean for a list of nodes to be a path?

theorem coercion_graph_semantics_sound (Γ : Ctx Term) (t1 t2 : Nat):
  ⊢ Γ ->
  construct_coercion_graph Γ = g ->
  #t1 ∈ g.nodes ->
  #t2 ∈ g.nodes ->
  Γ ⊢ #t1 : k ->
  Γ ⊢ #t2 : k ->
  ∀ l, (t1, t2, l) ∈ g.edges ->
  Γ ⊢ l : (#t1 ~[k]~ #t2) := by
intro wf gph n1 n2 jn1 jn2 l ed
induction Γ
· exfalso; cases jn1; case _ jn1 => unfold Frame.get_type at jn1; simp at jn1
case _ f _ ih =>
cases wf
· sorry
· sorry
· sorry
· sorry
· sorry
· sorry
· sorry
· sorry
· sorry
· sorry



theorem synth_coercion_type_sound : ⊢ Γ ->
  Term.isType Γ A ->
  Term.isType Γ B ->
  infer_kind Γ A = .some k ->
  infer_kind Γ B = .some k ->
  synth_coercion Γ A B = .some t ->
  Γ ⊢ t : (A ~[k]~ B) := by
intro wf wflhs wfrhs jlhsk jrhsk j
induction Γ, A, B using synth_coercion.induct generalizing t k
all_goals (
  unfold synth_coercion at j; simp at j; rw[Option.bind_eq_some] at j
  cases j
)
case _ ih1 ih2 _ j => -- A1 `@k B1 ~ A2 `@k B2
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j;
  case _ kA1 jA1 kA2 jA2 kB1 jB1 kB2 jB2 jes w1 j1 w2 j2 =>
  have j3 := Term.eq_of_beq jes.1
  have j4 := Term.eq_of_beq jes.2
  unfold infer_kind at jlhsk; simp at jlhsk;
  rw[Option.bind_eq_some] at jlhsk; cases jlhsk; case _ jlhsk =>
  rw[Option.bind_eq_some] at jlhsk; cases jlhsk; case _ jlhsk =>
  cases jlhsk; case _ jlhsk =>
  rw[Option.bind_eq_some] at jlhsk; cases jlhsk; case _ jlhsk =>
  cases jlhsk; case _ jlhsk =>
  cases jlhsk; case _ jlhsk =>
  simp at jlhsk;
  cases jlhsk
  case _ A1k kk arrK _ B1k eA1 eA2 =>
  have lem := is_arrowk_some arrK;
  cases lem; unfold is_arrowk at arrK; simp at arrK;
  have lemA1 := infer_kind_sound A1k wf;
  cases eA2
  unfold infer_kind at jrhsk; simp at jrhsk;
  rw[Option.bind_eq_some] at jrhsk; cases jrhsk; case _ jrhsk =>
  rw[Option.bind_eq_some] at jrhsk; cases jrhsk; case _ jrhsk =>
  cases jrhsk; case _ jrhsk =>
  rw[Option.bind_eq_some] at jrhsk; cases jrhsk; case _ jrhsk =>
  cases jrhsk; case _ jrhsk =>
  cases jrhsk; case _ jrhsk =>
  simp at jrhsk; cases jrhsk;
  case _ A2k kk2 arr2K _ B2k eB1 eB2 =>
  have lem := is_arrowk_some arr2K;
  cases lem; unfold is_arrowk at arr2K; simp at arr2K;
  have lemA2 := infer_kind_sound A2k wf;
  cases j3; cases j4; clear jes;
  replace eB1 := Term.eq_of_beq eB1;
  replace eA1 := Term.eq_of_beq eA1;
  cases eB1; cases eA1;
  unfold Term.isType at wflhs; simp at wflhs;
  unfold Term.isType at wfrhs; simp at wfrhs;
  cases wflhs; cases wfrhs;
  simp_all;
  apply Judgment.appc; assumption; assumption

case _ ih1 ih2 _ j => -- A1 -t> B1 ~ A2 -t> B2
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>  cases j; case _ j =>
  cases j
  case _ kA1 jA1 kA2 jA2 kB1 jB1 kB2 jB2 jes w1 j1 w2 j2 =>
  have j3 := Term.eq_of_beq jes.1
  have j4 := Term.eq_of_beq jes.2
  cases j3; cases j4; clear jes
  have jAk' := infer_kind_sound jlhsk wf
  have jrhsk' := infer_kind_sound jrhsk wf
  cases jAk'; cases jrhsk'
  unfold Term.isType at wflhs; simp at wflhs
  unfold Term.isType at wfrhs; simp at wfrhs
  case _ jA1k jB1k jA2k jB2k =>
  have lemA1k := infer_kind_sound jA1 wf
  have lemB1k := infer_kind_sound jB1 (Judgment.wfempty wf)
  have lemA2k := infer_kind_sound jA2 wf
  have lemB2k := infer_kind_sound jB2 (Judgment.wfempty wf)
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.1) lemA1k jA1k; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.1) lemA1k jA1k; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.2) lemB1k jB1k; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wfrhs.2) lemB2k jB2k; cases u
  have ih1' := @ih1 ★ w1 wf wflhs.1 wfrhs.1 jA1 jA2 j1
  have ih2' := @ih2 ★ w2 (Judgment.wfempty wf) wflhs.2 wfrhs.2 jB1 jB2 j2
  constructor; assumption;  assumption

case _ K1 _ _ _ ih _ j => -- Γ ⊢ t : ((∀[K1]A1) ~[k]~ ∀[K2]A2)
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  cases j; case _  j1 _ j2 _ j3 _ j4 j5 w j6 =>
  replace j5 := Term.eq_of_beq j5; cases j5
  have j1' := wf_kind_sound j1 wf
  clear j2;
  have lem' := infer_kind_sound jrhsk wf
  cases lem'; case _ lemlhs =>
  have lem' := infer_kind_sound jlhsk wf
  cases lem'; case _ lemrhs =>
  have wf' := Judgment.wfkind j1' wf
  unfold Term.isType at wflhs; simp at wflhs
  unfold Term.isType at wfrhs; simp at wfrhs
  have lemA1 := infer_kind_sound j3 (Judgment.wfkind j1' wf)
  have lemA2 := infer_kind_sound j4 (Judgment.wfkind j1' wf)
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wflhs.2) lemrhs lemA1; cases u
  have u := uniqueness_of_kinds (Term.is_type_shape_sound wfrhs.2) lemlhs lemA2; cases u
  case _  jB1k _ jB2k =>
  have ih1' := @ih ★ w (Judgment.wfkind j1' wf) wflhs.2 wfrhs.2 j3 j4 j6
  constructor; assumption; assumption

case _ j =>
 cases j; case _ j =>
 simp at j; split at j
 · cases j; case _ j =>
   replace j := Term.eq_of_beq j; cases j
   case _ k jlhs _ _ _ =>
   rw[jlhs] at jrhsk; cases jrhsk
   constructor
   · have lem1 := infer_kind_sound jlhsk wf;
     have lem3 := kind_of_type_well_formed wf lem1; simp at lem3;
     replace lem3 := lem3 wflhs lem1;
     assumption
   · apply infer_kind_sound jlhs wf
 · rw[Option.bind_eq_some] at j; cases j; case _ j =>
   cases j; case _ j1 j2 => sorry -- needs coercion_graph_kind_soundness etc.


theorem synth_term_type_sound : ⊢ Γ ->
  Term.isType Γ τ ->
  Term.isKind k ->
  Γ ⊢ τ : k ->
  synth_term n Γ τ = .some t ->
  Γ ⊢ t : τ := by
intro wf wfτ wfk jk j
induction n, τ using synth_term.induct generalizing Γ t
all_goals (unfold synth_term at j)
· simp at j; cases j
  case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j;
  case _ e _ =>
  replace e := Term.eq_of_beq e; cases e;
  case _ =>
    unfold Term.isType at wfτ; simp at wfτ;
    cases wfτ; case _ wfτ _ =>
    cases wfτ; cases jk;
    case _ j1 _ j2 j3 j4 j5 j6 j7 j8 =>
    have lemA := infer_kind_sound j1 wf
    have lemB := infer_kind_sound j2 wf
    have lemA' := Term.is_type_shape_sound j4
    have lemB' := Term.is_type_shape_sound j5
    have u := uniqueness_of_kinds lemA' j7 lemA; cases u
    have u := uniqueness_of_kinds lemB' j8 lemB; cases u
    apply synth_coercion_type_sound; assumption; assumption; assumption; assumption; assumption; assumption
· simp at j; cases j
  case _ ih1 ih2 _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  simp at j; cases j;
  case _ e _ =>
  replace e := Term.eq_of_beq e; cases e;
  case _ j _ =>
  have e := invert_arr_kind jk; cases e
  split at j
  case _ kg _ _ _ k j2 =>
    cases j;
    have ih1' := @ih1 kg Γ k wf
    constructor
    sorry
    sorry
    sorry
  case _ =>
    sorry
case _ ih =>
  simp at j; cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j =>
  rw[Option.bind_eq_some] at j; cases j; case _ j =>
  cases j; case _ j1 j2 =>
  simp at j2; simp at j1;
  cases j2; case _ j2 j3 =>
  simp at j3;
  sorry

case _ => simp_all -- contradiction case we are out of corns
