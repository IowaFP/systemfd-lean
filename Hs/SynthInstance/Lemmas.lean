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
