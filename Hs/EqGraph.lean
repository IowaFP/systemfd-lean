
structure EqGraph (T : Type) where
  nodes : List T
  edges : List (Nat × Nat × T)

namespace EqGraph

  def empty_graph : EqGraph T := { nodes := [], edges := [] }

  variable {T : Type} [BEq T]

  def node_data (g : EqGraph T) (i : Nat) : Option T := g.nodes[i]?

  def remaining_node_count (n : Nat) (visited : Nat -> Bool) : Nat :=
    let ℓ := List.filter (λ i => !visited i) (List.range n)
    List.length ℓ

  def mark_visited (visited : Nat -> Bool) (x : Nat) (i : Nat) : Bool :=
    if x == i then true
    else visited i

  theorem mark_visited_monotonic : v n -> mark_visited v i n := by
  intro h
  unfold mark_visited; simp
  apply Or.inr h

  theorem mark_visited_neq_monotonic : i ≠ n -> v n = b -> mark_visited v i n = b := by
  intro h1 h2
  unfold mark_visited; simp; rw [h2]; simp
  intro h3; exfalso; apply h1 h3

  theorem remaining_node_count_succ :
    remaining_node_count (n + 1) v = (if v n then 0 else 1) + remaining_node_count n v
  := by
  unfold remaining_node_count; simp
  rw [List.range_succ]; simp
  have lem : (List.filter (λ i => !v i) [n]).length = if v n = true then 0 else 1 := by
    unfold List.filter; simp
    generalize tdef : v n = t at *
    cases t <;> simp at *
  rw [lem]; omega

  theorem remaining_node_count_visited_n : m ≥ n ->
    remaining_node_count n (mark_visited v m) = remaining_node_count n v
  := by
  intro h
  induction n generalizing v m
  case _ => unfold remaining_node_count; simp
  case _ n ih =>
    rw [remaining_node_count_succ, remaining_node_count_succ]
    have lem : m ≥ n := by omega
    rw [ih lem]; simp
    cases lem
    case _ => exfalso; omega
    case _ x h2 =>
      simp at *;
      generalize tdef : v n = t
      have lem : x + 1 ≠ n := by omega
      cases t <;> simp
      case _ => apply mark_visited_neq_monotonic lem tdef
      case _ => apply mark_visited_monotonic tdef

  theorem remaining_node_count_gt_zero :
    v i = false ->
    i < n ->
    remaining_node_count n v > 0
  := by
  intro h1 h2
  unfold remaining_node_count; simp
  exists i

  theorem mark_visited_decrements_node_count :
    v i = false ->
    i < n ->
    remaining_node_count n v = x + 1 ->
    remaining_node_count n (mark_visited v i) = x
  := by
  intro h1 h2 h3
  induction n generalizing v i x
  case _ => cases h2
  case _ n ih =>
    rw [remaining_node_count_succ]
    rw [remaining_node_count_succ] at h3
    generalize t1def : v n = t1 at *
    cases t1 <;> simp at h3
    case _ =>
      have lem1 : remaining_node_count n v = x := by omega
      cases Nat.decEq n i
      case _ h4 =>
        have lem2 : mark_visited v i n = false := by
          unfold mark_visited; simp
          apply And.intro _ t1def; omega
        have lem3 : i < n := by omega
        rw [lem2]; simp
        cases x <;> simp at *
        case _ =>
          have lem4 := remaining_node_count_gt_zero h1 lem3
          omega
        case _ x =>
          replace ih := ih h1 lem3 lem1
          rw [ih]; omega
      case _ h4 =>
        subst h4
        generalize zdef : mark_visited v n n = z
        unfold mark_visited at zdef; simp at zdef
        subst zdef; simp
        rw [remaining_node_count_visited_n (by simp)]; apply lem1
    case _ =>
      cases h2
      case _ => rw [t1def] at h1; injection h1
      case _ h4 =>
        simp at h4
        have lem1 : i < n := by omega
        replace ih := ih h1 lem1 h3; rw [ih]
        rw [mark_visited_monotonic t1def]; simp

  def children (g : EqGraph T) (visited : Nat -> Bool) (s : Nat) : List (Nat × T) :=
    let ℓ := List.filter (λ (i, j, _) => i == s && !visited j && j < g.nodes.length) g.edges
    List.map (λ (_, j, t) => (j, t)) ℓ

  theorem children_are_nodes : (c, e) ∈ children g v s -> c < g.nodes.length := by
    intro h; unfold children at h; simp at h
    cases h; case _ a h =>
    cases h; case _ h1 h2 =>
    cases h2; case _ h2 h3 =>
    apply h3

  set_option linter.unusedVariables false in
  def find_path (g : EqGraph T) : (visited : Nat -> Bool) -> (s : Nat) -> (t : T) -> Option (List T)
  := λ visited s t => do
    let sd <- node_data g s
    if t == sd then return []
    let v := mark_visited visited s
    let cℓ := children g visited s
    if h1 : !visited s && s < g.nodes.length then
      for h2 : (c, e) in cℓ do
        let rest := find_path g v c t
        match rest with
        | .some p => return e :: p
        | .none => ()
      .none
    else .none
  termination_by v => remaining_node_count (List.length g.nodes) v
  decreasing_by
  generalize xdef : remaining_node_count g.nodes.length visited = x
  cases x
  case _ =>
    have lem : remaining_node_count g.nodes.length visited > 0 := by
      have lem1 := children_are_nodes h2
      unfold cℓ at h2; unfold children at h2; simp at h2
      cases h2; case _ a h =>
      unfold remaining_node_count; simp
      apply Exists.intro c
      apply And.intro lem1 h.2.1.2
    exfalso; omega
  case _ x =>
    simp at h1
    rw [mark_visited_decrements_node_count h1.1 h1.2 xdef]
    simp

  def find_node_with_label (g : EqGraph T) (label : T) : Option Nat := g.nodes.idxOf? label

  def find_path_by_label (g : EqGraph T) (visited : Nat -> Bool) (s : T) (t : T) : Option (List T) := do
    let source <- find_node_with_label g s
    find_path g visited source t

  def add_node (g : EqGraph T) (l : T) : EqGraph T :=
    { nodes := g.nodes ++ [l], edges := g.edges } -- TODO do we care about efficieny?

  def add_edge (g : EqGraph T) (l s t : T) : EqGraph T :=
    let (g, s') := match find_node_with_label g s with
      | .some n => (g, n)
      | .none => (add_node g s, g.nodes.length)
    let (g, t') := match find_node_with_label g t with
      | .some n => (g, n)
      | .none => (add_node g t, g.nodes.length)
    { nodes := g.nodes, edges := (s', t', l) :: g.edges }

  namespace Test
    def test_graph_loop : EqGraph String := {
      nodes := ["a", "b", "c", "d", "e"],
      edges := [
        (0, 1, "a->b"), (1, 2, "b->c"), (2, 3, "c->d"), (3, 4, "d->e"), (4, 0, "e->a")
      ]
    }

    #eval (EqGraph.add_edge empty_graph "e01" "n0" "n1").add_edge "e12" "n1" "n2"


    #eval find_path test_graph_loop (λ _ => false) 1 "a"
    #eval find_path_by_label test_graph_loop (λ _ => false) "b" "a"
    #eval find_path test_graph_loop (λ _ => false) 0 "e"
    #eval find_path_by_label test_graph_loop (λ _ => false) "a" "e"
  end Test

end EqGraph
