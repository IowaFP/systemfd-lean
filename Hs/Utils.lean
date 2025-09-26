

theorem List.reverse_length {l : List α}:
  l.length = l.reverse.length := by
induction l <;> simp at *
