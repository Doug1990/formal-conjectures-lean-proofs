import Mathlib

open scoped Nat.Prime

namespace OeisA100478

noncomputable def a (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | i + 5 =>
    let sumTerms := a (i + 4) + a (i + 3) + a (i + 2) + a (i + 1) + a i
    π sumTerms

theorem a_4 : a 4 = 1 := by rfl

end OeisA100478

#print axioms OeisA100478.a_4
