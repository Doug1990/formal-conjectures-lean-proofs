import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Erdos481

/--
For a finite sequence of $n$ (not necessarily distinct) integers $A = (x_1,\ldots,x_n)$, the
sequence `T a b A` of length $rn$ given by $(a_ix_j+b_i)_{1\leq j\leq n, 1\leq i\leq r}$.
-/
def T {r : ℕ} (a b : Fin r → ℕ) (A : List ℕ) : List ℕ :=
  (List.finRange r).flatMap (fun i : Fin r => A.map (fun x : ℕ => a i * x + b i))

namespace K

/-- `T` on (value, multiplier) pairs. -/
def T' {r : ℕ} (a b : Fin r → ℕ) (L : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.finRange r).flatMap (fun i : Fin r => L.map (fun p => (a i * p.1 + b i, a i * p.2)))

lemma fst_T' {r : ℕ} (a b : Fin r → ℕ) (L : List (ℕ × ℕ)) :
    (T' a b L).map Prod.fst = T a b (L.map Prod.fst) := by
  simp [T', T, List.map_flatMap, Function.comp_def]

lemma fst_iter {r : ℕ} (a b : Fin r → ℕ) (k : ℕ) :
    ((T' a b)^[k] [(1, 1)]).map Prod.fst = (T a b)^[k] [1] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fst_T', ih]

lemma mem_T' {r : ℕ} {a b : Fin r → ℕ} {L : List (ℕ × ℕ)} {q : ℕ × ℕ} (h : q ∈ T' a b L) :
    ∃ i, ∃ p ∈ L, q = (a i * p.1 + b i, a i * p.2) := by
  simp only [T', List.mem_flatMap, List.mem_map] at h
  obtain ⟨i, -, p, hp, rfl⟩ := h
  exact ⟨i, p, hp, rfl⟩

lemma my_sum_flatMap {α β : Type*} (l : List α) (g : α → List β) (h : β → ℝ) :
    ((l.flatMap g).map h).sum = (l.map fun x => ((g x).map h).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih]

lemma my_le {β : Type*} (l : List β) (f g : β → ℝ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- Weight: sum of reciprocals of the multipliers. -/
noncomputable def W (L : List (ℕ × ℕ)) : ℝ := (L.map (fun p => (1 : ℝ) / p.2)).sum

lemma W_T' {r : ℕ} (a b : Fin r → ℕ) (L : List (ℕ × ℕ)) :
    W (T' a b L) = (∑ i, (1 : ℝ) / a i) * W L := by
  unfold W T'
  rw [my_sum_flatMap, Finset.sum_mul, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  push_cast
  rw [one_div_mul_one_div]

lemma W_iter {r : ℕ} (a b : Fin r → ℕ) (k : ℕ) :
    W ((T' a b)^[k] [(1, 1)]) = (∑ i, (1 : ℝ) / a i) ^ k := by
  induction k with
  | zero => simp [W]
  | succ k ih => rw [Function.iterate_succ_apply', W_T', ih, pow_succ, mul_comm]

lemma inv {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ) :
    ∀ p ∈ (T' a b)^[k] [(1, 1)],
      1 ≤ p.2 ∧ p.2 ≤ (1 + ∑ i, a i) ^ k ∧ 1 ≤ p.1 ∧ p.1 ≤ (1 + ∑ i, b i) * (k + 1) * p.2 := by
  induction k with
  | zero =>
    intro p hp
    obtain rfl : p = (1, 1) := by simpa using hp
    refine ⟨le_rfl, by simp, le_rfl, ?_⟩
    show 1 ≤ (1 + ∑ i, b i) * (0 + 1) * 1
    simp
  | succ k ih =>
    intro q hq
    rw [Function.iterate_succ_apply'] at hq
    obtain ⟨i, p, hp, rfl⟩ := mem_T' hq
    obtain ⟨h1, h2, h3, h4⟩ := ih p hp
    have hai := ha i
    have hai' : a i ≤ 1 + ∑ j, a j :=
      (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)).trans
        (Nat.le_add_left _ _)
    have hbi : b i ≤ ∑ j, b j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)
    have e2 : 1 ≤ a i * p.2 := Nat.mul_le_mul hai h1
    refine ⟨e2, ?_, ?_, ?_⟩
    · show a i * p.2 ≤ (1 + ∑ j, a j) ^ (k + 1)
      calc a i * p.2 ≤ (1 + ∑ j, a j) * (1 + ∑ j, a j) ^ k := Nat.mul_le_mul hai' h2
        _ = _ := by rw [pow_succ, mul_comm]
    · show 1 ≤ a i * p.1 + b i
      have := Nat.mul_le_mul hai h3
      omega
    · show a i * p.1 + b i ≤ (1 + ∑ j, b j) * (k + 1 + 1) * (a i * p.2)
      generalize ∑ j, b j = B at *
      have e1 : a i * p.1 ≤ a i * ((1 + B) * (k + 1) * p.2) := Nat.mul_le_mul_left _ h4
      have e3 : B ≤ (1 + B) * (a i * p.2) :=
        calc B ≤ (1 + B) * 1 := by omega
          _ ≤ _ := Nat.mul_le_mul_left _ e2
      calc a i * p.1 + b i ≤ a i * ((1 + B) * (k + 1) * p.2) + (1 + B) * (a i * p.2) :=
            Nat.add_le_add e1 (hbi.trans e3)
        _ = _ := by ring

lemma hb (s : Finset ℕ) (M : ℕ) (hs : ∀ x ∈ s, 1 ≤ x ∧ x ≤ M) :
    ∑ x ∈ s, (1 : ℝ) / x ≤ 1 + Real.log M := by
  calc ∑ x ∈ s, (1 : ℝ) / x ≤ ∑ x ∈ Finset.Icc 1 M, (1 : ℝ) / x := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          rw [Finset.mem_Icc]
          exact hs x hx
        · intro i _ _
          positivity
    _ = (harmonic M : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ _ := harmonic_le_one_add_log M

lemma bound {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ)
    (hnd : ((T a b)^[k] [1]).Nodup) :
    (∑ i, (1 : ℝ) / a i) ^ k ≤ (1 + ∑ i, (b i : ℝ)) * (k + 1) *
      (1 + Real.log ((1 + ∑ i, (b i : ℝ)) * (k + 1) * (1 + ∑ i, (a i : ℝ)) ^ k)) := by
  have hfst := fst_iter a b k
  have hW := W_iter a b k
  have hinv := inv a b ha k
  generalize (T' a b)^[k] [(1, 1)] = L at hfst hW hinv
  rw [← hfst] at hnd
  have hM : (((1 + ∑ i, b i) * (k + 1) * (1 + ∑ i, a i) ^ k : ℕ) : ℝ) =
      (1 + ∑ i, (b i : ℝ)) * (k + 1) * (1 + ∑ i, (a i : ℝ)) ^ k := by
    push_cast; ring
  rw [← hW, ← hM]
  have hX : (0 : ℝ) ≤ (1 + ∑ i, (b i : ℝ)) * (k + 1) := by positivity
  calc W L ≤ (L.map (fun p => ((1 + ∑ i, (b i : ℝ)) * (k + 1)) * (1 / (p.1 : ℝ)))).sum := by
        unfold W
        apply my_le
        intro p hp
        obtain ⟨h1, h2, h3, h4⟩ := hinv p hp
        have h1' : (0 : ℝ) < p.2 := by exact_mod_cast h1
        have h3' : (0 : ℝ) < p.1 := by exact_mod_cast h3
        have h4' : (p.1 : ℝ) ≤ ((1 + ∑ i, (b i : ℝ)) * (k + 1)) * p.2 := by exact_mod_cast h4
        rw [mul_one_div, div_le_div_iff₀ h1' h3']
        linarith
    _ = ((1 + ∑ i, (b i : ℝ)) * (k + 1)) *
          ((L.map Prod.fst).map (fun x : ℕ => 1 / (x : ℝ))).sum := by
        rw [List.sum_map_mul_left, List.map_map]
        rfl
    _ = ((1 + ∑ i, (b i : ℝ)) * (k + 1)) *
          ∑ x ∈ (L.map Prod.fst).toFinset, (fun x : ℕ => 1 / (x : ℝ)) x := by
        rw [List.sum_toFinset _ hnd]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hX
        apply hb
        intro x hx
        rw [List.mem_toFinset, List.mem_map] at hx
        obtain ⟨p, hp, rfl⟩ := hx
        obtain ⟨h1, h2, h3, h4⟩ := hinv p hp
        exact ⟨h3, h4.trans (Nat.mul_le_mul_left _ h2)⟩

lemma final (S c A : ℝ) (hS : 1 < S) (hc : 1 ≤ c) (hA : 1 ≤ A)
    (h : ∀ k : ℕ, S ^ k ≤ c * (k + 1) * (1 + Real.log (c * (k + 1) * A ^ k))) : False := by
  have key : ∀ k : ℕ, S ^ k ≤ c * (2 + c + A) * ((k : ℝ) + 1) ^ 2 := by
    intro k
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have l1 : Real.log (c * (k + 1) * A ^ k) = Real.log c + Real.log (k + 1) + k * Real.log A := by
      rw [Real.log_mul (mul_ne_zero (by linarith) (by linarith)) (pow_ne_zero _ (by linarith)),
        Real.log_mul (by linarith) (by linarith), Real.log_pow]
    have l2 : Real.log c ≤ c := le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
    have l3 : Real.log (k + 1) ≤ k + 1 :=
      le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
    have l4 : Real.log A ≤ A := le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
    have l5 : k * Real.log A ≤ k * A := mul_le_mul_of_nonneg_left l4 hk
    have hck : 0 ≤ c * (k + 1) := mul_nonneg (by linarith) (by linarith)
    have hbr : 0 ≤ (k + 1) * (2 + c + A) - (1 + c + (k + 1) + k * A) := by nlinarith
    calc S ^ k ≤ _ := h k
      _ ≤ c * (k + 1) * (1 + c + (k + 1) + k * A) := by
          rw [l1]
          apply mul_le_mul_of_nonneg_left _ hck
          linarith
      _ ≤ c * (2 + c + A) * ((k : ℝ) + 1) ^ 2 := by
          nlinarith [mul_nonneg hck hbr]
  have hD : 0 < c * (2 + c + A) := mul_pos (by linarith) (by linarith)
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 2 hS
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 ht).2 (1 / (4 * (c * (2 + c + A)))) (by positivity))
  have h1 := hN (N + 1) (by omega)
  have h2 := key (N + 1)
  have hSp : 0 < S ^ (N + 1) := pow_pos (by linarith) _
  rw [div_lt_div_iff₀ hSp (by positivity)] at h1
  have hn : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 N
  have hsq : (((N + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 4 * ((N + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hsq hD.le]

end K

theorem erdos_481 {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i)
    (hab : 1 < ∑ i, (1 : ℝ) / a i) :
    ∃ k, ¬ ((T a b)^[k] [1]).Nodup := by
  by_contra hcon
  push Not at hcon
  have hb0 : (0 : ℝ) ≤ ∑ i, (b i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ ∑ i, (a i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  exact K.final _ _ _ hab (by linarith) (by linarith) fun k => K.bound a b ha k (hcon k)

end Erdos481

#print axioms Erdos481.erdos_481
