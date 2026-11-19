import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Linarith

namespace Erdos670

open Filter

def HasSeparatedDistances {X : Type*} [MetricSpace X] (A : Finset X) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ e ∈ A, a ≠ b → c ≠ e → s(a, b) ≠ s(c, e) →
    1 ≤ |dist a b - dist c e|

/-- Nonnegative reals pairwise at least 1 apart: sum ≥ k(k-1)/2. -/
lemma sum_sep (T : Finset ℝ) : (∀ a ∈ T, 0 ≤ a) →
    (∀ a ∈ T, ∀ b ∈ T, a ≠ b → 1 ≤ |a - b|) →
    ((T.card : ℝ) * ((T.card : ℝ) - 1) / 2 ≤ ∑ a ∈ T, a) ∧
      (T.Nonempty → ∃ a ∈ T, (T.card : ℝ) - 1 ≤ a) := by
  induction T using Finset.induction_on_max with
  | empty => intro _ _; simp
  | insert a s ha ih =>
    intro h0 hs
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => h0 x (Finset.mem_insert_of_mem hx))
      (fun x hx z hz hxz => hs x (Finset.mem_insert_of_mem hx) z (Finset.mem_insert_of_mem hz) hxz)
    have ha0 : 0 ≤ a := h0 a (Finset.mem_insert_self a s)
    have hcard : (s.card : ℝ) ≤ a := by
      rcases s.eq_empty_or_nonempty with he | hne
      · simp [he, ha0]
      · obtain ⟨c, hc, hcle⟩ := ih2 hne
        have hca := ha c hc
        have := hs a (Finset.mem_insert_self a s) c (Finset.mem_insert_of_mem hc) (ne_of_gt hca)
        rw [abs_of_pos (by linarith)] at this
        linarith
    rw [Finset.card_insert_of_notMem has, Finset.sum_insert has]
    push_cast
    refine ⟨?_, fun _ => ⟨a, Finset.mem_insert_self a s, by linarith⟩⟩
    have key : ((s.card : ℝ) + 1) * ((s.card : ℝ) + 1 - 1) / 2
        = s.card + s.card * ((s.card : ℝ) - 1) / 2 := by ring
    rw [key]
    linarith

lemma tele (x : ℕ → ℝ) (N k : ℕ) :
    ∑ i ∈ Finset.range N, (x (i + k) - x i) = ∑ j ∈ Finset.range k, (x (N + j) - x j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h := Finset.sum_range_sub (fun j => x (N + j)) k
    have h2 : ∑ j ∈ Finset.range k, (x (N + 1 + j) - x j)
        = ∑ j ∈ Finset.range k, (x (N + j) - x j)
          + ∑ j ∈ Finset.range k, (x (N + (j + 1)) - x (N + j)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [show N + 1 + j = N + (j + 1) by omega]
      ring
    rw [h2, h]
    simp

lemma tele_le (x : ℕ → ℝ) (hmono : Monotone x) (N k n : ℕ) (hNk : N + k ≤ n) :
    ∑ i ∈ Finset.range N, (x (i + k) - x i) ≤ k * (x (n - 1) - x 0) := by
  rw [tele]
  calc ∑ j ∈ Finset.range k, (x (N + j) - x j)
      ≤ ∑ j ∈ Finset.range k, (x (n - 1) - x 0) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        have hj' := Finset.mem_range.1 hj
        have h1 := hmono (show N + j ≤ n - 1 by omega)
        have h2 := hmono (Nat.zero_le j)
        linarith
    _ = k * (x (n - 1) - x 0) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma sum_succ (m : ℕ) : ∑ k ∈ Finset.range m, ((k : ℝ) + 1) = m * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma core (x : ℕ → ℝ) (n m : ℕ) (hmono : Monotone x) (hm : m ≤ n)
    (hsep : ∀ i j k l, i < j → j < n → k < l → l < n → (i ≠ k ∨ j ≠ l) →
      1 ≤ |(x j - x i) - (x l - x k)|) :
    ((m * (n - m) : ℕ) : ℝ) * (((m * (n - m) : ℕ) : ℝ) - 1) / 2
      ≤ (x (n - 1) - x 0) * (m * (m + 1) / 2) := by
  classical
  set Q : Finset (ℕ × ℕ) := Finset.range m ×ˢ Finset.range (n - m) with hQ
  set v : ℕ × ℕ → ℝ := fun p => x (p.2 + p.1 + 1) - x p.2 with hv
  have hmemQ : ∀ p ∈ Q, p.1 < m ∧ p.2 < n - m := by
    intro p hp
    rw [hQ, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    exact hp
  have hpair : ∀ p ∈ Q, ∀ q ∈ Q, v p ≠ v q → 1 ≤ |v p - v q| := by
    intro p hp q hq hne
    obtain ⟨hp1, hp2⟩ := hmemQ p hp
    obtain ⟨hq1, hq2⟩ := hmemQ q hq
    apply hsep p.2 (p.2 + p.1 + 1) q.2 (q.2 + q.1 + 1) (by omega) (by omega) (by omega) (by omega)
    by_contra hc
    push Not at hc
    apply hne
    have hpq : p = q := Prod.ext (by omega) hc.1
    rw [hpq]
  have hinj : Set.InjOn v Q := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2⟩ := hmemQ p hp
    obtain ⟨hq1, hq2⟩ := hmemQ q hq
    by_contra hne
    have := hsep p.2 (p.2 + p.1 + 1) q.2 (q.2 + q.1 + 1) (by omega) (by omega) (by omega) (by omega)
      (by
        by_contra hc
        push Not at hc
        apply hne
        exact Prod.ext (by omega) hc.1)
    have h0 : (x (p.2 + p.1 + 1) - x p.2) - (x (q.2 + q.1 + 1) - x q.2) = 0 := by
      have : v p = v q := hpq
      simp only [hv] at this
      linarith
    rw [h0, abs_zero] at this
    linarith
  set T := Q.image v with hT
  have hTcard : T.card = m * (n - m) := by
    rw [hT, Finset.card_image_of_injOn hinj, hQ, Finset.card_product, Finset.card_range,
      Finset.card_range]
  have hT0 : ∀ a ∈ T, 0 ≤ a := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 ha
    have := hmono (show p.2 ≤ p.2 + p.1 + 1 by omega)
    simp only [hv]
    linarith
  have hTs : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 1 ≤ |a - b| := by
    intro a ha b hb hab
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
    exact hpair p hp q hq hab
  have hlow := (sum_sep T hT0 hTs).1
  rw [hTcard] at hlow
  have hsum : ∑ a ∈ T, a = ∑ k ∈ Finset.range m,
      ∑ i ∈ Finset.range (n - m), (x (i + (k + 1)) - x i) := by
    rw [hT, Finset.sum_image hinj, hQ, Finset.sum_product]
    rfl
  have hup : ∑ k ∈ Finset.range m, ∑ i ∈ Finset.range (n - m), (x (i + (k + 1)) - x i)
      ≤ ∑ k ∈ Finset.range m, ((k : ℝ) + 1) * (x (n - 1) - x 0) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk' := Finset.mem_range.1 hk
    have := tele_le x hmono (n - m) (k + 1) n (by omega)
    push_cast at this
    exact this
  rw [← Finset.sum_mul, sum_succ] at hup
  linarith

lemma arith (m a ε D : ℝ) (hm : 1 ≤ m) (hε0 : 0 < ε) (hε : 2 ≤ ε * m)
    (ha : 2 * m ^ 2 + m ^ 3 + 1 ≤ a)
    (hD : (m * a) * ((m * a) - 1) / 2 ≤ D * (m * (m + 1) / 2)) :
    (1 - ε) * (a + m) ^ 2 ≤ D := by
  have h1 : (m + 1) * (1 - ε) ≤ m - 1 := by nlinarith
  have hm3 : 0 ≤ m ^ 3 := by positivity
  have ha1 : 1 ≤ a := by nlinarith
  have hA : a * (2 * m ^ 2 + m ^ 3 + 1) ≤ a * a := mul_le_mul_of_nonneg_left ha (by linarith)
  have hB : m ^ 3 ≤ a * m ^ 3 := by nlinarith
  have hC : 0 ≤ a * m := by nlinarith
  have hD2 : 0 ≤ m ^ 2 := by positivity
  have h2 : (m - 1) * (a + m) ^ 2 ≤ m * a ^ 2 - a := by nlinarith
  have h3 : 0 ≤ (a + m) ^ 2 := sq_nonneg _
  have h4 : (m + 1) * (1 - ε) * (a + m) ^ 2 ≤ (m - 1) * (a + m) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 h3
  have key : (m * (m + 1)) * ((1 - ε) * (a + m) ^ 2) ≤ (m * (m + 1)) * D := by
    calc (m * (m + 1)) * ((1 - ε) * (a + m) ^ 2) = m * ((m + 1) * (1 - ε) * (a + m) ^ 2) := by
          ring
      _ ≤ m * ((m - 1) * (a + m) ^ 2) := mul_le_mul_of_nonneg_left h4 (by linarith)
      _ ≤ m * (m * a ^ 2 - a) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = 2 * ((m * a) * ((m * a) - 1) / 2) := by ring
      _ ≤ 2 * (D * (m * (m + 1) / 2)) := by linarith
      _ = (m * (m + 1)) * D := by ring
  exact le_of_mul_le_mul_left key (mul_pos (by linarith) (by linarith))

lemma real_core (S : Finset ℝ) (n m : ℕ) (hS : S.card = n) (hn : m < n)
    (hsep : HasSeparatedDistances S) :
    ((m * (n - m) : ℕ) : ℝ) * (((m * (n - m) : ℕ) : ℝ) - 1) / 2
      ≤ Metric.diam (S : Set ℝ) * (m * (m + 1) / 2) := by
  set f := S.orderEmbOfFin hS with hf
  set x : ℕ → ℝ := fun i => f ⟨min i (n - 1), by omega⟩ with hx
  have hmono : Monotone x := by
    intro i j hij
    exact f.le_iff_le.2 (Fin.mk_le_mk.2 (by omega))
  have hmem : ∀ i, x i ∈ S := fun i => Finset.orderEmbOfFin_mem S hS _
  have hlt : ∀ i j, i < j → j < n → x i < x j := by
    intro i j hij hj
    exact f.lt_iff_lt.2 (Fin.mk_lt_mk.2 (by omega))
  have hinj : ∀ i k, i < n → k < n → x i = x k → i = k := by
    intro i k hi hk h
    have := congrArg Fin.val (f.injective h)
    simp only at this
    omega
  have hsep' : ∀ i j k l, i < j → j < n → k < l → l < n → (i ≠ k ∨ j ≠ l) →
      1 ≤ |(x j - x i) - (x l - x k)| := by
    intro i j k l hij hj hkl hl hne
    have hs : s(x j, x i) ≠ s(x l, x k) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := hinj j l hj hl h1
        have := hinj i k (by omega) (by omega) h2
        omega
      · have := hinj j k hj (by omega) h1
        have := hinj i l (by omega) hl h2
        omega
    have := hsep (x j) (hmem j) (x i) (hmem i) (x l) (hmem l) (x k) (hmem k)
      (ne_of_gt (hlt i j hij hj)) (ne_of_gt (hlt k l hkl hl)) hs
    rw [Real.dist_eq, Real.dist_eq, abs_of_pos (sub_pos.2 (hlt i j hij hj)),
      abs_of_pos (sub_pos.2 (hlt k l hkl hl))] at this
    exact this
  have hc := core x n m hmono hn.le hsep'
  have hd : x (n - 1) - x 0 ≤ Metric.diam (S : Set ℝ) := by
    have := Metric.dist_le_diam_of_mem S.finite_toSet.isBounded (hmem (n - 1)) (hmem 0)
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hmono (Nat.zero_le _)))] at this
    exact this
  have hpos : (0 : ℝ) ≤ m * (m + 1) / 2 := by positivity
  exact hc.trans (mul_le_mul_of_nonneg_right hd hpos)

lemma de (p q : EuclideanSpace ℝ (Fin 1)) : dist p q = dist (p 0) (q 0) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, Real.sqrt_sq dist_nonneg]

theorem erdos_670.variants.dim_one :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ A : Finset (EuclideanSpace ℝ (Fin 1)), A.card = n → HasSeparatedDistances A →
        (1 - ε) * (n : ℝ) ^ 2 ≤ Metric.diam (A : Set (EuclideanSpace ℝ (Fin 1))) := by
  intro ε hε
  classical
  set m := ⌈2 / ε⌉₊ with hmdef
  have hm2 : 2 / ε ≤ (m : ℝ) := Nat.le_ceil _
  have hεm : 2 ≤ ε * m := by
    rw [div_le_iff₀ hε] at hm2
    linarith
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 < m := Nat.ceil_pos.2 (div_pos (by norm_num) hε)
    exact_mod_cast this
  refine Filter.eventually_atTop.2 ⟨m + (2 * m ^ 2 + m ^ 3 + 1), fun n hn A hA hsep => ?_⟩
  set e : EuclideanSpace ℝ (Fin 1) → ℝ := fun p => p 0 with he
  have hiso : Isometry e := Isometry.of_dist_eq (fun p q => (de p q).symm)
  set S := A.image e with hS
  have hScard : S.card = n := by
    rw [hS, Finset.card_image_of_injective _ hiso.injective, hA]
  have hSsep : HasSeparatedDistances S := by
    intro a ha b hb c hc d hd hab hcd hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hd
    have := hsep p hp q hq r hr t ht (fun h => hab (by rw [h])) (fun h => hcd (by rw [h]))
      (fun h => hs (congrArg (Sym2.map e) h))
    rw [de, de] at this
    exact this
  have hdiam : Metric.diam (A : Set (EuclideanSpace ℝ (Fin 1))) = Metric.diam (S : Set ℝ) := by
    rw [hS, Finset.coe_image, hiso.diam_image]
  rw [hdiam]
  have hmn : m < n := by omega
  have hc := real_core S n m hScard hmn hSsep
  have hcast : ((m * (n - m) : ℕ) : ℝ) = (m : ℝ) * ((n - m : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at hc
  have hnm : (n : ℝ) = ((n - m : ℕ) : ℝ) + m := by
    rw [Nat.cast_sub hmn.le]; ring
  rw [hnm]
  apply arith (m : ℝ) ((n - m : ℕ) : ℝ) ε _ hm1 hε hεm _ hc
  have : 2 * m ^ 2 + m ^ 3 + 1 ≤ n - m := by omega
  exact_mod_cast this

end Erdos670

#print axioms Erdos670.erdos_670.variants.dim_one
