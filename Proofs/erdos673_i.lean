import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Filter Finset
open scoped Topology

namespace Set

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos673

noncomputable def G (n : ℕ) : ℝ :=
  ∑ i : Fin (n.divisors.card - 1), (Nat.nth (· ∣ n) i : ℝ) / Nat.nth (· ∣ n) (i + 1)

/-! ### Tao's bound (copied from results/erdos673_tao.lean) -/

lemma fin_dvd (n : ℕ) (hn : 0 < n) : (Set.ofPred (· ∣ n)).Finite := by
  apply n.divisors.finite_toSet.subset
  intro d hd
  simp only [Finset.mem_coe, Nat.mem_divisors]
  exact ⟨hd, hn.ne'⟩

lemma card_dvd_eq (n : ℕ) (hn : 0 < n) : (fin_dvd n hn).toFinset.card = n.divisors.card := by
  congr 1
  ext d
  simp only [Set.Finite.mem_toFinset, Nat.mem_divisors]
  exact ⟨fun h => ⟨h, hn.ne'⟩, fun h => h.1⟩

lemma G_eq (n : ℕ) : G n = ∑ j ∈ Finset.range (n.divisors.card - 1),
    (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1) :=
  Fin.sum_univ_eq_sum_range (fun j => (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1)) _

lemma key (n m e : ℕ) (hn : 0 < n) (hm : 1 < m) (he : e ∣ n / m) (hmn : m ∣ n) :
    Nat.count (· ∣ n) e + 1 < n.divisors.card ∧
    (1 : ℝ) / m ≤ (Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) : ℝ) /
      Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
  have hf := fin_dvd n hn
  have hc := card_dvd_eq n hn
  have hnm : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmn) (by omega)
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he hnm
  have hdiv : e ∣ n := he.trans (Nat.div_dvd_of_dvd hmn)
  have hem : e * m ∣ n := by
    obtain ⟨k, hk⟩ := he
    obtain ⟨l, hl⟩ := hmn
    refine ⟨k, ?_⟩
    have : n / m = l := by rw [hl, Nat.mul_div_cancel_left _ (by omega)]
    rw [hl, ← this, hk]; ring
  have hlt : e + 1 ≤ e * m := by nlinarith
  have h1 : Nat.count (· ∣ n) (e + 1) = Nat.count (· ∣ n) e + 1 :=
    Nat.count_succ_eq_succ_count_iff.2 hdiv
  have h2 : Nat.count (· ∣ n) (e + 1) ≤ Nat.count (· ∣ n) (e * m) := Nat.count_monotone _ hlt
  have h3 : Nat.count (· ∣ n) (e * m) < n.divisors.card := hc ▸ Nat.count_lt_card hf hem
  refine ⟨by omega, ?_⟩
  rw [Nat.nth_count (p := (· ∣ n)) hdiv]
  have h4 : Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) ≤ e * m := by
    calc _ ≤ Nat.nth (· ∣ n) (Nat.count (· ∣ n) (e * m)) :=
          Nat.nth_le_nth_of_lt_card hf (by omega) (by omega)
      _ = e * m := Nat.nth_count (p := (· ∣ n)) hem
  have h5 : e < Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
    calc e = Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) := (Nat.nth_count (p := (· ∣ n)) hdiv).symm
      _ < _ := Nat.nth_lt_nth_of_lt_card hf (Nat.lt_succ_self _) (by omega)
  have he' : (0 : ℝ) < e := by exact_mod_cast hepos
  have h4' : ((Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) : ℕ) : ℝ) ≤ (e : ℝ) * m := by
    exact_mod_cast h4
  have h5' : (0 : ℝ) < ((Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_le _).trans_lt h5
  calc (1 : ℝ) / m = e / (e * m) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left he'.le h5' h4'

lemma tao_lower (n m : ℕ) (hn : 0 < n) (hm : 1 < m) (hmn : m ∣ n) :
    ((n / m).divisors.card : ℝ) / m ≤ G n := by
  rw [G_eq]
  have hinj : Set.InjOn (Nat.count (· ∣ n)) ((n / m).divisors : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∣ n := (Nat.dvd_of_mem_divisors ha).trans (Nat.div_dvd_of_dvd hmn)
    have hb' : b ∣ n := (Nat.dvd_of_mem_divisors hb).trans (Nat.div_dvd_of_dvd hmn)
    exact Nat.count_injective ha' hb' hab
  calc ((n / m).divisors.card : ℝ) / m = ∑ e ∈ (n / m).divisors, (1 : ℝ) / m := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ e ∈ (n / m).divisors, (Nat.nth (· ∣ n) (Nat.count (· ∣ n) e) : ℝ) /
          Nat.nth (· ∣ n) (Nat.count (· ∣ n) e + 1) := by
        apply Finset.sum_le_sum
        intro e he
        exact (key n m e hn hm (Nat.dvd_of_mem_divisors he) hmn).2
    _ = ∑ j ∈ (n / m).divisors.image (Nat.count (· ∣ n)),
          (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1) :=
        (Finset.sum_image (f := fun j => (Nat.nth (· ∣ n) j : ℝ) / Nat.nth (· ∣ n) (j + 1))
          hinj).symm
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hj
          rw [Finset.mem_range]
          have := (key n m e hn hm (Nat.dvd_of_mem_divisors he) hmn).1
          omega
        · intro j _ _
          positivity

/-! ### Number-theoretic helpers -/

lemma totient_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have hpP := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hpP (hs' q hq)).2 (fun h => hp (h ▸ hq))
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.totient_mul hcop,
      Nat.totient_prime hpP, ih hs']

lemma totient_prod_primes_real (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (Nat.totient (∏ p ∈ s, p) : ℝ) = (∏ p ∈ s, (p : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
  rw [totient_prod_primes s hs, ← Finset.prod_mul_distrib, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h1 : 1 ≤ p := (hs p hp).one_lt.le
  have h0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hs p hp).ne_zero
  rw [Nat.cast_sub h1, mul_sub, mul_one_div_cancel h0]
  simp

lemma cop_mul (Q q : ℕ) : #{n ∈ range (q * Q) | Q.Coprime n} = q * Nat.totient Q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * Q = q * Q + Q by ring, Finset.range_eq_Ico,
      ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (q * Q)) (Nat.le_add_right _ _),
      Finset.filter_union, Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ← Finset.range_eq_Ico, ih, Nat.filter_coprime_Ico_eq_totient]
    ring

lemma cop_count (Q b : ℕ) (hQ : 0 < Q) :
    #{n ∈ range b | Q.Coprime n} ≤ (b / Q + 1) * Nat.totient Q := by
  rw [← cop_mul]
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro x hx
  have h := Nat.lt_mul_div_succ b hQ
  rw [Finset.mem_range] at hx ⊢
  rw [mul_comm]
  omega

lemma block_exists (a : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ b, a < b ∧ ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ δ := by
  set f := Set.indicator {p : ℕ | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) with hf
  have hnn : ∀ n, 0 ≤ f n := fun n =>
    Set.indicator_nonneg (fun n _ => div_nonneg zero_le_one (Nat.cast_nonneg n)) n
  have hns := not_summable_one_div_on_primes
  rw [← hf, not_summable_iff_tendsto_nat_atTop_of_nonneg hnn] at hns
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_atTop.1 hns ((∑ i ∈ range a, f i) - Real.log δ))
  refine ⟨max N (a + 1), by omega, ?_⟩
  have hab : a ≤ max N (a + 1) := by omega
  have hsplit := Finset.sum_range_add_sum_Ico f hab
  have hbig := hN (max N (a + 1)) (le_max_left _ _)
  have hIco : ∑ i ∈ Ico a (max N (a + 1)), f i =
      ∑ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 / (p : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hf, Set.indicator_apply]
    rfl
  have hL : -Real.log δ ≤ ∑ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 / (p : ℝ)) := by
    linarith
  calc ∏ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, Real.exp (-(1 / (p : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hpP := (Finset.mem_filter.1 hp).2
          have : (1 : ℝ) / p ≤ 1 :=
            div_le_one_of_le₀ (by exact_mod_cast hpP.one_lt.le) (Nat.cast_nonneg _)
          linarith
        · intro p _
          have := Real.add_one_le_exp (-(1 / (p : ℝ)))
          linarith
    _ = Real.exp (-(∑ p ∈ (Ico a (max N (a + 1))).filter Nat.Prime, (1 / (p : ℝ)))) := by
        rw [← Real.exp_sum, Finset.sum_neg_distrib]
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 (by linarith)
    _ = δ := Real.exp_log hδ

lemma tau_ge (x : ℕ) (hx : x ≠ 0) (D : Finset ℕ) (hD : ∀ p ∈ D, p.Prime ∧ p ∣ x) :
    2 ^ #D ≤ #x.divisors := by
  rw [Nat.card_divisors hx]
  calc 2 ^ #D ≤ 2 ^ #x.primeFactors :=
        Nat.pow_le_pow_right (by norm_num) (Finset.card_le_card fun p hp =>
          Nat.mem_primeFactors.2 ⟨(hD p hp).1, (hD p hp).2, hx⟩)
    _ ≤ _ := by
        apply Finset.pow_card_le_prod
        intro p hp
        obtain ⟨hpP, hpd, -⟩ := Nat.mem_primeFactors.1 hp
        have := hpP.factorization_pos_of_dvd hx hpd
        omega

/-! ### Blocks of primes -/

/-- Product of the primes in `[a, b)`. -/
def Qb (a b : ℕ) : ℕ := ∏ p ∈ (Ico a b).filter Nat.Prime, p

lemma Qb_pos (a b : ℕ) : 0 < Qb a b :=
  Finset.prod_pos fun _ hp => (Finset.mem_filter.1 hp).2.pos

lemma not_cop (a b n : ℕ) (h : ¬ (Qb a b).Coprime n) :
    ∃ p, p.Prime ∧ a ≤ p ∧ p < b ∧ p ∣ n := by
  by_contra hc
  apply h
  refine Nat.Coprime.prod_left fun p hp => ?_
  obtain ⟨hpI, hpP⟩ := Finset.mem_filter.1 hp
  rw [Finset.mem_Ico] at hpI
  rw [Nat.Prime.coprime_iff_not_dvd hpP]
  intro hd
  exact hc ⟨p, hpP, hpI.1, hpI.2, hd⟩

lemma cop_density (a b N : ℕ) (δ : ℝ)
    (hR : ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ δ) :
    (#{n ∈ range N | (Qb a b).Coprime n} : ℝ) ≤ δ * N + Qb a b := by
  have hQ := Qb_pos a b
  have hQr : (0 : ℝ) < Qb a b := by exact_mod_cast hQ
  have h1 := cop_count (Qb a b) N hQ
  have h2 : (#{n ∈ range N | (Qb a b).Coprime n} : ℝ) ≤
      ((N / Qb a b : ℕ) : ℝ) * Nat.totient (Qb a b) + Nat.totient (Qb a b) := by
    have : ((#{n ∈ range N | (Qb a b).Coprime n} : ℕ) : ℝ) ≤
        (((N / Qb a b + 1) * Nat.totient (Qb a b) : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have h3 : ((N / Qb a b : ℕ) : ℝ) ≤ (N : ℝ) / Qb a b := Nat.cast_div_le
  have h4 : (Nat.totient (Qb a b) : ℝ) =
      (Qb a b : ℝ) * ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
    unfold Qb
    rw [totient_prod_primes_real _ (fun p hp => (Finset.mem_filter.1 hp).2), Nat.cast_prod]
  have h5 : (Nat.totient (Qb a b) : ℝ) ≤ Qb a b := by exact_mod_cast Nat.totient_le _
  have h6 : ((N / Qb a b : ℕ) : ℝ) * Nat.totient (Qb a b) ≤
      (N : ℝ) / Qb a b * Nat.totient (Qb a b) :=
    mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
  have h7 : (N : ℝ) / Qb a b * Nat.totient (Qb a b) =
      N * ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
    rw [h4]
    field_simp
  have h8 : (N : ℝ) * ∏ p ∈ (Ico a b).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ N * δ :=
    mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg _)
  linarith

noncomputable def sq (a : ℕ) (δ : ℝ) (hδ : 0 < δ) : ℕ → ℕ
  | 0 => a
  | j + 1 => Classical.choose (block_exists (sq a δ hδ j) δ hδ)

lemma seq_exists (a : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ s : ℕ → ℕ, s 0 = a ∧ ∀ j, s j < s (j + 1) ∧
    ∏ p ∈ (Ico (s j) (s (j + 1))).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ δ :=
  ⟨sq a δ hδ, rfl, fun j => Classical.choose_spec (block_exists (sq a δ hδ j) δ hδ)⟩

/-! ### Good integers have large `G` -/

lemma G_big (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hpd : p ∣ n) (D : Finset ℕ)
    (hD : ∀ q ∈ D, q.Prime ∧ q ∣ n ∧ q ≠ p) : (2 : ℝ) ^ #D / p ≤ G n := by
  have ht := tao_lower n p hn hp.one_lt hpd
  have hnp : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hpd) hp.pos).ne'
  have hτ := tau_ge (n / p) hnp D (fun q hq => by
    obtain ⟨h1, h2, h3⟩ := hD q hq
    have hcop : q.Coprime p := (Nat.coprime_primes h1 hp).2 h3
    rw [← Nat.mul_div_cancel' hpd] at h2
    exact ⟨h1, hcop.dvd_mul_left.1 h2⟩)
  have h : (2 : ℝ) ^ #D ≤ #(n / p).divisors := by exact_mod_cast hτ
  calc (2 : ℝ) ^ #D / p ≤ #(n / p).divisors / p := div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
    _ ≤ G n := ht

lemma good (C : ℝ) (e1 K : ℕ) (he1 : 0 < e1) (hK : C * e1 < 2 ^ K) (s : ℕ → ℕ)
    (hs : StrictMono s) (hs0 : s 0 = e1) (n : ℕ) (hn : n ≠ 0)
    (h0 : ¬ (Qb 0 e1).Coprime n) (hj : ∀ j < K, ¬ (Qb (s j) (s (j + 1))).Coprime n) :
    C < G n := by
  obtain ⟨p, hp, -, hpe, hpd⟩ := not_cop 0 e1 n h0
  have hex : ∀ j, ∃ q, j < K → (q.Prime ∧ s j ≤ q ∧ q < s (j + 1) ∧ q ∣ n) := by
    intro j
    by_cases hjK : j < K
    · obtain ⟨q, h1, h2, h3, h4⟩ := not_cop _ _ n (hj j hjK)
      exact ⟨q, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, fun h => absurd h hjK⟩
  choose f hf using hex
  have hinj : Set.InjOn f (range K : Set ℕ) := by
    intro i hi j hj' hij
    rw [Finset.coe_range, Set.mem_Iio] at hi hj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 := (hf i hi).2.2.1
      have h2 := (hf j hj').2.1
      have h3 := hs.monotone (show i + 1 ≤ j by omega)
      omega
    · have h1 := (hf j hj').2.2.1
      have h2 := (hf i hi).2.1
      have h3 := hs.monotone (show j + 1 ≤ i by omega)
      omega
  have hcard : #((range K).image f) = K := by rw [card_image_of_injOn hinj, card_range]
  have hD : ∀ q ∈ (range K).image f, q.Prime ∧ q ∣ n ∧ q ≠ p := by
    intro q hq
    obtain ⟨j, hj', rfl⟩ := Finset.mem_image.1 hq
    rw [Finset.mem_range] at hj'
    obtain ⟨h1, h2, -, h4⟩ := hf j hj'
    have := hs.monotone (Nat.zero_le j)
    refine ⟨h1, h4, ?_⟩
    omega
  have hG := G_big n p (Nat.pos_of_ne_zero hn) hp hpd _ hD
  rw [hcard] at hG
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpe' : (p : ℝ) ≤ e1 := by exact_mod_cast hpe.le
  have h1 : C < (2 : ℝ) ^ K / e1 := by
    rw [lt_div_iff₀ (by exact_mod_cast he1)]
    exact hK
  have h2 : (2 : ℝ) ^ K / e1 ≤ 2 ^ K / p := div_le_div_of_nonneg_left (by positivity) hpr hpe'
  linarith

/-! ### Counting -/

lemma lower (C ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, ∀ N : ℕ, (N : ℝ) - ε * N - c ≤ #{n ∈ range N | C < G n} := by
  obtain ⟨e1, he1, hR0⟩ := block_exists 0 (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (C * e1) (by norm_num : (1 : ℝ) < 2)
  have hδ : 0 < ε / (2 * (K + 1)) := by positivity
  obtain ⟨s, hs0, hs⟩ := seq_exists e1 (ε / (2 * (K + 1))) hδ
  have hsm : StrictMono s := strictMono_nat_of_lt_succ fun j => (hs j).1
  refine ⟨1 + Qb 0 e1 + ∑ j ∈ range K, (Qb (s j) (s (j + 1)) : ℝ), fun N => ?_⟩
  have hsub : (range N).filter (fun n => ¬ C < G n) ⊆
      ({0} ∪ (range N).filter (fun n => (Qb 0 e1).Coprime n)) ∪
      (range K).biUnion (fun j => (range N).filter (fun n => (Qb (s j) (s (j + 1))).Coprime n)) := by
    intro n hn
    obtain ⟨hnN, hnC⟩ := Finset.mem_filter.1 hn
    by_cases h0 : n = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [h0]))
    by_cases h1 : (Qb 0 e1).Coprime n
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hnN, h1⟩))
    by_cases h2 : ∃ j < K, (Qb (s j) (s (j + 1))).Coprime n
    · obtain ⟨j, hj, h⟩ := h2
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨j, Finset.mem_range.2 hj, Finset.mem_filter.2 ⟨hnN, h⟩⟩)
    · exfalso
      exact hnC (good C e1 K he1 hK s hsm hs0 n h0 h1 (fun j hj h => h2 ⟨j, hj, h⟩))
  have h3 : #((range N).filter (fun n => ¬ C < G n)) ≤
      1 + #((range N).filter (fun n => (Qb 0 e1).Coprime n)) +
      ∑ j ∈ range K, #((range N).filter (fun n => (Qb (s j) (s (j + 1))).Coprime n)) := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ #({0} : Finset ℕ) + #((range N).filter (fun n => (Qb 0 e1).Coprime n)) +
          #((range K).biUnion
            (fun j => (range N).filter (fun n => (Qb (s j) (s (j + 1))).Coprime n))) :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ _ := by
          rw [Finset.card_singleton]
          exact Nat.add_le_add_left Finset.card_biUnion_le _
  have h3' : (#((range N).filter (fun n => ¬ C < G n)) : ℝ) ≤
      1 + #((range N).filter (fun n => (Qb 0 e1).Coprime n)) +
      ∑ j ∈ range K, (#((range N).filter (fun n => (Qb (s j) (s (j + 1))).Coprime n)) : ℝ) := by
    exact_mod_cast h3
  have h4 := cop_density 0 e1 N (ε / 2) hR0
  have h5 : ∑ j ∈ range K, (#((range N).filter (fun n => (Qb (s j) (s (j + 1))).Coprime n)) : ℝ)
      ≤ ∑ j ∈ range K, (ε / (2 * (K + 1)) * N + (Qb (s j) (s (j + 1)) : ℝ)) :=
    Finset.sum_le_sum fun j _ => cop_density (s j) (s (j + 1)) N _ (hs j).2
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h5
  have hKδ : (K : ℝ) * (ε / (2 * (K + 1))) ≤ ε / 2 := by
    have e : ((K : ℝ) + 1) * (ε / (2 * (K + 1))) = ε / 2 := by
      field_simp
    nlinarith
  have hKδN : (K : ℝ) * (ε / (2 * (K + 1)) * N) ≤ ε / 2 * N := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hKδ (Nat.cast_nonneg _)
  have hsplit : (#((range N).filter (fun n => C < G n)) : ℝ) +
      #((range N).filter (fun n => ¬ C < G n)) = N := by
    exact_mod_cast (by rw [Finset.card_filter_add_card_filter_not, Finset.card_range] :
      #((range N).filter (fun n => C < G n)) + #((range N).filter (fun n => ¬ C < G n)) = N)
  linarith

theorem erdos_673.parts.i : ∀ C : ℝ, {n : ℕ | C < G n}.HasDensity 1 := by
  intro C
  unfold Set.HasDensity
  have hpd : ∀ b : ℕ, Set.partialDensity {n : ℕ | C < G n} Set.univ b =
      (#((range b).filter (fun n => C < G n)) : ℝ) / b := by
    intro b
    have e1 : ({n : ℕ | C < G n} ∩ Set.univ ∩ Set.Iio b) =
        (((range b).filter (fun n => C < G n) : Finset ℕ) : Set ℕ) := by
      ext n
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_univ, and_true, Set.mem_Iio,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      tauto
    have e2 : (Set.univ ∩ Set.Iio b : Set ℕ) = ((range b : Finset ℕ) : Set ℕ) := by
      ext n
      simp
    unfold Set.partialDensity
    rw [e1, e2, Set.ncard_coe_finset, Set.ncard_coe_finset, Finset.card_range]
  simp only [hpd]
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun b => ?_⟩
  · obtain ⟨c, hc⟩ := lower C ((1 - a) / 3) (by linarith)
    rw [eventually_atTop]
    obtain ⟨N0, hN0⟩ := exists_nat_gt (c / ((1 - a) / 3))
    refine ⟨N0 + 1, fun N hN => ?_⟩
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN0N : (N0 : ℝ) ≤ N := by exact_mod_cast (show N0 ≤ N by omega)
    have hcN : c < (1 - a) / 3 * N := by
      have := hN0.trans_le hN0N
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    rw [lt_div_iff₀ hNpos]
    have := hc N
    nlinarith
  · have h : #((range b).filter (fun n => C < G n)) ≤ b :=
      (Finset.card_filter_le _ _).trans (Finset.card_range b).le
    have h' : (#((range b).filter (fun n => C < G n)) : ℝ) ≤ b := by exact_mod_cast h
    calc _ ≤ (1 : ℝ) := div_le_one_of_le₀ h' (Nat.cast_nonneg _)
      _ < a := ha

end Erdos673

#print axioms Erdos673.erdos_673.parts.i
