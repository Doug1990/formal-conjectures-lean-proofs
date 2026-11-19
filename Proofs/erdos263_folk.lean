import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace Erdos263

def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  (∀ n : ℕ, a n > 0) ∧
    StrictMono a ∧
    (∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
      atTop.Tendsto (fun n : ℕ => (a n : ℝ) / (b n : ℝ)) (𝓝 1) →
      Irrational (∑' n, 1 / (b n : ℝ)))

namespace FK

def key (L : ℕ → ℝ) (m : ℕ) : ℝ ×ₗ ℕ := toLex (L m, m)

lemma key_lt_iff (L : ℕ → ℝ) (m n : ℕ) :
    key L m < key L n ↔ L m < L n ∨ (L m = L n ∧ m < n) := by
  unfold key; exact Prod.Lex.toLex_lt_toLex

lemma key_inj (L : ℕ → ℝ) {m n : ℕ} (h : key L m = key L n) : m = n := by
  have := congrArg (fun x => (ofLex x).2) h
  simpa [key] using this

lemma L_le_of_not_lt (L : ℕ → ℝ) {m n : ℕ} (h : ¬ key L m < key L n) : L n ≤ L m := by
  by_contra h'
  push Not at h'
  exact h ((key_lt_iff L m n).2 (Or.inl h'))

lemma log_le_half (x : ℝ) (hx : 0 ≤ x) : Real.log (1 + x) ≤ (1 + x) / 2 := by
  have h1 : Real.log ((1 + x) / 2) ≤ (1 + x) / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log ((1 + x) / 2) = Real.log (1 + x) - Real.log 2 :=
    Real.log_div (by positivity) (by norm_num)
  have h3 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  linarith

lemma logB_le (B : ℝ) (hB : 12 ≤ B) : Real.log (1 + 2 * B) ≤ B / 2 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := B / 2) (by linarith)
  have h2 : 1 + 2 * B ≤ Real.exp (B / 2) := by nlinarith
  rw [Real.log_le_iff_le_exp (by linarith)]
  exact h2

/-- The ordering argument: every element has a bounded "prefix sum". -/
theorem bound (L : ℕ → ℝ) (hL0 : ∀ m, 0 ≤ L m) (pred : ℕ → Finset ℕ)
    (hpred : ∀ m n, m ∈ pred n ↔ key L m < key L n) (C : ℝ) (hC : 0 ≤ C)
    (hbad : ∀ n, L n ≤ (∑ m ∈ pred n, L m) + C + Real.log (1 + L n)) :
    ∀ j n, (pred n).card = j → (∑ m ∈ pred n, L m) + L n ≤
      (12 + 6 * C) * 2 ^ j - j - (2 + C + Real.log (1 + 2 * (12 + 6 * C))) := by
  set B := 12 + 6 * C with hBdef
  have hlB := logB_le B (by linarith)
  have hlB0 : 0 ≤ Real.log (1 + 2 * B) := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  intro j
  induction j with
  | zero =>
    intro n hn
    rw [Finset.card_eq_zero] at hn
    have h1 := hbad n
    rw [hn] at h1 ⊢
    have h2 := log_le_half (L n) (hL0 n)
    simp only [Finset.sum_empty] at h1 ⊢
    push_cast
    linarith
  | succ j ih =>
    intro n hn
    have hne : (pred n).Nonempty := by
      rw [← Finset.card_pos, hn]; omega
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (pred n) (key L) hne
    have hpp : pred p = (pred n).erase p := by
      ext m
      rw [Finset.mem_erase, hpred, hpred]
      constructor
      · intro h
        refine ⟨?_, lt_trans h ((hpred p n).1 hp)⟩
        rintro rfl; exact lt_irrefl _ h
      · rintro ⟨h1, h2⟩
        have h3 := hmax m ((hpred m n).2 h2)
        refine lt_of_le_of_ne h3 ?_
        intro h4; exact h1 (key_inj L h4)
    have hcp : (pred p).card = j := by
      rw [hpp, Finset.card_erase_of_mem hp, hn]; rfl
    have hIH := ih p hcp
    have hsum : (∑ m ∈ pred n, L m) = (∑ m ∈ pred p, L m) + L p := by
      rw [hpp, Finset.sum_erase_add _ _ hp]
    set S := ∑ m ∈ pred n, L m with hSdef
    have hS : S ≤ B * 2 ^ j - j - (2 + C + Real.log (1 + 2 * B)) := by
      rw [hsum]; exact hIH
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun m _ => hL0 m)
    have hb := hbad n
    have hh := log_le_half (L n) (hL0 n)
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hL1 : L n ≤ 2 * S + 2 * C + 1 := by linarith
    have hSB : S ≤ B * 2 ^ j := by linarith
    have hBp : B * 1 ≤ B * 2 ^ j := by
      apply mul_le_mul_of_nonneg_left hpow; linarith
    have hle : 1 + L n ≤ (1 + 2 * B) * 2 ^ (j + 1) := by
      rw [pow_succ]; nlinarith
    have hlog : Real.log (1 + L n) ≤ Real.log (1 + 2 * B) + (j + 1) := by
      have h1 : Real.log (1 + L n) ≤ Real.log ((1 + 2 * B) * 2 ^ (j + 1)) :=
        Real.log_le_log (by linarith [hL0 n]) hle
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow] at h1
      push_cast at h1
      have : ((j : ℝ) + 1) * Real.log 2 ≤ (j + 1) * 1 :=
        mul_le_mul_of_nonneg_left hl2 (by linarith)
      linarith
    rw [pow_succ]
    push_cast
    linarith

/-- The final contradiction with growth. -/
theorem contra (L : ℕ → ℝ) (hL0 : ∀ m, 0 ≤ L m) (pred : ℕ → Finset ℕ)
    (hpred : ∀ m n, m ∈ pred n ↔ key L m < key L n) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ n, (∑ m ∈ pred n, L m) + L n ≤ B * 2 ^ (pred n).card)
    (hgrow : ∀ᶠ m in atTop, B * 2 ^ m < L m) : False := by
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hgrow
  obtain ⟨n, -, hmax⟩ := Finset.exists_max_image (Finset.range (N2 + 1)) (key L)
    ⟨0, by simp⟩
  have hsub : (Finset.range (N2 + 1)).erase n ⊆ pred n := by
    intro m hm
    rw [Finset.mem_erase] at hm
    rw [hpred]
    refine lt_of_le_of_ne (hmax m hm.2) ?_
    intro h; exact hm.1 (key_inj L h)
  have hc : N2 ≤ (pred n).card := by
    have := Finset.card_le_card hsub
    have h2 : N2 ≤ ((Finset.range (N2 + 1)).erase n).card := by
      have := Finset.pred_card_le_card_erase (s := Finset.range (N2 + 1)) (a := n)
      simp at this; omega
    omega
  set c := (pred n).card with hcdef
  have hnn : n ∉ pred n := by
    rw [hpred]; exact lt_irrefl _
  have hcard : (insert n (pred n)).card = c + 1 := Finset.card_insert_of_notMem hnn
  have hex : ∃ m ∈ insert n (pred n), c ≤ m := by
    by_contra h
    push Not at h
    have : insert n (pred n) ⊆ Finset.range c := by
      intro m hm; rw [Finset.mem_range]; exact h m hm
    have := Finset.card_le_card this
    rw [hcard, Finset.card_range] at this
    omega
  obtain ⟨m, hm, hcm⟩ := hex
  have hS0 : 0 ≤ ∑ k ∈ pred n, L k := Finset.sum_nonneg (fun k _ => hL0 k)
  have hLm : L m ≤ (∑ k ∈ pred n, L k) + L n := by
    rcases Finset.mem_insert.1 hm with h | h
    · subst h; linarith
    · have := Finset.single_le_sum (fun k _ => hL0 k) h
      linarith [hL0 n]
  have h1 := hT n
  have h2 : B * 2 ^ c ≤ B * 2 ^ m :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hcm) hB
  have h3 := hN2 m (by omega)
  linarith

end FK

open FK in
theorem erdos_263.variants.folklore (a : ℕ -> ℕ)
    (ha : atTop.Tendsto (fun n : ℕ => (a n : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop) :
    Irrational <| ∑' n, (1 : ℝ) / (a n : ℝ) := by
  classical
  -- basic definitions
  set bN : ℕ → ℕ := fun m => max (a m) 1 with hbN
  set L : ℕ → ℝ := fun m => Real.log (bN m : ℝ) with hLdef
  have hb1 : ∀ m, (1 : ℝ) ≤ (bN m : ℝ) := by
    intro m; exact_mod_cast le_max_right (a m) 1
  have hL0 : ∀ m, 0 ≤ L m := fun m => Real.log_nonneg (hb1 m)
  have hexpL : ∀ m, Real.exp (L m) = (bN m : ℝ) := fun m =>
    Real.exp_log (by linarith [hb1 m])
  -- growth
  have grow : ∀ K : ℝ, 0 ≤ K → ∀ᶠ m in atTop, 1 ≤ a m ∧ K * 2 ^ m ≤ L m := by
    intro K hK
    filter_upwards [ha.eventually (eventually_ge_atTop (Real.exp K))] with m hm
    have ha0 : (0 : ℝ) ≤ a m := by positivity
    have e1 : ((a m : ℝ) ^ (1 / (2 ^ m : ℝ))) ^ (2 ^ m) = (a m : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]
      push_cast
      rw [one_div_mul_cancel (by positivity), Real.rpow_one]
    have e2 : Real.exp K ^ (2 ^ m) ≤ (a m : ℝ) := by
      rw [← e1]
      exact pow_le_pow_left₀ (Real.exp_pos K).le hm _
    rw [← Real.exp_nat_mul] at e2
    have e3 : (1 : ℝ) ≤ a m := by
      have : (1 : ℝ) ≤ Real.exp (((2 ^ m : ℕ) : ℝ) * K) := Real.one_le_exp (by positivity)
      linarith
    have e3' : 1 ≤ a m := by exact_mod_cast e3
    refine ⟨e3', ?_⟩
    have hbm : (bN m : ℝ) = a m := by
      simp only [hbN]; rw [max_eq_left e3']
    show K * 2 ^ m ≤ Real.log (bN m : ℝ)
    rw [hbm, Real.le_log_iff_exp_le (by linarith)]
    push_cast at e2
    rw [mul_comm]; exact e2
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (grow 2 (by norm_num))
  -- terms
  set g : ℕ → ℝ := fun m => 1 / (a m : ℝ) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => by simp only [hg]; positivity
  have hgL : ∀ m, g m ≤ Real.exp (-L m) := by
    intro m
    rw [Real.exp_neg, hexpL]
    simp only [hg]
    rcases Nat.eq_zero_or_pos (a m) with h | h
    · rw [h]; simp
    · have hbm : bN m = a m := by simp only [hbN]; rw [max_eq_left h]
      rw [hbm, one_div]
  have hmpow : ∀ m : ℕ, (m : ℝ) ≤ 2 ^ m := by
    intro m
    have := Nat.lt_two_pow_self (n := m)
    exact_mod_cast this.le
  have he1 : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num)
    rwa [Real.exp_zero] at this
  have he0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hgeo : Summable (fun m : ℕ => Real.exp (-1) ^ m) :=
    summable_geometric_of_lt_one he0 he1
  have hexpm : ∀ m : ℕ, Real.exp (-(m : ℝ)) = Real.exp (-1) ^ m := by
    intro m; rw [← Real.exp_nat_mul]; ring_nf
  have hind : ∀ M : ℕ, Summable (fun m : ℕ => if m < M then (1 : ℝ) else 0) := by
    intro M
    apply summable_of_ne_finset_zero (s := Finset.range M)
    intro m hm
    rw [Finset.mem_range] at hm
    simp [hm]
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun m => ?_) ((hind N1).add hgeo)
    by_cases hm : m < N1
    · simp only [hm, if_true]
      have : g m ≤ 1 := by
        simp only [hg]
        rcases Nat.eq_zero_or_pos (a m) with h | h
        · rw [h]; simp
        · have : (1 : ℝ) ≤ a m := by exact_mod_cast h
          rw [div_le_one (by linarith)]; exact this
      linarith [pow_nonneg he0 m]
    · simp only [hm, if_false, zero_add]
      have h1 := (hN1 m (by omega)).2
      have h2 := hgL m
      rw [← hexpm]
      refine h2.trans (Real.exp_le_exp.2 ?_)
      have := hmpow m
      linarith
  -- rationality assumption
  intro hrat
  obtain ⟨r, hr⟩ := hrat
  set s := ∑' n, (1 : ℝ) / (a n : ℝ) with hs
  have hsg : s = ∑' m, g m := rfl
  have hq0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hqs : (r.den : ℝ) * s = r.num := by
    rw [← hr, Rat.cast_def]; field_simp
  set C : ℝ := Real.log r.den + Real.log ((N1 : ℝ) + 3) with hCdef
  have hC : 0 ≤ C := by
    have h1 : 0 ≤ Real.log (r.den : ℝ) := Real.log_nonneg (by exact_mod_cast r.den_pos)
    have h2 : 0 ≤ Real.log ((N1 : ℝ) + 3) := Real.log_nonneg (by linarith [(Nat.cast_nonneg N1 : (0:ℝ) ≤ N1)])
    linarith
  -- predecessor sets
  let pred : ℕ → Finset ℕ := fun n =>
    (Finset.range (N1 + ⌈L n⌉₊ + 1)).filter (fun m => key L m < key L n)
  have hpred : ∀ m n, m ∈ pred n ↔ key L m < key L n := by
    intro m n
    simp only [pred, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      by_cases hm : m < N1
      · omega
      · have h1 := (hN1 m (by omega)).2
        have h2 : L m ≤ L n := by
          rcases (key_lt_iff L m n).1 h with h | h
          · exact h.le
          · exact h.1.le
        have h3 := hmpow m
        have h4 : (m : ℝ) ≤ ⌈L n⌉₊ := by
          have := Nat.le_ceil (L n)
          have : (0:ℝ) ≤ 2 ^ m := by positivity
          linarith
        have : m ≤ ⌈L n⌉₊ := by exact_mod_cast h4
        omega
  -- the bad inequality at every n
  have hbad : ∀ n, L n ≤ (∑ m ∈ pred n, L m) + C + Real.log (1 + L n) := by
    intro n
    by_contra hgood
    push Not at hgood
    set H := pred n with hH
    set P : ℕ := ∏ m ∈ H, bN m with hP
    -- integrality
    set d : ℕ → ℕ := fun m => if a m = 0 then 0 else ∏ k ∈ H.erase m, bN k with hd
    have hPg : ∀ m ∈ H, (P : ℝ) * g m = (d m : ℝ) := by
      intro m hm
      simp only [hd, hg]
      by_cases h0 : a m = 0
      · simp [h0]
      · rw [if_neg h0]
        have hbm : bN m = a m := by
          simp only [hbN]; rw [max_eq_left (Nat.one_le_iff_ne_zero.2 h0)]
        have hPe : P = (∏ k ∈ H.erase m, bN k) * a m := by
          rw [hP, ← Finset.prod_erase_mul H bN hm, hbm]
        rw [hPe]
        have : (a m : ℝ) ≠ 0 := by exact_mod_cast h0
        push_cast
        field_simp
    -- split the sum
    set f : ℕ → ℝ := fun m => if m ∈ H then 0 else g m with hf
    have hf0 : ∀ m, 0 ≤ f m := fun m => by
      simp only [hf]; split_ifs
      · exact le_refl _
      · exact hg0 m
    have hfg : ∀ m, f m ≤ g m := fun m => by
      simp only [hf]; split_ifs
      · exact hg0 m
      · exact le_refl _
    have hfsum : Summable f := Summable.of_nonneg_of_le hf0 hfg hgsum
    set e : ℕ → ℝ := fun m => if m ∈ H then g m else 0 with he
    have hesum : Summable e := by
      apply summable_of_ne_finset_zero (s := H)
      intro m hm; simp [he, hm]
    have hsplit : s = (∑ m ∈ H, g m) + ∑' m, f m := by
      have h1 : ∑' m, e m = ∑ m ∈ H, g m := by
        rw [tsum_eq_sum (s := H) (fun m hm => by simp [he, hm])]
        exact Finset.sum_congr rfl (fun m hm => by simp [he, hm])
      rw [← h1, ← hesum.tsum_add hfsum, hsg]
      congr 1; funext m
      simp only [he, hf]; split_ifs <;> simp
    set t := ∑' m, f m with ht
    have hint : ∃ z : ℤ, (r.den : ℝ) * P * t = z := by
      refine ⟨r.num * P - r.den * ∑ m ∈ H, (d m : ℤ), ?_⟩
      have : t = s - ∑ m ∈ H, g m := by linarith
      rw [this]
      push_cast
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      have h2 : ∀ m ∈ H, (r.den : ℝ) * P * g m = r.den * (d m : ℝ) := by
        intro m hm; rw [mul_assoc, hPg m hm]
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum]
      have : (r.den : ℝ) * P * s = r.num * P := by
        rw [mul_comm (r.den : ℝ) P, mul_assoc, hqs]; ring
      rw [this]
    obtain ⟨z, hz⟩ := hint
    -- positivity of the tail
    set m0 := N1 + H.sup id + 1 with hm0
    have hm0H : m0 ∉ H := by
      intro h
      have := Finset.le_sup (f := id) h
      simp only [id] at this
      omega
    have hgm0 : 0 < g m0 := by
      have := (hN1 m0 (by omega)).1
      simp only [hg]
      have : (1 : ℝ) ≤ a m0 := by exact_mod_cast this
      positivity
    have htpos : 0 < t := by
      have h1 : f m0 = g m0 := by simp [hf, hm0H]
      have := Summable.tsum_lt_tsum (f := fun _ => (0 : ℝ)) (i := m0) hf0
        (by rw [h1]; exact hgm0) summable_zero hfsum
      simpa using this
    -- upper bound of the tail
    set M := N1 + ⌈L n⌉₊ with hM
    set hb : ℕ → ℝ := fun m =>
      Real.exp (-L n) * ((if m < M then (1 : ℝ) else 0) + Real.exp (-1) ^ m) with hhb
    have hfb : ∀ m, f m ≤ hb m := by
      intro m
      have hb0 : 0 ≤ hb m := by
        simp only [hhb]
        apply mul_nonneg (Real.exp_pos _).le
        apply add_nonneg
        · split_ifs <;> norm_num
        · exact pow_nonneg he0 m
      simp only [hf]
      split_ifs with hmH
      · exact hb0
      · have hLn : L n ≤ L m := L_le_of_not_lt L (by rwa [hpred] at hmH)
        by_cases hmM : m < M
        · simp only [hhb, hmM, if_true]
          have h1 := hgL m
          have h2 : Real.exp (-L m) ≤ Real.exp (-L n) := Real.exp_le_exp.2 (by linarith)
          have h3 : 0 ≤ Real.exp (-L n) * Real.exp (-1) ^ m :=
            mul_nonneg (Real.exp_pos _).le (pow_nonneg he0 m)
          nlinarith
        · simp only [hhb, hmM, if_false, zero_add]
          have h1 := (hN1 m (by omega)).2
          have h3 := hmpow m
          have h4 : L n ≤ m := by
            have := Nat.le_ceil (L n)
            have : ⌈L n⌉₊ ≤ m := by omega
            have : ((⌈L n⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast this
            linarith
          rw [← hexpm, ← Real.exp_add]
          refine (hgL m).trans (Real.exp_le_exp.2 ?_)
          linarith
    have hbsum : Summable hb := ((hind M).add hgeo).mul_left _
    have htb : t ≤ ∑' m, hb m := Summable.tsum_le_tsum hfb hfsum hbsum
    have hbval : ∑' m, hb m = Real.exp (-L n) * (M + (1 - Real.exp (-1))⁻¹) := by
      simp only [hhb]
      rw [tsum_mul_left, Summable.tsum_add (hind M) hgeo, tsum_geometric_of_lt_one he0 he1]
      congr 2
      rw [tsum_eq_sum (s := Finset.range M) (fun m hm => by
        rw [Finset.mem_range] at hm; simp [hm])]
      rw [Finset.sum_congr rfl (fun m hm => by rw [Finset.mem_range] at hm; simp [hm] :
        ∀ m ∈ Finset.range M, (if m < M then (1 : ℝ) else 0) = 1)]
      simp
    have hinv : (1 - Real.exp (-1))⁻¹ ≤ 2 := by
      have h1 : 2 ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      have h2 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        linarith
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have hMle : (M : ℝ) ≤ N1 + L n + 1 := by
      simp only [hM]; push_cast
      have := Nat.ceil_lt_add_one (hL0 n)
      linarith
    have ht2 : t ≤ Real.exp (-L n) * ((N1 : ℝ) + L n + 3) := by
      rw [hbval] at htb
      refine htb.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
      linarith
    -- the product as an exponential
    have hPexp : (P : ℝ) = Real.exp (∑ m ∈ H, L m) := by
      rw [Real.exp_sum, hP]; push_cast
      exact Finset.prod_congr rfl (fun m _ => (hexpL m).symm)
    have hqexp : (r.den : ℝ) = Real.exp (Real.log r.den) := (Real.exp_log hq0).symm
    have hNexp : ((N1 : ℝ) + L n + 3) = Real.exp (Real.log ((N1 : ℝ) + L n + 3)) :=
      (Real.exp_log (by linarith [hL0 n, (Nat.cast_nonneg N1 : (0:ℝ) ≤ N1)])).symm
    have hlogsplit : Real.log ((N1 : ℝ) + L n + 3) ≤
        Real.log ((N1 : ℝ) + 3) + Real.log (1 + L n) := by
      rw [← Real.log_mul (by positivity) (by linarith [hL0 n])]
      apply Real.log_le_log (by linarith [hL0 n, (Nat.cast_nonneg N1 : (0:ℝ) ≤ N1)])
      have := hL0 n
      have : (0 : ℝ) ≤ N1 := Nat.cast_nonneg N1
      nlinarith
    have hlt : (r.den : ℝ) * P * t < 1 := by
      have hP0 : (0 : ℝ) ≤ P := by positivity
      calc (r.den : ℝ) * P * t ≤ (r.den : ℝ) * P * (Real.exp (-L n) * ((N1 : ℝ) + L n + 3)) :=
            mul_le_mul_of_nonneg_left ht2 (by positivity)
        _ = Real.exp (Real.log r.den + (∑ m ∈ H, L m) + -L n +
              Real.log ((N1 : ℝ) + L n + 3)) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add, ← hqexp, ← hPexp, ← hNexp]; ring
        _ < 1 := by
            have := Real.exp_lt_exp.2 (show Real.log r.den + (∑ m ∈ H, L m) + -L n +
              Real.log ((N1 : ℝ) + L n + 3) < 0 by linarith)
            rwa [Real.exp_zero] at this
    have hzpos : (0 : ℝ) < z := by
      rw [← hz]
      have : (0 : ℝ) < P := by
        have : (1 : ℝ) ≤ P := by
          rw [hPexp]; exact Real.one_le_exp (Finset.sum_nonneg (fun m _ => hL0 m))
        linarith
      positivity
    rw [hz] at hlt
    have h1 : (0 : ℤ) < z := by exact_mod_cast hzpos
    have h2 : z < 1 := by exact_mod_cast hlt
    omega
  -- combinatorial contradiction
  have hT := bound L hL0 pred hpred C hC hbad
  set B := 12 + 6 * C with hB
  have hlB0 : 0 ≤ Real.log (1 + 2 * B) := Real.log_nonneg (by linarith)
  refine contra L hL0 pred hpred B (by linarith) (fun n => ?_) ?_
  · have := hT _ n rfl
    have : (0 : ℝ) ≤ ((pred n).card : ℝ) := Nat.cast_nonneg _
    linarith
  · filter_upwards [grow (B + 1) (by linarith)] with m hm
    have : (0 : ℝ) < 2 ^ m := by positivity
    nlinarith [hm.2]

theorem erdos_263.variants.super_doubly_exponential_eventual (a : ℕ → ℕ)
    (ha : ∀ n : ℕ, a n > 0)
    (ha' : StrictMono a)
    (ha'' : ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∀ᶠ n in atTop, c * (a n : ℝ) ^ (2 + ε) ≤ (a (n + 1) : ℝ)) :
    IsIrrationalitySequence a := by
  obtain ⟨ε, c, hε, hc, hev⟩ := ha''
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set y : ℕ → ℝ := fun n => Real.log (a n) with hy
  have hapos : ∀ n, (0 : ℝ) < a n := fun n => by exact_mod_cast ha n
  have hrec : ∀ n ≥ N0, Real.log c + (2 + ε) * y n ≤ y (n + 1) := by
    intro n hn
    have h1 := hN0 n hn
    have h0 := hapos n
    have h2 : 0 < c * (a n : ℝ) ^ (2 + ε) := by positivity
    have h3 := Real.log_le_log h2 h1
    rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow h0] at h3
    exact h3
  set Y0 : ℝ := 2 * |Real.log c| / ε + 1 with hY0
  have hY0pos : 1 ≤ Y0 := by
    have : 0 ≤ 2 * |Real.log c| / ε := by positivity
    linarith
  have hY0e : ε / 2 * Y0 = |Real.log c| + ε / 2 := by
    rw [hY0]; field_simp
  set N := N0 + ⌈Real.exp Y0⌉₊ with hN
  have hyN : ∀ n ≥ N, Y0 ≤ y n := by
    intro n hn
    have h1 : (n : ℝ) ≤ a n := by exact_mod_cast ha'.id_le n
    have h2 : Real.exp Y0 ≤ n := by
      have := Nat.le_ceil (Real.exp Y0)
      have : (⌈Real.exp Y0⌉₊ : ℝ) ≤ n := by
        exact_mod_cast (show ⌈Real.exp Y0⌉₊ ≤ n by omega)
      linarith
    show Y0 ≤ Real.log (a n)
    rw [Real.le_log_iff_exp_le (hapos n)]
    linarith
  set r : ℝ := 1 + ε / 4 with hr
  have hr1 : 1 < r := by linarith
  have hstep : ∀ n ≥ N, r * (y n / 2 ^ n) ≤ y (n + 1) / 2 ^ (n + 1) := by
    intro n hn
    have h1 := hrec n (by omega)
    have h2 := hyN n hn
    have h3 := neg_le_abs (Real.log c)
    have h4 : ε / 2 * Y0 ≤ ε / 2 * y n := mul_le_mul_of_nonneg_left h2 (by linarith)
    have h5 : (2 + ε / 2) * y n ≤ y (n + 1) := by nlinarith
    have h6 : r * (y n / 2 ^ n) = (2 + ε / 2) * y n / 2 ^ (n + 1) := by
      rw [hr, pow_succ]; field_simp; ring
    rw [h6]
    exact div_le_div_of_nonneg_right h5 (by positivity)
  have hind : ∀ k : ℕ, r ^ k * (y N / 2 ^ N) ≤ y (N + k) / 2 ^ (N + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := hstep (N + k) (by omega)
      calc r ^ (k + 1) * (y N / 2 ^ N) = r * (r ^ k * (y N / 2 ^ N)) := by ring
        _ ≤ r * (y (N + k) / 2 ^ (N + k)) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ y (N + k + 1) / 2 ^ (N + k + 1) := h1
        _ = y (N + (k + 1)) / 2 ^ (N + (k + 1)) := by rw [← add_assoc]
  have hzN : 0 < y N / 2 ^ N / r ^ N := by
    have := hyN N le_rfl
    have : 0 < y N := by linarith
    have : 0 < r := by linarith
    positivity
  have hG : Tendsto (fun n => y n / 2 ^ n) atTop atTop := by
    refine tendsto_atTop_mono' atTop (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
      ((tendsto_pow_atTop_atTop_of_one_lt hr1).atTop_mul_const hzN)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hrN : 0 < r ^ N := by have : 0 < r := by linarith
                               positivity
    calc r ^ (N + k) * (y N / 2 ^ N / r ^ N) = r ^ k * (y N / 2 ^ N) := by
          rw [pow_add]; field_simp
      _ ≤ _ := hind k
  refine ⟨ha, ha', ?_⟩
  rintro b ⟨hb, hab⟩
  apply erdos_263.variants.folklore b
  have hev2 : ∀ᶠ n in atTop, (a n : ℝ) / b n < 2 :=
    hab.eventually (gt_mem_nhds (by norm_num))
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  have hlow : ∀ᶠ n in atTop, y n / 2 ^ n + (-1) ≤ Real.log (b n) / 2 ^ n := by
    filter_upwards [hev2] with n hn
    have hb0 : (0 : ℝ) < b n := by exact_mod_cast hb n
    have h1 : (a n : ℝ) < 2 * b n := by
      rw [div_lt_iff₀ hb0] at hn; linarith
    have h2 : y n ≤ Real.log 2 + Real.log (b n) := by
      rw [← Real.log_mul (by norm_num) hb0.ne']
      exact Real.log_le_log (hapos n) h1.le
    have h4 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have h5 : Real.log 2 / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h6 : y n / 2 ^ n ≤ Real.log 2 / 2 ^ n + Real.log (b n) / 2 ^ n := by
      rw [← add_div]; exact div_le_div_of_nonneg_right h2 (by positivity)
    linarith
  have hT2 : Tendsto (fun n => Real.log (b n) / 2 ^ n) atTop atTop :=
    tendsto_atTop_mono' atTop hlow (tendsto_atTop_add_const_right _ (-1) hG)
  refine (Real.tendsto_exp_atTop.comp hT2).congr (fun n => ?_)
  have hb0 : (0 : ℝ) < b n := by exact_mod_cast hb n
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos hb0]
  congr 1
  ring

theorem erdos_263.variants.super_doubly_exponential (a: ℕ -> ℕ)
    (ha : ∀ n : ℕ, a n > 0)
    (ha' : StrictMono a)
    (ha'' : ∃ ε : ℝ, ε > 0 ∧
      Filter.atTop.liminf (fun n : ℕ => (a (n + 1) : ℝ) / a n ^ (2 + ε)) > 0) :
    IsIrrationalitySequence a := by
  obtain ⟨ε, hε, hl⟩ := ha''
  set l := Filter.atTop.liminf (fun n : ℕ => (a (n + 1) : ℝ) / a n ^ (2 + ε)) with hldef
  have hbdd : IsBoundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (a (n + 1) : ℝ) / a n ^ (2 + ε)) :=
    ⟨0, eventually_map.2 (Eventually.of_forall fun n =>
      div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))⟩
  have hev := Filter.eventually_lt_of_lt_liminf (show l / 2 < l by linarith) hbdd
  refine erdos_263.variants.super_doubly_exponential_eventual a ha ha'
    ⟨ε, l / 2, hε, by linarith, ?_⟩
  filter_upwards [hev] with n hn
  have hp : (0:ℝ) < (a n : ℝ) ^ (2 + ε) := by
    have : (0:ℝ) < a n := by exact_mod_cast ha n
    positivity
  rw [lt_div_iff₀ hp] at hn
  exact hn.le

end Erdos263

#print axioms Erdos263.erdos_263.variants.folklore
#print axioms Erdos263.erdos_263.variants.super_doubly_exponential_eventual
#print axioms Erdos263.erdos_263.variants.super_doubly_exponential
