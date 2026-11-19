import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Max

namespace Erdos1055

def IsOfClass : ℕ+ → ℕ → Prop := fun r ↦
  PNat.caseStrongInductionOn (p := fun (_ : ℕ+) ↦ ℕ → Prop) r
    (fun p ↦ (p + 1).primeFactors ⊆ {2, 3})
    (fun n H p ↦
      (∀ (m : ℕ+) (hm : m ≤ n), ¬ H m hm p) ∧
      (∀ r ∈ (p + 1).primeFactors,
        ∃ (m : ℕ+) (hm : m ≤ n), H m hm r) ∧
      (∃ r ∈ (p + 1).primeFactors,
        ∀ (m : ℕ+) (hm : m ≤ n), H m hm r → m = n))

theorem C_one (p : ℕ) : IsOfClass 1 p ↔ (p + 1).primeFactors ⊆ {2, 3} := by
  unfold IsOfClass PNat.caseStrongInductionOn
  rw [PNat.strongInductionOn.eq_1]
  exact Iff.rfl

theorem C_succ (n : ℕ+) (p : ℕ) : IsOfClass (n + 1) p ↔
    ((∀ (m : ℕ+) (_ : m ≤ n), ¬ IsOfClass m p) ∧
      (∀ r ∈ (p + 1).primeFactors, ∃ (m : ℕ+) (_ : m ≤ n), IsOfClass m r) ∧
      (∃ r ∈ (p + 1).primeFactors, ∀ (m : ℕ+) (_ : m ≤ n), IsOfClass m r → m = n)) := by
  obtain ⟨k, hk⟩ := n
  cases k with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ k =>
    unfold IsOfClass PNat.caseStrongInductionOn
    rw [PNat.strongInductionOn.eq_1]
    exact Iff.rfl

theorem exists_pred {r s : ℕ+} (h : r < s) : ∃ n : ℕ+, s = n + 1 ∧ r ≤ n := by
  have h1 : (r : ℕ) < s := (PNat.coe_lt_coe _ _).2 h
  have h2 : 0 < (r : ℕ) := r.pos
  refine ⟨(⟨(s : ℕ) - 1, by omega⟩ : ℕ+), ?_, ?_⟩
  · apply PNat.eq
    show (s : ℕ) = ((s : ℕ) - 1) + 1
    omega
  · exact (PNat.coe_le_coe _ _).1 (by show (r : ℕ) ≤ (s : ℕ) - 1; omega)

theorem C_uniq {r s : ℕ+} {p : ℕ} (hr : IsOfClass r p) (hs : IsOfClass s p) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · obtain ⟨n, rfl, hrn⟩ := exists_pred h
    exact absurd hr (((C_succ n p).1 hs).1 r hrn)
  · exact h
  · obtain ⟨n, rfl, hsn⟩ := exists_pred h
    exact absurd hs (((C_succ n p).1 hr).1 s hsn)

theorem factor_lt {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q ∈ (p + 1).primeFactors) :
    q < p := by
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hq, hd, -⟩ := hq
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h2 := hp.two_le
  have hev : 2 ∣ p + 1 := by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩
  have hle : q ≤ p + 1 := Nat.le_of_dvd (by omega) hd
  have hne1 : q ≠ p + 1 := by
    rintro rfl
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hev
    omega
  have hne2 : q ≠ p := by
    rintro rfl
    have : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).1 hd
    have := Nat.le_of_dvd (by omega) this
    omega
  omega

theorem C_exists (p : ℕ) (hp : p.Prime) : ∃ r, IsOfClass r p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  by_cases h2 : p = 2
  · subst h2
    refine ⟨1, ?_⟩
    rw [C_one]
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq, hd, -⟩ := hq
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 hd
    simp [this]
  have hc : ∀ q ∈ (p + 1).primeFactors, ∃ m, IsOfClass m q := fun q hq =>
    ih q (factor_lt hp h2 hq) (Nat.prime_of_mem_primeFactors hq)
  choose! c hc using hc
  have hne : (p + 1).primeFactors.Nonempty :=
    Nat.nonempty_primeFactors.2 (by have := hp.two_le; omega)
  obtain ⟨q0, hq0, hmax⟩ := Finset.exists_max_image _ c hne
  by_cases hex : ∃ m, m ≤ c q0 ∧ IsOfClass m p
  · obtain ⟨m, -, hm⟩ := hex
    exact ⟨m, hm⟩
  · refine ⟨c q0 + 1, (C_succ _ p).2 ⟨fun m hm hmp => hex ⟨m, hm, hmp⟩,
      fun r hr => ⟨c r, hmax r hr, hc r hr⟩,
      ⟨q0, hq0, fun m _ hmq => C_uniq hmq (hc q0 hq0)⟩⟩⟩

theorem C_down (n : ℕ+) (p : ℕ) (h : IsOfClass (n + 1) p) : ∃ q, q.Prime ∧ IsOfClass n q := by
  obtain ⟨-, h2, ⟨r, hr, h3⟩⟩ := (C_succ n p).1 h
  obtain ⟨m, hm, hmr⟩ := h2 r hr
  exact ⟨r, Nat.prime_of_mem_primeFactors hr, (h3 m hm hmr) ▸ hmr⟩

theorem C_desc (r : ℕ+) : ∀ k : ℕ, ∀ s : ℕ+, (s : ℕ) = r + k → ∀ p, p.Prime →
    IsOfClass s p → ∃ q, q.Prime ∧ IsOfClass r q := by
  intro k
  induction k with
  | zero =>
    intro s hs p hp hsp
    have : s = r := PNat.eq (by simpa using hs)
    subst this
    exact ⟨p, hp, hsp⟩
  | succ k ih =>
    intro s hs p hp hsp
    obtain ⟨n, rfl, -⟩ := exists_pred (r := r) (s := s) (by rw [← PNat.coe_lt_coe]; omega)
    obtain ⟨q, hq, hnq⟩ := C_down n p hsp
    rw [PNat.add_coe, PNat.one_coe] at hs
    exact ih n (by omega) q hq hnq

theorem C_lt {p q : ℕ} (hp5 : 5 ≤ p) (hpq : p ∈ (q + 1).primeFactors) {t : ℕ+}
    (ht : IsOfClass t q) {s : ℕ+} (hs : IsOfClass s p) : s < t := by
  by_cases ht1 : t = 1
  · subst ht1
    rw [C_one] at ht
    have := ht hpq
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  · obtain ⟨n, rfl, -⟩ := exists_pred (r := 1) (s := t) (lt_of_le_of_ne one_le (Ne.symm ht1))
    obtain ⟨-, h2, -⟩ := (C_succ n q).1 ht
    obtain ⟨m, hm, hmp⟩ := h2 p hpq
    have := C_uniq hmp hs
    subst this
    rw [← PNat.coe_le_coe] at hm
    rw [← PNat.coe_lt_coe, PNat.add_coe, PNat.one_coe]
    omega

theorem step (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (s : ℕ+) (hs : IsOfClass s p) :
    ∃ q, q.Prime ∧ 5 ≤ q ∧ ∃ t, s < t ∧ IsOfClass t q := by
  have hcop : Nat.Coprime (p - 1) p := by
    have h := (Nat.coprime_self_add_right (m := p - 1) (n := 1)).2 (Nat.coprime_one_right _)
    rwa [Nat.sub_add_cancel (by omega)] at h
  obtain ⟨q, hqp, hq, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq p (q := p) (a := p - 1) (by omega) hcop
  have hdvd : p ∣ q + 1 := by
    have := Nat.ModEq.add_right 1 hmod
    rw [Nat.sub_add_cancel (by omega)] at this
    exact (Nat.modEq_zero_iff_dvd).1 (this.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
  have hmem : p ∈ (q + 1).primeFactors := Nat.mem_primeFactors.2 ⟨hp, hdvd, by omega⟩
  obtain ⟨t, ht⟩ := C_exists q hq
  exact ⟨q, hq, by omega, t, C_lt hp5 hmem ht hs, ht⟩

theorem C_five : IsOfClass 1 5 := by
  rw [C_one]
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  obtain ⟨hq, hd, -⟩ := hq
  have : q ∣ 2 * 3 := hd
  rcases (Nat.Prime.dvd_mul hq).1 this with h | h
  · simp [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h]
  · simp [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h]

theorem big (r : ℕ) : ∃ p, p.Prime ∧ 5 ≤ p ∧ ∃ s : ℕ+, r ≤ (s : ℕ) ∧ IsOfClass s p := by
  induction r with
  | zero => exact ⟨5, Nat.prime_five, le_rfl, 1, Nat.zero_le _, C_five⟩
  | succ r ih =>
    obtain ⟨p, hp, hp5, s, hrs, hs⟩ := ih
    obtain ⟨q, hq, hq5, t, hst, ht⟩ := step p hp hp5 s hs
    exact ⟨q, hq, hq5, t, by have := (PNat.coe_lt_coe _ _).2 hst; omega, ht⟩

theorem exists_p (r : ℕ+) : ∃ p, p.Prime ∧ IsOfClass r p := by
  obtain ⟨p, hp, -, s, hrs, hs⟩ := big r
  exact C_desc r ((s : ℕ) - r) s (by omega) p hp hs

end Erdos1055

#print axioms Erdos1055.exists_p
