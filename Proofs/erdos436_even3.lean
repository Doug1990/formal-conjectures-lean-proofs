import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.NormNum.Prime

open Filter

namespace Erdos436

def IsPowerResidue (k p a : ℕ) : Prop :=
  (a : ZMod p) ≠ 0 ∧ ∃ x : ZMod p, x ^ k = a

noncomputable def r (k m p : ℕ) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : 1 ≤ n ∧ ∀ i < m, IsPowerResidue k p (n + i)), (n : ℕ∞)

noncomputable def runLimsup (k m : ℕ) : ℕ∞ :=
  limsup (r k m) (atTop ⊓ 𝓟 {p | p.Prime})

local notation "Λ" => runLimsup

namespace T3

/-- odd numbers below `K` not divisible by 3 -/
def S (K : ℕ) : Finset ℕ := (Finset.range K).filter (fun o => o % 2 = 1 ∧ o % 3 ≠ 0)

def R (K : ℕ) : ℕ := ∏ o ∈ S K, o

lemma R_pos (K : ℕ) : 0 < R K :=
  Finset.prod_pos (fun o ho => by simp only [S, Finset.mem_filter] at ho; omega)

lemma not3 (K : ℕ) : ¬ 3 ∣ R K := by
  intro h
  obtain ⟨o, ho, hd⟩ := (Nat.prime_three.prime.dvd_finsetProd_iff _).1 h
  simp only [S, Finset.mem_filter] at ho
  omega

lemma key (K p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5) (hdv : ∀ o ∈ S K, o ∣ p + 3) :
    ∀ m : ℕ, 0 < m → m < K → m % 3 ≠ 0 → jacobiSym m p = jacobiSym m 3 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro h0 hK h3
  rcases Nat.even_or_odd m with ⟨m', hm'⟩ | hodd
  · have hm'0 : 0 < m' := by omega
    have e : ((m : ℕ) : ℤ) = 2 * (m' : ℤ) := by rw [hm']; push_cast; ring
    rw [e, jacobiSym.mul_left, jacobiSym.mul_left, ih m' (by omega) hm'0 (by omega) (by omega)]
    have hp_odd : Odd p := Nat.odd_iff.2 (by omega)
    rw [jacobiSym.at_two hp_odd, jacobiSym.at_two (by decide : Odd 3)]
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₈_nat_eq_if_mod_eight]
    simp [show p % 2 = 1 by omega, hp8]
  · have hmS : m ∈ S K := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨hK, Nat.odd_iff.1 hodd, h3⟩
    have hd := hdv m hmS
    have hp4 : p % 4 = 1 := by omega
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four hp4 hodd]
    have hmod : jacobiSym (p : ℤ) m = jacobiSym (-3) m := by
      apply jacobiSym.mod_left'
      have hz : ((m : ℕ) : ℤ) ∣ (p : ℤ) - (-3) := by
        have := Int.natCast_dvd_natCast.2 hd
        rw [show (p : ℤ) - -3 = ((p + 3 : ℕ) : ℤ) by push_cast; ring]
        exact this
      exact (Int.modEq_iff_dvd.2 hz).symm.eq
    rw [hmod, jacobiSym.neg _ hodd]
    have h13 : m % 4 = 1 ∨ m % 4 = 3 := by rcases hodd with ⟨t, rfl⟩; omega
    rcases h13 with h1 | h1
    · have q := jacobiSym.quadratic_reciprocity_one_mod_four (a := m) (b := 3) h1 (by decide)
      push_cast at q
      rw [ZMod.χ₄_nat_one_mod_four h1, q, one_mul]
    · have q := jacobiSym.quadratic_reciprocity_three_mod_four (a := 3) (b := m) (by decide) h1
      push_cast at q
      rw [ZMod.χ₄_nat_three_mod_four h1, q]
      ring

lemma nonsq (K p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5) (hdv : ∀ o ∈ S K, o ∣ p + 3)
    (m : ℕ) (hm : m % 3 = 2) (h0 : 0 < m) (hK : m < K) : ¬ IsSquare ((m : ℕ) : ZMod p) := by
  have hJ := key K p hp8 hdv m h0 hK (by omega)
  have h3 : jacobiSym m 3 = -1 := by
    rw [jacobiSym.mod_left' (a₂ := 2) (by push_cast; omega)]
    rw [jacobiSym.at_two (by decide), ZMod.χ₈_nat_eq_if_mod_eight]
    decide
  have hL : legendreSym p m = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym, hJ, h3]
  have := (legendreSym.eq_neg_one_iff (p := p)).1 hL
  simpa using this

lemma exists_p (K N0 : ℕ) :
    ∃ p > N0, p.Prime ∧ p % 8 = 5 ∧ ∀ o ∈ S K, o ∣ p + 3 := by
  obtain ⟨N, hN⟩ : ∃ N, N = 8 * R K := ⟨_, rfl⟩
  have hR := R_pos K
  have h3 := not3 K
  have hN8 : 8 ≤ N := by omega
  have : NeZero N := ⟨by omega⟩
  have hcop : Nat.Coprime (N - 3) N := by
    have d1 := Nat.gcd_dvd_left (N - 3) N
    have d2 := Nat.gcd_dvd_right (N - 3) N
    have d3 : Nat.gcd (N - 3) N ∣ 3 := by
      have := Nat.dvd_sub d2 d1
      rwa [show N - (N - 3) = 3 by omega] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 d3 with h | h
    · exact h
    · rw [h] at d2
      exfalso
      omega
  have hu : IsUnit ((N - 3 : ℕ) : ZMod N) := (ZMod.isUnit_iff_coprime _ _).2 hcop
  obtain ⟨p, hpN, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_eq_mod hu N0
  have hmod : p % N = (N - 3) % N := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hpa
  rw [Nat.mod_eq_of_lt (show N - 3 < N by omega)] at hmod
  have hdvN : N ∣ p + 3 := by
    have hd := Nat.div_add_mod p N
    exact ⟨p / N + 1, by rw [mul_add, mul_one]; omega⟩
  refine ⟨p, hpN, hp, ?_, ?_⟩
  · have : 8 ∣ p + 3 := Nat.dvd_trans ⟨R K, hN⟩ hdvN
    omega
  · intro o ho
    exact Nat.dvd_trans (Nat.dvd_trans (Finset.dvd_prod_of_mem _ ho) ⟨8, by rw [hN, R]; ring⟩) hdvN

lemma lower (k : ℕ) (hk : Even k) (M p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 5)
    (hdv : ∀ o ∈ S (M + 3), o ∣ p + 3) : (M : ℕ∞) ≤ r k 3 p := by
  have := Fact.mk hp
  refine le_iInf₂ ?_
  rintro n ⟨hn, h⟩
  by_contra hlt
  have hnM : n < M := by
    by_contra h'
    exact hlt (by exact_mod_cast (show M ≤ n by omega))
  obtain ⟨j, rfl⟩ := hk
  have : ∃ i < 3, (n + i) % 3 = 2 := by
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h | h
    · exact ⟨2, by omega, by omega⟩
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  obtain ⟨i, hi, hi2⟩ := this
  obtain ⟨_, x, hx⟩ := h i hi
  apply nonsq (M + 3) p hp8 hdv (n + i) hi2 (by omega) (by omega)
  exact ⟨x ^ j, by rw [← hx, pow_add]⟩

end T3

theorem erdos_436.variants.even_three : ∀ k ≥ 2, Even k → Λ k 3 = ⊤ := by
  intro k _ hk
  have freq : ∀ M : ℕ, ∃ᶠ p in atTop ⊓ 𝓟 {p | p.Prime}, (M : ℕ∞) ≤ r k 3 p := by
    intro M h
    rw [eventually_inf_principal, eventually_atTop] at h
    obtain ⟨N0, hN0⟩ := h
    obtain ⟨p, hpN, hp, hp8, hdv⟩ := T3.exists_p (M + 3) N0
    exact hN0 p hpN.le hp (T3.lower k hk M p hp hp8 hdv)
  by_contra hne
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
  have h1 : (((n + 1 : ℕ)) : ℕ∞) ≤ runLimsup k 3 := le_limsup_of_frequently_le' (freq (n + 1))
  rw [← hn] at h1
  have : n + 1 ≤ n := by exact_mod_cast h1
  omega

end Erdos436

#print axioms Erdos436.erdos_436.variants.even_three
