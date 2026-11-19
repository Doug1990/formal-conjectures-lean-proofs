import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.Bertrand
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.LinearCombination

open Function Set Finset

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Basic.lean. -/
def IsSidon {α : Type*} [Add α] (A : Set α) : Prop := ∀ᵉ (i₁ ∈ A) (j₁ ∈ A) (i₂ ∈ A) (j₂ ∈ A),
  i₁ + i₂ = j₁ + j₂ → (i₁ = j₁ ∧ i₂ = j₂) ∨ (i₁ = j₂ ∧ i₂ = j₁)

namespace Erdos44

namespace Bose

/-- Bose's key step: if `θ` is not in the subfield, `(θ+x)(θ+y)` determines `{x, y}`. -/
lemma key {F K : Type*} [Field F] [Field K] (ι : F →+* K) (θ : K) (hθ : ∀ c, θ ≠ ι c)
    (x y u v : F) (h : (θ + ι x) * (θ + ι y) = (θ + ι u) * (θ + ι v)) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  have h1 : θ * ι (x + y - u - v) = ι (u * v - x * y) := by
    simp only [map_sub, map_add, map_mul]
    linear_combination h
  by_cases hs : x + y - u - v = 0
  · have h2 : ι (u * v - x * y) = 0 := by rw [← h1, hs, map_zero, mul_zero]
    have h3 : u * v - x * y = 0 := (map_eq_zero ι).mp h2
    have h4 : (x - u) * (x - v) = 0 := by linear_combination x * hs + h3
    rcases mul_eq_zero.mp h4 with h5 | h5
    · left
      constructor
      · linear_combination h5
      · linear_combination hs - h5
    · right
      constructor
      · linear_combination h5
      · linear_combination hs - h5
  · exfalso
    have hne : ι (x + y - u - v) ≠ 0 := (map_ne_zero ι).mpr hs
    apply hθ ((u * v - x * y) / (x + y - u - v))
    rw [map_div₀, ← h1, mul_div_cancel_right₀ θ hne]

/-- A Sidon set of size `p` in `{1, …, p²}` for every prime `p`. -/
lemma exists_sidon (p : ℕ) (hp : p.Prime) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (p ^ 2) ∧ IsSidon (A : Set ℕ) ∧ A.card = p := by
  have := Fact.mk hp
  let K := GaloisField p 2
  have hK : Nat.card K = p ^ 2 := GaloisField.card p 2 (by norm_num)
  let ι : ZMod p →+* K := algebraMap (ZMod p) K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  let θ : K := g
  have hpow : ∀ z : K, z ≠ 0 → ∃ n : ℕ, θ ^ n = z := by
    intro z hz
    have hm : Units.mk0 z hz ∈ Submonoid.powers g :=
      (mem_powers_iff_mem_zpowers).mpr (hg _)
    obtain ⟨n, hn⟩ := Submonoid.mem_powers_iff _ _ |>.mp hm
    refine ⟨n, ?_⟩
    have := congrArg Units.val hn
    simpa [θ] using this
  have hθ : ∀ c, θ ≠ ι c := by
    intro c hc
    have hsurj : Surjective ι := by
      intro z
      by_cases hz : z = 0
      · exact ⟨0, by simp [hz]⟩
      · obtain ⟨n, hn⟩ := hpow z hz
        exact ⟨c ^ n, by rw [map_pow, ← hc, hn]⟩
    have hle := Nat.card_le_card_of_surjective ι hsurj
    rw [hK, Nat.card_eq_fintype_card, ZMod.card] at hle
    have h2 := hp.two_le
    nlinarith
  have hθx : ∀ x : ZMod p, θ + ι x ≠ 0 := by
    intro x hx
    apply hθ (-x)
    rw [map_neg]
    linear_combination hx
  have hcardU : Nat.card Kˣ ≤ p ^ 2 := by
    rw [← hK]
    exact Nat.card_le_card_of_injective _ Units.val_injective
  have hex : ∀ x : ZMod p, ∃ k, k < p ^ 2 ∧ θ ^ k = θ + ι x := by
    intro x
    obtain ⟨n, hn⟩ := hpow _ (hθx x)
    refine ⟨n % orderOf g, ?_, ?_⟩
    · exact lt_of_lt_of_le (Nat.mod_lt _ (orderOf_pos g)) (le_trans orderOf_le_card hcardU)
    · have := congrArg Units.val (pow_mod_orderOf g n)
      simp only [Units.val_pow_eq_pow_val] at this
      rw [← hn]
      exact this
  choose e he1 he2 using hex
  have einj : Injective e := by
    intro x y hxy
    have := he2 x
    rw [hxy, he2 y] at this
    exact (RingHom.injective ι) (add_left_cancel this).symm
  refine ⟨Finset.univ.image (fun x => e x + 1), ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
    obtain ⟨x, rfl⟩ := ha
    have := he1 x
    simp only [Finset.mem_Icc]
    omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hi₁ hj₁ hi₂ hj₂
    obtain ⟨x, rfl⟩ := hi₁
    obtain ⟨u, rfl⟩ := hj₁
    obtain ⟨y, rfl⟩ := hi₂
    obtain ⟨v, rfl⟩ := hj₂
    have hs : e x + e y = e u + e v := by omega
    have hprod : (θ + ι x) * (θ + ι y) = (θ + ι u) * (θ + ι v) := by
      rw [← he2, ← he2, ← he2, ← he2, ← pow_add, ← pow_add, hs]
    rcases key ι θ hθ x y u v hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; subst h1; subst h2; exact ⟨rfl, rfl⟩
    · right; subst h1; subst h2; exact ⟨rfl, rfl⟩
  · rw [Finset.card_image_of_injective _ (fun a b h => einj (by simpa using h)),
      Finset.card_univ, ZMod.card]

lemma exists_sidon' (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSidon (A : Set ℕ) ∧ Nat.sqrt N + 1 ≤ 2 * A.card := by
  have hs1 : 1 ≤ Nat.sqrt N := Nat.le_sqrt.mpr (by omega)
  by_cases hs : Nat.sqrt N < 2
  · refine ⟨{1}, ?_, ?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_singleton] at ha
      simp only [Finset.mem_Icc]
      omega
    · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ _
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hi₁ hj₁ hi₂ hj₂
      left
      exact ⟨hi₁.trans hj₁.symm, hi₂.trans hj₂.symm⟩
    · simp only [Finset.card_singleton]
      omega
  · obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt N / 2) (by omega)
    obtain ⟨A, hA, hS, hc⟩ := exists_sidon p hp
    refine ⟨A, ?_, hS, ?_⟩
    · have hpN : p ^ 2 ≤ N := by
        have h1 : p ≤ Nat.sqrt N := by omega
        have h2 := Nat.sqrt_le' N
        calc p ^ 2 ≤ Nat.sqrt N ^ 2 := Nat.pow_le_pow_left h1 2
          _ ≤ N := h2
      intro a ha
      have := Finset.mem_Icc.mp (hA ha)
      exact Finset.mem_Icc.mpr ⟨this.1, le_trans this.2 hpN⟩
    · rw [hc]
      omega

end Bose

/--
For any `N`, there exists a Sidon set of size at least `√N/2`.
-/
theorem sidon_set_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    ∃ᵉ (A ⊆ Finset.Icc 1 N), IsSidon (A : Set ℕ) ∧ Real.sqrt N / 2 ≤ A.card := by
  obtain ⟨A, hA, hS, hc⟩ := Bose.exists_sidon' N hN
  refine ⟨A, hA, hS, ?_⟩
  have h1 : (N : ℝ) < ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' N
  have h2 : Real.sqrt N < ((Nat.sqrt N + 1 : ℕ) : ℝ) :=
    (Real.sqrt_lt' (by positivity)).mpr h1
  have h3 : ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * (A.card : ℝ) := by exact_mod_cast hc
  linarith

end Erdos44

#print axioms Erdos44.sidon_set_lower_bound
