import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace Nat

def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p^k ∣ n

instance Full.decide : ∀ k n, Decidable (Full k n) := by
  intro k n
  dsimp [Full]
  infer_instance

abbrev Powerful : ℕ → Prop := (2).Full

instance Powerful.decide : ∀ n, Decidable (Powerful n) := by
  intro n
  dsimp [Powerful, Full]
  apply Finset.decidableDforallFinset

end Nat

open Nat Filter Topology

namespace Erdos942

def erdos_942.h (n : ℕ) : ℕ := ((Finset.Ico (n ^ 2) ((n + 1) ^ 2)).filter Powerful).card

lemma powerful_mk (a p : ℕ) : Nat.Powerful (a ^ 2 * p ^ 3) := by
  intro r hr
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hd : r ∣ a ^ 2 * p ^ 3 := Nat.dvd_of_mem_primeFactors hr
  rcases (Nat.Prime.dvd_mul hrp).1 hd with h | h
  · exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (hrp.dvd_of_dvd_pow h) 2) _
  · exact Dvd.dvd.mul_left ((pow_dvd_pow_of_dvd (hrp.dvd_of_dvd_pow h) 2).trans
      (pow_dvd_pow p (by decide))) _

lemma key_ne {p r a b : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r) (ha : a ≠ 0)
    (hb : b ≠ 0) : a ^ 2 * p ^ 3 ≠ b ^ 2 * r ^ 3 := by
  intro h
  have := congrArg (fun x => x.factorization p) h
  rw [Nat.factorization_mul (pow_ne_zero _ ha) (pow_ne_zero _ hp.ne_zero),
    Nat.factorization_mul (pow_ne_zero _ hb) (pow_ne_zero _ hr.ne_zero)] at this
  simp only [Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization, hr.factorization, Finsupp.single_apply, if_true, hpr.symm, if_false] at this
  omega

lemma floor_close {Q : ℕ} (hQ : 0 < Q) {u v : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (h : ⌊(Q:ℝ) * u⌋₊ = ⌊(Q:ℝ) * v⌋₊) : |u - v| < 1 / Q := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have h1 := Nat.floor_le (mul_nonneg hQ'.le hu0)
  have h2 := Nat.lt_floor_add_one ((Q:ℝ) * u)
  have h3 := Nat.floor_le (mul_nonneg hQ'.le hv0)
  have h4 := Nat.lt_floor_add_one ((Q:ℝ) * v)
  rw [h] at h1 h2
  have hab : |(Q:ℝ) * (u - v)| < 1 := by
    rw [abs_lt, mul_sub]; constructor <;> linarith
  rw [abs_mul, abs_of_pos hQ'] at hab
  rw [lt_div_iff₀ hQ']
  linarith [mul_comm (Q:ℝ) |u - v|]

lemma dirichlet (m Q : ℕ) (hQ : 0 < Q) (x : Fin m → ℝ) :
    ∃ q : ℕ, 0 < q ∧ ∃ z : Fin m → ℤ, ∀ i, |(q:ℝ) * x i - z i| < 1 / Q := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  let f : ℕ → (Fin m → Fin Q) := fun k i =>
    ⟨⌊(Q:ℝ) * Int.fract ((k:ℝ) * x i)⌋₊, by
      rw [Nat.floor_lt (mul_nonneg hQ'.le (Int.fract_nonneg _))]
      calc (Q:ℝ) * Int.fract ((k:ℝ) * x i) < Q * 1 :=
            mul_lt_mul_of_pos_left (Int.fract_lt_one _) hQ'
        _ = Q := mul_one _⟩
  have hc : (Finset.univ : Finset (Fin m → Fin Q)).card < (Finset.range (Q ^ m + 1)).card := by
    simp
  obtain ⟨k1, -, k2, -, hne, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := f) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have claim : ∀ a b : ℕ, a < b → f a = f b →
      ∃ q : ℕ, 0 < q ∧ ∃ z : Fin m → ℤ, ∀ i, |(q:ℝ) * x i - z i| < 1 / Q := by
    intro a b hab hfab
    refine ⟨b - a, by omega, fun i => ⌊(b:ℝ) * x i⌋ - ⌊(a:ℝ) * x i⌋, fun i => ?_⟩
    have hi : ⌊(Q:ℝ) * Int.fract ((b:ℝ) * x i)⌋₊ = ⌊(Q:ℝ) * Int.fract ((a:ℝ) * x i)⌋₊ := by
      have := congrArg (fun g => (g i : ℕ)) hfab
      exact this.symm
    have := floor_close hQ (Int.fract_nonneg _) (Int.fract_nonneg _) hi
    have e : (((b - a : ℕ) : ℝ)) * x i - ((⌊(b:ℝ) * x i⌋ - ⌊(a:ℝ) * x i⌋ : ℤ) : ℝ)
        = Int.fract ((b:ℝ) * x i) - Int.fract ((a:ℝ) * x i) := by
      rw [Nat.cast_sub hab.le, Int.fract, Int.fract]; push_cast; ring
    rw [e]; exact this
  rcases lt_or_gt_of_ne hne with h | h
  · exact claim k1 k2 h hf
  · exact claim k2 k1 h hf.symm

noncomputable abbrev pr (i : ℕ) : ℕ := Nat.nth Nat.Prime i

noncomputable def g (i : ℕ) : ℝ := (pr i : ℝ) * √(pr i : ℝ)

lemma g_pos (i : ℕ) : 0 < g i := by
  have h : (0:ℝ) < pr i := by exact_mod_cast (Nat.prime_nth_prime i).pos
  exact mul_pos h (Real.sqrt_pos.2 h)

lemma count_le (n : ℕ) {m : ℕ} (S : Finset (Fin m)) (a : Fin m → ℕ) (ha : ∀ i ∈ S, a i ≠ 0)
    (hx : ∀ i ∈ S, (n:ℝ) ≤ a i * g i ∧ (a i : ℝ) * g i < n + 1) :
    S.card ≤ erdos_942.h n := by
  unfold erdos_942.h
  refine Finset.card_le_card_of_injOn (fun i => a i ^ 2 * pr i ^ 3) ?_ ?_
  · intro i hi
    obtain ⟨h1, h2⟩ := hx i hi
    have hsq : ((a i ^ 2 * pr i ^ 3 : ℕ) : ℝ) = ((a i : ℝ) * g i) ^ 2 := by
      unfold g
      have : (0:ℝ) ≤ (pr i : ℝ) := Nat.cast_nonneg _
      push_cast
      rw [mul_pow, mul_pow, Real.sq_sqrt this]; ring
    have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, powerful_mk _ _⟩
    · have : ((n ^ 2 : ℕ) : ℝ) ≤ ((a i ^ 2 * pr i ^ 3 : ℕ) : ℝ) := by
        rw [hsq]; push_cast; exact pow_le_pow_left₀ h0 h1 2
      exact Nat.cast_le.1 this
    · have : ((a i ^ 2 * pr i ^ 3 : ℕ) : ℝ) < (((n + 1) ^ 2 : ℕ) : ℝ) := by
        rw [hsq]; push_cast; exact pow_lt_pow_left₀ h2 (le_trans h0 h1) (by norm_num)
      exact Nat.cast_lt.1 this
  · intro i hi j hj hij
    by_contra hne
    have hpne : pr i ≠ pr j := fun h =>
      hne (Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h))
    exact key_ne (Nat.prime_nth_prime _) (Nat.prime_nth_prime _) hpne (ha i hi) (ha j hj) hij

lemma key (L N0 : ℕ) : ∃ n ≥ N0, L ≤ erdos_942.h n := by
  classical
  have hP : 2 ≤ pr (2 * L) := (Nat.prime_nth_prime _).two_le
  have hle : ∀ i : Fin (2 * L), g i ≤ (pr (2 * L) : ℝ) ^ 2 := by
    intro i
    have hpi : pr i ≤ pr (2 * L) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone i.2.le
    have h1 : (1:ℝ) ≤ pr i := by exact_mod_cast (Nat.prime_nth_prime (i : ℕ)).one_lt.le
    have hs : √(pr i : ℝ) ≤ pr i := by
      calc √(pr i : ℝ) ≤ √((pr i : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by rw [sq]; exact le_mul_of_one_le_left (by linarith) h1)
        _ = pr i := Real.sqrt_sq (by linarith)
    have hP' : (pr i : ℝ) ≤ pr (2 * L) := by exact_mod_cast hpi
    unfold g
    calc (pr i : ℝ) * √(pr i : ℝ) ≤ pr (2 * L) * pr (2 * L) :=
          mul_le_mul hP' (hs.trans hP') (Real.sqrt_nonneg _) (by linarith)
      _ = (pr (2 * L) : ℝ) ^ 2 := (sq _).symm
  have hQ : 0 < 3 * pr (2 * L) ^ 2 := Nat.mul_pos (by norm_num) (pow_pos (by omega) 2)
  obtain ⟨q', hq', z, hz⟩ := dirichlet (2 * L) _ hQ (fun i => ((N0 + 1 : ℕ) : ℝ) / g i)
  have hq1 : N0 + 1 ≤ q' * (N0 + 1) := Nat.le_mul_of_pos_left _ hq'
  have hclose : ∀ i : Fin (2 * L), |((q' * (N0 + 1) : ℕ) : ℝ) - z i * g i| < 1 / 3 := by
    intro i
    have hg := g_pos i
    have hzi := hz i
    beta_reduce at hzi
    have e : ((q' * (N0 + 1) : ℕ) : ℝ) - z i * g i
        = g i * ((q' : ℝ) * (((N0 + 1 : ℕ) : ℝ) / g i) - z i) := by
      push_cast; field_simp
    rw [e, abs_mul, abs_of_pos hg]
    have hPr : (0:ℝ) < pr (2 * L) := by exact_mod_cast (show 0 < pr (2 * L) by omega)
    calc g i * |(q' : ℝ) * (((N0 + 1 : ℕ) : ℝ) / g i) - z i|
        ≤ (pr (2 * L) : ℝ) ^ 2 * |(q' : ℝ) * (((N0 + 1 : ℕ) : ℝ) / g i) - z i| :=
          mul_le_mul_of_nonneg_right (hle i) (abs_nonneg _)
      _ < (pr (2 * L) : ℝ) ^ 2 * (1 / ((3 * pr (2 * L) ^ 2 : ℕ) : ℝ)) :=
          mul_lt_mul_of_pos_left hzi (by positivity)
      _ = 1 / 3 := by push_cast; field_simp
  have hzpos : ∀ i : Fin (2 * L), 0 < z i := by
    intro i
    have hc := hclose i
    rw [abs_lt] at hc
    have hq : (1:ℝ) ≤ ((q' * (N0 + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ q' * (N0 + 1))
    have hpos : (0:ℝ) < z i * g i := by linarith [hc.1, hc.2]
    by_contra hneg
    push Not at hneg
    have h0 : (z i : ℝ) ≤ 0 := by exact_mod_cast hneg
    have := mul_le_mul_of_nonneg_right h0 (g_pos i).le
    rw [zero_mul] at this
    linarith
  have haeq : ∀ i : Fin (2 * L), (((z i).toNat : ℕ) : ℝ) = (z i : ℝ) := by
    intro i
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hzpos i).le]
  have hane : ∀ i : Fin (2 * L), (z i).toNat ≠ 0 := by
    intro i; have := hzpos i; omega
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2 * L))))
    (fun i => ((q' * (N0 + 1) : ℕ) : ℝ) ≤ z i * g i)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  by_cases hA : L ≤ (Finset.univ.filter
      (fun i : Fin (2 * L) => ((q' * (N0 + 1) : ℕ) : ℝ) ≤ z i * g i)).card
  · refine ⟨q' * (N0 + 1), by omega,
      le_trans hA (count_le _ _ (fun i => (z i).toNat) (fun i _ => hane i) ?_)⟩
    intro i hi
    rw [Finset.mem_filter] at hi
    have hc := hclose i
    rw [abs_lt] at hc
    rw [haeq]
    constructor <;> linarith [hi.2, hc.1]
  · have hB : L ≤ (Finset.univ.filter
        (fun i : Fin (2 * L) => ¬ ((q' * (N0 + 1) : ℕ) : ℝ) ≤ z i * g i)).card := by omega
    refine ⟨q' * (N0 + 1) - 1, by omega,
      le_trans hB (count_le _ _ (fun i => (z i).toNat) (fun i _ => hane i) ?_)⟩
    intro i hi
    rw [Finset.mem_filter] at hi
    have hc := hclose i
    rw [abs_lt] at hc
    rw [haeq, Nat.cast_sub (by omega : 1 ≤ q' * (N0 + 1))]
    have h2 := not_le.1 hi.2
    push_cast at h2 hc ⊢
    constructor <;> linarith [h2, hc.2]

theorem erdos_942.variants.limsup :
    atTop.limsup (((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h)) = ⊤ := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine eq_top_iff.2 (le_iInf fun N => ?_)
  have key2 : ∀ k : ℕ, (k : ℕ∞) ≤ ⨆ i ≥ N, ((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h) i := by
    intro k
    obtain ⟨n, hn, hk⟩ := key k N
    refine le_trans ?_ (le_iSup₂_of_le n hn le_rfl)
    simp only [Function.comp]
    exact_mod_cast hk
  generalize (⨆ i ≥ N, ((fun (n : ℕ) ↦ (n : ℕ∞)) ∘ erdos_942.h) i) = X at key2 ⊢
  induction X using ENat.recTopCoe with
  | top => exact le_rfl
  | coe x =>
    have := key2 (x + 1)
    exact absurd (by exact_mod_cast this : x + 1 ≤ x) (by omega)

#print axioms erdos_942.variants.limsup

end Erdos942
