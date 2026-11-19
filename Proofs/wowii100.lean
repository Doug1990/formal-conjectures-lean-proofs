import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Restated from FormalConjecturesForMathlib/Combinatorics/SimpleGraph/{Independence,Degrees}.lean. -/
namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

end SimpleGraph

namespace WOWII100Aux

open SimpleGraph

lemma poly (L k : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k) :
    4*L*(L+2*k-2)^2 < L*(L+k)*(L+k-1)^2 + (L+k)*k*(2*L+3*k-2) := by
  obtain ⟨p, hp, rfl⟩ : ∃ p, 0 ≤ p ∧ L = 1 + p := ⟨L - 1, by linarith, by ring⟩
  obtain ⟨q, hq, rfl⟩ : ∃ q, 0 ≤ q ∧ k = 1 + q := ⟨k - 1, by linarith, by ring⟩
  nlinarith [mul_nonneg hp hq, sq_nonneg (p^2 - 1/2), mul_nonneg (mul_nonneg hp hq) (sq_nonneg (p - 1/2)),
    mul_nonneg (sq_nonneg q) (sq_nonneg (p - 2/3)), mul_nonneg hp (sq_nonneg (p - q)),
    mul_nonneg hq (sq_nonneg (p - q)), mul_nonneg hp (sq_nonneg (q - 1)),
    mul_nonneg hq (sq_nonneg (p - 1)), mul_nonneg hq (sq_nonneg (q - 1)),
    mul_nonneg hp (sq_nonneg (p - 1)), mul_nonneg (mul_nonneg hp hq) (sq_nonneg (q - 1)),
    sq_nonneg (p - 1), sq_nonneg (q - 1), sq_nonneg (p - q),
    mul_nonneg (by linarith : (0:ℝ) ≤ p + q + 1) (sq_nonneg (p - q)),
    mul_nonneg (by linarith : (0:ℝ) ≤ p + q + 1) (sq_nonneg (p - 1)),
    mul_nonneg (by linarith : (0:ℝ) ≤ p + q + 1) (sq_nonneg (q - 1)),
    mul_nonneg (mul_nonneg hp hq) hp, mul_nonneg (mul_nonneg hp hq) hq]

lemma final (A L t X Q : ℝ) (hA : 1 ≤ A) (hL0 : 0 ≤ L) (hLi : L + 1 ≤ A ∨ A ≤ L)
    (hLz : L = 0 ∨ 1 ≤ L) (hQ1 : A*(A-1)^2 ≤ Q)
    (hQ2 : L + 1 ≤ A → A*(A-1)^2 + (3*A-2-L)*X ≤ Q) (hX1 : L + 1 ≤ A → t*(A-L) ≤ X)
    (hX2 : X ≤ A*(t-1)) :
    4*A - 4 - 2*L < Real.sqrt Q := by
  by_cases hm : 4*A - 4 - 2*L < 0
  · exact lt_of_lt_of_le hm (Real.sqrt_nonneg _)
  have hm' := not_lt.1 hm
  rw [Real.lt_sqrt hm']
  rcases hLi with hk | hk
  · have h2 := hQ2 hk
    have h1 := hX1 hk
    have htL : A ≤ t * L := by nlinarith
    have hLpos : 1 ≤ L := by
      rcases hLz with h0 | h0
      · rw [h0, mul_zero] at htL; linarith
      · exact h0
    have hP := poly L (A - L) hLpos (by linarith)
    have hAL : 0 ≤ A - L := by linarith
    have hLX : A * (A - L) ≤ L * X := by
      nlinarith [mul_le_mul_of_nonneg_right htL hAL, mul_le_mul_of_nonneg_left h1 hL0]
    have hc : 0 ≤ 3*A - 2 - L := by linarith
    have key : L*A*(A-1)^2 + A*(A-L)*(3*A-2-L) ≤ L * Q := by
      nlinarith [mul_le_mul_of_nonneg_left h2 hL0, mul_le_mul_of_nonneg_left hLX hc]
    have hlt : L * (4*A-4-2*L)^2 < L * Q := by nlinarith
    exact lt_of_mul_lt_mul_left hlt hL0
  · have hA2 : 2 ≤ A := by linarith
    have hle : 4*A - 4 - 2*L ≤ 2*(A-2) := by linarith
    have hsq : (4*A - 4 - 2*L)^2 ≤ (2*(A-2))^2 := pow_le_pow_left₀ hm' hle 2
    have hr : 0 ≤ A - 2 := by linarith
    nlinarith [mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg hr hr]

variable {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj]

lemma cS {S : Finset α} (hS : G.IsIndepSet (S : Set α)) {s : α} (hs : s ∈ S) :
    (S.card - 1) + (Sᶜ.filter (fun v => ¬ G.Adj s v)).card ≤ Gᶜ.degree s := by
  rw [← card_neighborFinset_eq_degree]
  have hsub : S.erase s ∪ Sᶜ.filter (fun v => ¬ G.Adj s v) ⊆ Gᶜ.neighborFinset s := by
    intro w hw
    rw [mem_neighborFinset, compl_adj]
    rcases Finset.mem_union.1 hw with h | h
    · obtain ⟨hne, hwS⟩ := Finset.mem_erase.1 h
      exact ⟨Ne.symm hne, hS hs hwS (Ne.symm hne)⟩
    · obtain ⟨hwT, hna⟩ := Finset.mem_filter.1 h
      refine ⟨?_, hna⟩
      rintro rfl
      exact (Finset.mem_compl.1 hwT) hs
  have hdisj : Disjoint (S.erase s) (Sᶜ.filter (fun v => ¬ G.Adj s v)) := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    exact (Finset.mem_compl.1 (Finset.mem_filter.1 h2).1) (Finset.mem_of_mem_erase h1)
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hs] at this
  exact this

lemma cT {S : Finset α} {v : α} (hv : v ∈ Sᶜ) :
    (S.filter (fun s => ¬ G.Adj s v)).card ≤ Gᶜ.degree v := by
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsS, hna⟩ := Finset.mem_filter.1 hs
  rw [mem_neighborFinset, compl_adj]
  refine ⟨?_, fun h => hna h.symm⟩
  rintro rfl
  exact (Finset.mem_compl.1 hv) hsS

omit [DecidableEq α] in
lemma yT {S : Finset α} (hS : G.IsIndepSet (S : Set α)) (v : α) :
    (S.filter (fun s => G.Adj s v)).card ≤ (G.induce (G.neighborSet v)).indepNum := by
  let Q : Finset (G.neighborSet v) :=
    (S.filter (fun s => G.Adj s v)).subtype (fun w => w ∈ G.neighborSet v)
  have hQ : Q.card = (S.filter (fun s => G.Adj s v)).card := by
    rw [Finset.card_subtype]
    congr 1
    apply Finset.filter_true_of_mem
    intro w hw
    exact ((Finset.mem_filter.1 hw).2).symm
  have hind : (G.induce (G.neighborSet v)).IsIndepSet (Q : Set _) := by
    intro a ha b hb hab hadj
    have ha' : a.1 ∈ S.filter (fun s => G.Adj s v) := Finset.mem_subtype.1 ha
    have hb' : b.1 ∈ S.filter (fun s => G.Adj s v) := Finset.mem_subtype.1 hb
    exact hS (Finset.mem_filter.1 ha').1 (Finset.mem_filter.1 hb').1
      (fun e => hab (Subtype.ext e)) hadj
  rw [← hQ]
  exact hind.card_le_indepNum

lemma dpos [Nontrivial α] (hc : G.Connected) {S : Finset α} (hS : G.IsIndepSet (S : Set α))
    {s : α} (hs : s ∈ S) : 1 ≤ (Sᶜ.filter (fun v => G.Adj s v)).card := by
  obtain ⟨w, hw⟩ := exists_ne s
  obtain ⟨p⟩ := hc.preconnected s w
  cases p with
  | nil => exact absurd rfl hw
  | cons hadj _ =>
    apply Finset.card_pos.2
    refine ⟨_, Finset.mem_filter.2 ⟨Finset.mem_compl.2 ?_, hadj⟩⟩
    intro hu
    exact hS hs hu (G.ne_of_adj hadj) hadj

end WOWII100Aux

namespace WrittenOnTheWallII.GraphConjecture100

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]

theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  intro maxL
  have hmax : ∀ v, indepNeighborsCard G v ≤ maxL := fun v =>
    Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  clear_value maxL
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  have hSi := hS.isIndepSet
  have hA1 : 1 ≤ S.card := by
    obtain ⟨v⟩ := (inferInstance : Nonempty α)
    have h1 : G.IsIndepSet (({v} : Finset α) : Set α) := by
      rw [Finset.coe_singleton]; exact Set.pairwise_singleton _ _
    have := h1.card_le_indepNum
    rw [Finset.card_singleton] at this
    rw [hS.card_eq]; exact this
  have hLv : ∀ v, (S.filter (fun s => G.Adj s v)).card ≤ maxL := by
    intro v
    exact (WOWII100Aux.yT G hSi v).trans (hmax v)
  have hsplit : ∀ s, (Sᶜ.filter (fun v => G.Adj s v)).card
      + (Sᶜ.filter (fun v => ¬ G.Adj s v)).card = Sᶜ.card :=
    fun s => Finset.card_filter_add_card_filter_not _
  have hsplitT : ∀ v, (S.filter (fun s => G.Adj s v)).card
      + (S.filter (fun s => ¬ G.Adj s v)).card = S.card :=
    fun v => Finset.card_filter_add_card_filter_not _
  have hdc : ∑ s ∈ S, (Sᶜ.filter (fun v => ¬ G.Adj s v)).card
      = ∑ v ∈ Sᶜ, (S.filter (fun s => ¬ G.Adj s v)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ s ∈ S, ((Sᶜ.filter (fun v => ¬ G.Adj s v)).card : ℝ) :=
    ⟨_, rfl⟩
  have hXZ : X = ∑ v ∈ Sᶜ, ((S.filter (fun s => ¬ G.Adj s v)).card : ℝ) := by
    rw [hX]; exact_mod_cast hdc
  have hX0 : 0 ≤ X := by
    rw [hX]; exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  -- vertices of S
  have hcs : ∀ s ∈ S, ((S.card : ℝ) - 1 + ((Sᶜ.filter (fun v => ¬ G.Adj s v)).card : ℝ))
      ≤ (Gᶜ.degree s : ℝ) := by
    intro s hs
    have h0 := WOWII100Aux.cS G hSi hs
    have h' : ((S.card - 1 + (Sᶜ.filter (fun v => ¬ G.Adj s v)).card : ℕ) : ℝ)
        ≤ (Gᶜ.degree s : ℝ) := by exact_mod_cast h0
    rw [Nat.cast_add, Nat.cast_sub hA1, Nat.cast_one] at h'
    exact h'
  have hA1r : (1 : ℝ) ≤ S.card := by exact_mod_cast hA1
  have hQS : (S.card : ℝ) * ((S.card : ℝ) - 1)^2 + 2*((S.card : ℝ) - 1)*X
      ≤ ∑ s ∈ S, (Gᶜ.degree s : ℝ)^2 := by
    rw [hX, Finset.mul_sum,
      show (S.card : ℝ) * ((S.card : ℝ) - 1)^2 = ∑ s ∈ S, ((S.card : ℝ) - 1)^2 by
        rw [Finset.sum_const, nsmul_eq_mul],
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s hs
    have h1 := hcs s hs
    have h2 : (0:ℝ) ≤ ((Sᶜ.filter (fun v => ¬ G.Adj s v)).card : ℝ) := Nat.cast_nonneg _
    have h3 : (0:ℝ) ≤ (S.card : ℝ) - 1 := by linarith
    nlinarith
  have hQT0 : 0 ≤ ∑ v ∈ Sᶜ, (Gᶜ.degree v : ℝ)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hQ : ∑ v, (Gᶜ.degree v : ℝ)^2
      = ∑ s ∈ S, (Gᶜ.degree s : ℝ)^2 + ∑ v ∈ Sᶜ, (Gᶜ.degree v : ℝ)^2 :=
    (Finset.sum_add_sum_compl S _).symm
  have hzv : (maxL : ℝ) + 1 ≤ S.card → ∀ v ∈ Sᶜ,
      (S.card : ℝ) - maxL ≤ ((S.filter (fun s => ¬ G.Adj s v)).card : ℝ) := by
    intro _ v _
    have e1 := hsplitT v
    have e2 := hLv v
    have : S.card ≤ (S.filter (fun s => ¬ G.Adj s v)).card + maxL := by omega
    have : (S.card : ℝ) ≤ ((S.filter (fun s => ¬ G.Adj s v)).card : ℝ) + maxL := by
      exact_mod_cast this
    linarith
  have hQT : (maxL : ℝ) + 1 ≤ S.card →
      ((S.card : ℝ) - maxL) * X ≤ ∑ v ∈ Sᶜ, (Gᶜ.degree v : ℝ)^2 := by
    intro hk
    rw [hXZ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v hv
    have h1 := hzv hk v hv
    have h2 : ((S.filter (fun s => ¬ G.Adj s v)).card : ℝ) ≤ (Gᶜ.degree v : ℝ) := by
      exact_mod_cast WOWII100Aux.cT G hv
    have h3 : (0:ℝ) ≤ (S.card : ℝ) - maxL := by linarith
    nlinarith
  have hX1 : (maxL : ℝ) + 1 ≤ S.card → (Sᶜ.card : ℝ) * ((S.card : ℝ) - maxL) ≤ X := by
    intro hk
    rw [hXZ]
    have := Finset.card_nsmul_le_sum Sᶜ (fun v => ((S.filter (fun s => ¬ G.Adj s v)).card : ℝ))
      ((S.card : ℝ) - maxL) (hzv hk)
    rwa [nsmul_eq_mul] at this
  have hX2 : X ≤ (S.card : ℝ) * ((Sᶜ.card : ℝ) - 1) := by
    rw [hX]
    have := Finset.sum_le_card_nsmul S (fun s => ((Sᶜ.filter (fun v => ¬ G.Adj s v)).card : ℝ))
      ((Sᶜ.card : ℝ) - 1) (by
        intro s hs
        have e1 := hsplit s
        have e2 := WOWII100Aux.dpos G h hSi hs
        have : (Sᶜ.filter (fun v => ¬ G.Adj s v)).card + 1 ≤ Sᶜ.card := by omega
        have : (((Sᶜ.filter (fun v => ¬ G.Adj s v)).card : ℝ)) + 1 ≤ (Sᶜ.card : ℝ) := by
          exact_mod_cast this
        show _ ≤ _
        linarith)
    rwa [nsmul_eq_mul] at this
  have hLi : (maxL : ℝ) + 1 ≤ S.card ∨ (S.card : ℝ) ≤ maxL := by
    rcases le_or_gt S.card maxL with h1 | h1
    · right; exact_mod_cast h1
    · left; exact_mod_cast h1
  have hLz : (maxL : ℝ) = 0 ∨ 1 ≤ (maxL : ℝ) := by
    rcases Nat.eq_zero_or_pos maxL with h1 | h1
    · left; exact_mod_cast h1
    · right; exact_mod_cast h1
  have hfin := WOWII100Aux.final (S.card : ℝ) (maxL : ℝ) (Sᶜ.card : ℝ) X
    (∑ v, (Gᶜ.degree v : ℝ)^2) hA1r (Nat.cast_nonneg _) hLi hLz
    (by rw [hQ]; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (S.card : ℝ) - 1) hX0])
    (fun hk => by rw [hQ]; have := hQT hk; linarith)
    hX1 hX2
  have hint : (S.card : ℤ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
    rw [Int.le_ceil_iff]
    push_cast
    unfold degreeL2Norm
    linarith
  rw [← hS.card_eq]
  exact_mod_cast hint

end WrittenOnTheWallII.GraphConjecture100

#print axioms WrittenOnTheWallII.GraphConjecture100.conjecture100
