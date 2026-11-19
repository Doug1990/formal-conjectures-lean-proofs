import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Pi

/-- Restated from FormalConjecturesForMathlib/Combinatorics/Additive/VCDim.lean
(additive version of `HasMulVCNDimAtMost`). -/
def HasAddVCNDimAtMost {G : Type*} [AddCommGroup G] (A : Set G) (n d : ℕ) : Prop :=
  ∀ (x : Fin n → Fin (d + 1) → G) (y : Set (Fin n → Fin (d + 1)) → G),
    ¬ ∀ i s, y s + ∑ k, x k (i k) ∈ A ↔ i ∈ s

namespace VCDimConvex

namespace VCN

/-- Abstract paraboloid point. -/
def P {m : ℕ} (e : Fin m → ℝ) : ℝ × (Fin m → ℝ) := (∑ j, e j ^ 2, e)

lemma not_mem {m : ℕ} (G' : Set (Fin m → ℝ)) (p : Fin m → ℝ) (hp : p ∉ G') :
    P p ∉ convexHull ℝ (P '' G') := by
  intro hmem
  let f : ℝ × (Fin m → ℝ) → ℝ := fun w => w.1 - 2 * ∑ j, p j * w.2 j
  have hlin : IsLinearMap ℝ f := by
    refine ⟨fun x y => ?_, fun c x => ?_⟩
    · simp only [f, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      ring
    · have : ∀ j, p j * (c * x.2 j) = c * (p j * x.2 j) := fun j => by ring
      simp only [f, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, this,
        ← Finset.mul_sum]
      ring
  have hval : ∀ e : Fin m → ℝ, f (P e) + ∑ j, p j ^ 2 = ∑ j, (e j - p j) ^ 2 := by
    intro e
    have : ∀ j, (e j - p j) ^ 2 = e j ^ 2 - 2 * (p j * e j) + p j ^ 2 := fun j => by ring
    simp only [f, P, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsub : P '' G' ⊆ {w | -(∑ j, p j ^ 2) < f w} := by
    rintro _ ⟨e, he, rfl⟩
    show -(∑ j, p j ^ 2) < f (P e)
    have hne : e ≠ p := fun h => hp (h ▸ he)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
    have hpos : 0 < ∑ j, (e j - p j) ^ 2 := by
      refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨j, Finset.mem_univ _, ?_⟩
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hj)))
    linarith [hval e]
  have h : -(∑ j, p j ^ 2) < f (P p) := convexHull_min hsub (convex_halfSpace_gt hlin _) hmem
  have h0 := hval p
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at h0
  linarith

lemma exists_inj (X : Type*) [Countable X] : ∃ q : Set X → ℝ, Function.Injective q := by
  obtain ⟨g, hg⟩ := Countable.exists_injective_nat X
  have h : Cardinal.mk (Set ℕ) = Cardinal.mk ℝ := by
    rw [Cardinal.mk_set, Cardinal.mk_nat, Cardinal.mk_real, Cardinal.two_power_aleph0]
  obtain ⟨e⟩ := Cardinal.eq.1 h
  exact ⟨fun s => e (g '' s), e.injective.comp (Set.image_injective.2 hg)⟩

variable {n : ℕ}

/-- The point with coordinates `a k` (k < n) and `r` (last coordinate). -/
def V (a : Fin n → ℝ) (r : ℝ) : Fin (n + 1) → ℝ :=
  Pi.single (Fin.last n) r + ∑ k, Pi.single (Fin.castSucc k) (a k)

lemma V_cs (a : Fin n → ℝ) (r : ℝ) (k : Fin n) : V a r k.castSucc = a k := by
  simp [V, Finset.sum_apply, Pi.single_apply, Fin.castSucc_ne_last]

lemma V_last (a : Fin n → ℝ) (r : ℝ) : V a r (Fin.last n) = r := by
  simp [V, Finset.sum_apply, Fin.castSucc_ne_last]

lemma V_inj {a a' : Fin n → ℝ} {r r' : ℝ} (h : V a r = V a' r') : a = a' ∧ r = r' := by
  refine ⟨funext fun k => ?_, ?_⟩
  · have := congrFun h k.castSucc
    rwa [V_cs, V_cs] at this
  · have := congrFun h (Fin.last n)
    rwa [V_last, V_last] at this

lemma sum_eq (a : Fin n → ℝ) (r : ℝ) :
    ((r ^ 2, Pi.single (Fin.last n) r) : ℝ × (Fin (n + 1) → ℝ)) +
      ∑ k, ((a k ^ 2, Pi.single (Fin.castSucc k) (a k)) : ℝ × (Fin (n + 1) → ℝ)) =
      P (V a r) := by
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, P]
    rw [Fin.sum_univ_castSucc]
    simp only [V_cs, V_last]
    ring
  · simp only [Prod.snd_add, Prod.snd_sum, P, V]

/-- Version in `ℝ × ℝ^(n+1)`. -/
lemma main (n : ℕ) : ∃ C : Set (ℝ × (Fin (n + 1) → ℝ)), Convex ℝ C ∧
    ∀ d, ¬ HasAddVCNDimAtMost C n d := by
  obtain ⟨q, hq⟩ := exists_inj (Fin n → ℕ)
  let G' : Set (Fin (n + 1) → ℝ) :=
    {e | ∃ a : Fin n → ℕ, ∃ T : Set (Fin n → ℕ), a ∈ T ∧ e = V (fun k => (a k : ℝ)) (q T)}
  refine ⟨convexHull ℝ (P '' G'), convex_convexHull ℝ _, fun d hd => ?_⟩
  let cast : (Fin n → Fin (d + 1)) → (Fin n → ℕ) := fun i k => (i k : ℕ)
  have hcast : Function.Injective cast := by
    intro i i' h
    funext k
    exact Fin.ext (congrFun h k)
  refine hd (fun k j => (((j : ℕ) : ℝ) ^ 2, Pi.single k.castSucc ((j : ℕ) : ℝ)))
    (fun s => (q (cast '' s) ^ 2, Pi.single (Fin.last n) (q (cast '' s)))) fun i s => ?_
  rw [sum_eq (fun k => ((i k : ℕ) : ℝ)) (q (cast '' s))]
  constructor
  · intro hmem
    by_contra hi
    refine not_mem G' _ ?_ hmem
    rintro ⟨a, T, ha, he⟩
    obtain ⟨h1, h2⟩ := V_inj he
    have hT : T = cast '' s := hq h2.symm
    have ha' : a = cast i := by
      funext k
      have := congrFun h1 k
      exact_mod_cast this.symm
    rw [hT, ha'] at ha
    exact hi (hcast.mem_set_image.1 ha)
  · intro hi
    exact subset_convexHull ℝ _ ⟨_, ⟨cast i, cast '' s, Set.mem_image_of_mem _ hi, rfl⟩, rfl⟩

end VCN

/-- There exists a set of infinite $\mathrm{VC}_n$ dimension in $\mathbb R^{n + 2}$. -/
lemma exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost (n : ℕ) :
    ∃ C : Set (Fin (n + 2) → ℝ), Convex ℝ C ∧ ∀ d, ¬ HasAddVCNDimAtMost C n d := by
  obtain ⟨C, hC, hd⟩ := VCN.main n
  let L := Fin.consLinearEquiv (R := ℝ) (fun _ : Fin (n + 2) => ℝ)
  refine ⟨L '' C, hC.linear_image L.toLinearMap, fun d h => ?_⟩
  refine hd d fun x y hxy => h (fun k j => L (x k j)) (fun s => L (y s)) fun i s => ?_
  rw [← map_sum, ← map_add, L.injective.mem_set_image]
  exact hxy i s

end VCDimConvex

#print axioms VCDimConvex.exists_convex_rn_add_two_vc_n_forall_not_hasAddVCNDimAtMost
