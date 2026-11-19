import Mathlib.Data.Holor
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.DenseEmbedding

namespace Arxiv.«0805.3777»

/-- The space of complex tensors of a fixed format, topologised as the finite-dimensional complex
vector space that it is. -/
noncomputable scoped instance instTopologicalSpaceHolor {ds : List ℕ} :
    TopologicalSpace (Holor ℂ ds) :=
  inferInstanceAs <| TopologicalSpace (HolorIndex ds → ℂ)

def IsGenericRank (ds : List ℕ) (r : ℕ) : Prop :=
  ∃ U : Set (Holor ℂ ds), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank = r

def IsMaxRank (ds : List ℕ) (r : ℕ) : Prop :=
  IsGreatest (Set.range fun T : Holor ℂ ds => T.cprank) r

lemma cprank_spec {ds : List ℕ} (x : Holor ℂ ds) : Holor.CPRankMax x.cprank x := by
  let := Classical.decPred fun n : ℕ => Holor.CPRankMax n x
  exact Nat.find_spec (p := fun n => Holor.CPRankMax n x) ⟨ds.prod, Holor.cprankMax_upper_bound x⟩

lemma cprank_le_of {ds : List ℕ} (x : Holor ℂ ds) (n : ℕ) (h : Holor.CPRankMax n x) :
    x.cprank ≤ n := by
  unfold Holor.cprank
  exact @Nat.find_min' _ (Classical.decPred _) _ _ h

lemma cprank_add_le {ds : List ℕ} (x y : Holor ℂ ds) : (x + y).cprank ≤ x.cprank + y.cprank :=
  cprank_le_of _ _ (Holor.cprankMax_add (cprank_spec x) (cprank_spec y))

theorem isMaxRank_le_two_mul_isGenericRank {ds : List ℕ} {r R : ℕ} (hr : IsGenericRank ds r)
    (hR : IsMaxRank ds R) : R ≤ 2 * r := by
  obtain ⟨U, hU, hUd, hUr⟩ := hr
  obtain ⟨T, rfl⟩ := hR.1
  have : IsTopologicalAddGroup (Holor ℂ ds) :=
    inferInstanceAs (IsTopologicalAddGroup (HolorIndex ds → ℂ))
  let f : Holor ℂ ds → Holor ℂ ds := fun A => T - A
  have hfc : Continuous f := continuous_const.sub continuous_id
  have hfs : Function.Surjective f := fun B => ⟨T - B, by simp [f]⟩
  have hV : Dense (f '' U) := hfs.denseRange.dense_image hfc hUd
  obtain ⟨A, hAU, B, hBU, hBA⟩ := hV.inter_open_nonempty U hU hUd.nonempty
  have hT : T = B + A := by rw [← hBA]; simp [f]
  calc T.cprank = (B + A).cprank := by rw [← hT]
    _ ≤ B.cprank + A.cprank := cprank_add_le B A
    _ = 2 * r := by rw [hUr A hAU, hUr B hBU]; omega

end Arxiv.«0805.3777»

#print axioms Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank
