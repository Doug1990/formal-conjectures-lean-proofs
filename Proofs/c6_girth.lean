import Mathlib

open SimpleGraph

namespace WrittenOnTheWallII.Test

/-- C6: The cycle graph on 6 vertices (as in the checkout). -/
abbrev C6 : SimpleGraph (Fin 6) := cycleGraph 6

lemma adj_arith : ∀ u v : Fin 6, (cycleGraph 6).Adj u v →
    (u.val + 1) % 6 = v.val ∨ (v.val + 1) % 6 = u.val := by
  decide

lemma no_short_cycle {n : ℕ} (h3 : 3 ≤ n) (h5 : n ≤ 5)
    (f : Copy (cycleGraph n) (cycleGraph 6)) : False := by
  interval_cases n
  · have h01 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 3).Adj 0 1 by decide))
    have h12 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 3).Adj 1 2 by decide))
    have h20 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 3).Adj 2 0 by decide))
    omega
  · have h01 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide))
    have h12 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 4).Adj 1 2 by decide))
    have h23 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide))
    have h30 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 4).Adj 3 0 by decide))
    have hac : (f.toHom 0).val ≠ (f.toHom 2).val := fun h =>
      absurd (f.injective (Fin.ext h)) (by decide)
    have hbd : (f.toHom 1).val ≠ (f.toHom 3).val := fun h =>
      absurd (f.injective (Fin.ext h)) (by decide)
    omega
  · have h01 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 5).Adj 0 1 by decide))
    have h12 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 5).Adj 1 2 by decide))
    have h23 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 5).Adj 2 3 by decide))
    have h34 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 5).Adj 3 4 by decide))
    have h40 := adj_arith _ _ (f.toHom.map_adj (show (cycleGraph 5).Adj 4 0 by decide))
    omega

theorem C6_girth : C6.girth = 6 := by
  have hup : C6.egirth ≤ 6 := by
    have := egirth_le_length (cycleGraph.isCycle_cycle (n := 3))
    simpa using this
  have hlow : 6 ≤ C6.egirth := by
    rw [le_egirth]
    intro a w hw
    by_contra hlt
    push_neg at hlt
    have hlt' : w.length < 6 := by exact_mod_cast hlt
    have h3 := hw.three_le_length
    obtain ⟨f⟩ := (cycleGraph_isContained_iff (G := C6) (n := w.length) (by omega)).mpr
      ⟨a, w, hw, rfl⟩
    exact no_short_cycle h3 (by omega) f
  have : C6.egirth = 6 := le_antisymm hup hlow
  simp [girth, this]

end WrittenOnTheWallII.Test

#print axioms WrittenOnTheWallII.Test.C6_girth
