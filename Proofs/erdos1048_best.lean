import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Erdos1043

/-- The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert\leq 1\}$ (restated from Erdos1043). -/
def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

end Erdos1043

namespace Erdos1048

open Polynomial Erdos1043

lemma levelSet_X_pow (n : ℕ) (hn : 1 ≤ n) :
    levelSet ((X : ℂ[X]) ^ n) = Metric.closedBall 0 1 := by
  ext z
  show ‖((X : ℂ[X]) ^ n).eval z‖ ≤ 1 ↔ z ∈ Metric.closedBall 0 1
  rw [eval_pow, eval_X, norm_pow, Metric.mem_closedBall, dist_zero_right]
  exact pow_le_one_iff_of_nonneg (norm_nonneg z) (by omega)

theorem erdos_1048.variants.diam_ge_two_is_best (n : ℕ) (hn : 1 ≤ n) :
    Metric.ediam (connectedComponentIn (levelSet ((X : ℂ[X]) ^ n)) 0) = 2 := by
  rw [levelSet_X_pow n hn, (convex_closedBall (0:ℂ) 1).isPreconnected.connectedComponentIn
    (Metric.mem_closedBall_self zero_le_one),
    ← ENNReal.ofReal_toReal Metric.isBounded_closedBall.ediam_ne_top]
  change ENNReal.ofReal (Metric.diam (Metric.closedBall (0:ℂ) 1)) = 2
  rw [Metric.diam_closedBall_eq _ zero_le_one, mul_one]
  exact ENNReal.ofReal_ofNat 2

end Erdos1048

#print axioms Erdos1048.erdos_1048.variants.diam_ge_two_is_best
