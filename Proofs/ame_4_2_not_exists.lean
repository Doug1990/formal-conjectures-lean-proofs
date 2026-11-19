-- Hand copy of the verified file work/ame42.lean (2026-11-05). Not compiled separately;
-- the work file is the verified source.
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.BigOperators

open scoped BigOperators

namespace OpenQuantumProblem35

abbrev Config (n d : ℕ) := Fin n → Fin d

abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)

abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ

instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp

def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1

def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)

def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)

def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩

noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))

noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)

def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d

def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)

def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ

namespace AME42

abbrev C4 := Config 4 2
abbrev C2 := Config 2 2

/-! ### Part 1: the singlet (shadow) identity -/

def mix (S : Fin 4 → Bool) (x y : C4) : C4 := fun i => if S i then y i else x i

noncomputable def P (f : C4 → ℂ) (S : Fin 4 → Bool) : ℂ :=
  ∑ x : C4, ∑ y : C4, f x * f y * star (f (mix S x y)) * star (f (mix S y x))

def sgnS (S : Fin 4 → Bool) : ℤ := ∏ i, (if S i then -1 else 1)

def fb (a b a' b' : Fin 2) (s : Bool) : ℤ :=
  (if s then -1 else 1) *
    ((if a' = (if s then b else a) then 1 else 0) * (if b' = (if s then a else b) then 1 else 0))

def sg (a : Fin 2) : ℤ := if a = 0 then 1 else -1

lemma fb_sum : ∀ a b a' b' : Fin 2, (∑ s : Bool, fb a b a' b' s) =
    sg a * sg a' * ((if b = a + 1 then 1 else 0) * (if b' = a' + 1 then 1 else 0)) := by
  decide +kernel

def fl (x : C4) : C4 := fun i => x i + 1

def sig (x : C4) : ℤ := ∏ i, sg (x i)

noncomputable def T (f : C4 → ℂ) : ℂ := ∑ x, (sig x : ℂ) * (f x * f (fl x))

noncomputable def M (f : C4 → ℂ) : ℂ :=
  ∑ x : C4, ∑ y : C4, ∑ x' : C4, ∑ y' : C4,
    f x * f y * star (f x') * star (f y') *
      (((∏ i, ∑ s : Bool, fb (x i) (y i) (x' i) (y' i) s : ℤ)) : ℂ)

lemma prod_fb (S : Fin 4 → Bool) (x y x' y' : C4) :
    (∏ i, fb (x i) (y i) (x' i) (y' i) (S i)) =
      sgnS S * ((if x' = mix S x y then 1 else 0) * (if y' = mix S y x then 1 else 0)) := by
  have e1 : (∀ i ∈ (Finset.univ : Finset (Fin 4)), x' i = if S i then y i else x i) ↔
      x' = mix S x y :=
    ⟨fun h => funext fun i => h i (Finset.mem_univ _), fun h i _ => by subst h; rfl⟩
  have e2 : (∀ i ∈ (Finset.univ : Finset (Fin 4)), y' i = if S i then x i else y i) ↔
      y' = mix S y x :=
    ⟨fun h => funext fun i => h i (Finset.mem_univ _), fun h i _ => by subst h; rfl⟩
  unfold fb sgnS
  simp only [Finset.prod_mul_distrib, Finset.prod_boole, e1, e2]

lemma prod_fb2 (x y x' y' : C4) :
    (∏ i, ∑ s : Bool, fb (x i) (y i) (x' i) (y' i) s) =
      sig x * sig x' * ((if y = fl x then 1 else 0) * (if y' = fl x' then 1 else 0)) := by
  have e1 : (∀ i ∈ (Finset.univ : Finset (Fin 4)), y i = x i + 1) ↔ y = fl x :=
    ⟨fun h => funext fun i => h i (Finset.mem_univ _), fun h i _ => by subst h; rfl⟩
  have e2 : (∀ i ∈ (Finset.univ : Finset (Fin 4)), y' i = x' i + 1) ↔ y' = fl x' :=
    ⟨fun h => funext fun i => h i (Finset.mem_univ _), fun h i _ => by subst h; rfl⟩
  unfold sig
  simp only [fb_sum, Finset.prod_mul_distrib, Finset.prod_boole, e1, e2]

lemma comm3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (h : α → β → γ → ℂ) :
    (∑ a, ∑ b, ∑ c, h a b c) = ∑ c, ∑ a, ∑ b, h a b c := by
  have : ∀ a, (∑ b, ∑ c, h a b c) = ∑ c, ∑ b, h a b c := fun a => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_comm]

lemma collapse (g : C4 → C4 → ℂ) (A B : C4) :
    (∑ x' : C4, ∑ y' : C4, g x' y' * ((if x' = A then 1 else 0) * (if y' = B then 1 else 0)))
      = g A B := by
  rw [Finset.sum_eq_single A (fun b _ hb => by simp [hb]) (by simp)]
  rw [Finset.sum_eq_single B (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma collapse2 (g : C4 → C4 → C4 → ℂ) (A : C4) (B : C4 → C4) :
    (∑ y : C4, ∑ x' : C4, ∑ y' : C4,
      g y x' y' * ((if y = A then 1 else 0) * (if y' = B x' then 1 else 0)))
      = ∑ x', g A x' (B x') := by
  rw [Finset.sum_eq_single A (fun b _ hb => by simp [hb]) (by simp)]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [Finset.sum_eq_single (B x') (fun b _ hb => by simp [hb]) (by simp)]
  simp

lemma M_eq_a (f : C4 → ℂ) : M f = ∑ S, (sgnS S : ℂ) * P f S := by
  unfold M P
  have inner : ∀ x y : C4,
      (∑ x' : C4, ∑ y' : C4, f x * f y * star (f x') * star (f y') *
        (((∏ i, ∑ s : Bool, fb (x i) (y i) (x' i) (y' i) s : ℤ)) : ℂ)) =
      ∑ S : Fin 4 → Bool, (sgnS S : ℂ) *
        (f x * f y * star (f (mix S x y)) * star (f (mix S y x))) := by
    intro x y
    have h1 : ∀ x' y' : C4,
        (((∏ i, ∑ s : Bool, fb (x i) (y i) (x' i) (y' i) s : ℤ)) : ℂ) =
          ∑ S : Fin 4 → Bool, (sgnS S : ℂ) *
            ((if x' = mix S x y then 1 else 0) * (if y' = mix S y x then 1 else 0)) := by
      intro x' y'
      rw [Fintype.prod_sum]
      simp only [prod_fb, Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero]
    simp only [h1, Finset.mul_sum]
    rw [comm3]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    refine Eq.trans ?_ (collapse (fun x' y' => (sgnS S : ℂ) *
      (f x * f y * star (f x') * star (f y'))) (mix S x y) (mix S y x))
    refine Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun y' _ => ?_))
    ring
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => inner x y))]
  rw [comm3]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]

lemma Tsq (f : C4 → ℂ) : T f * star (T f) =
    ∑ x : C4, ∑ x' : C4, (sig x : ℂ) * (sig x' : ℂ) *
      (f x * f (fl x) * star (f x') * star (f (fl x'))) := by
  unfold T
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
  simp only [star_mul', star_intCast]
  ring

lemma M_eq_b (f : C4 → ℂ) : M f = T f * star (T f) := by
  rw [Tsq f]
  unfold M
  have h1 : ∀ x y x' y' : C4,
      (((∏ i, ∑ s : Bool, fb (x i) (y i) (x' i) (y' i) s : ℤ)) : ℂ) =
        (sig x : ℂ) * (sig x' : ℂ) *
          ((if y = fl x then 1 else 0) * (if y' = fl x' then 1 else 0)) := by
    intro x y x' y'
    rw [prod_fb2]
    simp only [Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero]
  simp only [h1]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Eq.trans ?_ (collapse2 (fun y x' y' => (sig x : ℂ) * (sig x' : ℂ) *
    (f x * f y * star (f x') * star (f y'))) (fl x) fl)
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl
    (fun x' _ => Finset.sum_congr rfl (fun y' _ => ?_)))
  ring

def cpl (S : Fin 4 → Bool) : Fin 4 → Bool := fun i => !S i

lemma mix_cpl (S : Fin 4 → Bool) (x y : C4) : mix (cpl S) x y = mix S y x := by
  funext i
  unfold mix cpl
  cases S i <;> rfl

lemma P_cpl (f : C4 → ℂ) (S : Fin 4 → Bool) : P f (cpl S) = P f S := by
  unfold P
  simp only [mix_cpl]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

/-! ### Part 2: values of P from the AME property -/

def L (k : Fin 2) : Fin 4 := ⟨k.1, by omega⟩
def R (k : Fin 2) : Fin 4 := ⟨2 + k.1, by omega⟩

lemma split (j : Fin 4) : (∃ m : Fin 2, j = L m) ∨ (∃ k : Fin 2, j = R k) := by
  fin_cases j
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩

lemma comb_left (x : C2) (z : C2) (k : Fin 2) :
    combineFirst (n := 4) (d := 2) 2 (by decide) x z (L k) = x k := by
  simp [combineFirst, L, k.2]

lemma comb_right (x : C2) (z : C2) (k : Fin 2) :
    combineFirst (n := 4) (d := 2) 2 (by decide) x z (R k) = z k := by
  have : ¬ (2 + k.1 < 2) := by omega
  simp [combineFirst, R, this]

lemma cover (π : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (∃ m, i = π.symm (L m)) ∨ ∃ k, i = π.symm (R k) := by
  rcases split (π i) with ⟨m, hm⟩ | ⟨k, hk⟩
  · exact Or.inl ⟨m, by rw [← hm]; simp⟩
  · exact Or.inr ⟨k, by rw [← hk]; simp⟩

def W (π : Equiv.Perm (Fin 4)) (a : C2) (z : C2) : C4 :=
  permuteConfig π (combineFirst (n := 4) (d := 2) 2 (by decide) a z)

lemma W_apply (π : Equiv.Perm (Fin 4)) (a : C2) (z : C2) (i : Fin 4) :
    W π a z (π.symm i) = combineFirst (n := 4) (d := 2) 2 (by decide) a z i := by
  simp only [W, permuteConfig, Equiv.apply_symm_apply]

lemma W_L (π : Equiv.Perm (Fin 4)) (a : C2) (z : C2) (k : Fin 2) :
    W π a z (π.symm (L k)) = a k := by
  rw [W_apply]; exact comb_left a z k

lemma W_R (π : Equiv.Perm (Fin 4)) (a : C2) (z : C2) (k : Fin 2) :
    W π a z (π.symm (R k)) = z k := by
  rw [W_apply]; exact comb_right a z k

def E (π : Equiv.Perm (Fin 4)) : C2 × C2 ≃ C4 where
  toFun p := W π p.1 p.2
  invFun x := (fun k => x (π.symm (L k)), fun k => x (π.symm (R k)))
  left_inv p := by
    ext k
    · simp [W_L]
    · simp [W_R]
  right_inv x := by
    funext i
    rcases cover π i with ⟨m, rfl⟩ | ⟨k, rfl⟩
    · simp [W_L]
    · simp [W_R]

lemma reidx (π : Equiv.Perm (Fin 4)) (g : C4 → ℂ) :
    (∑ x : C4, g x) = ∑ a : C2, ∑ z : C2, g (W π a z) := by
  rw [← (E π).sum_comp g, Fintype.sum_prod_type]
  rfl

def pat (π : Equiv.Perm (Fin 4)) (U : Fin 2 → Bool) : Fin 4 → Bool :=
  fun i => if h : (π i).1 < 2 then U ⟨(π i).1, h⟩ else false

def mixU (U : Fin 2 → Bool) (a b : C2) : C2 := fun k => if U k then b k else a k

lemma pat_L (π : Equiv.Perm (Fin 4)) (U : Fin 2 → Bool) (m : Fin 2) :
    pat π U (π.symm (L m)) = U m := by
  have h := congrArg Fin.val (Equiv.apply_symm_apply π (L m))
  unfold pat
  rw [dif_pos (lt_of_eq_of_lt h m.2)]
  congr 1
  exact Fin.ext h

lemma pat_R (π : Equiv.Perm (Fin 4)) (U : Fin 2 → Bool) (k : Fin 2) :
    pat π U (π.symm (R k)) = false := by
  have h := congrArg Fin.val (Equiv.apply_symm_apply π (R k))
  change _ = 2 + k.1 at h
  unfold pat
  rw [dif_neg (by omega)]

lemma mix_W (π : Equiv.Perm (Fin 4)) (U : Fin 2 → Bool) (a b z w : C2) :
    mix (pat π U) (W π a z) (W π b w) = W π (mixU U a b) z := by
  funext i
  rcases cover π i with ⟨m, rfl⟩ | ⟨k, rfl⟩
  · simp only [mix, pat_L, W_L, mixU]
  · simp only [mix, pat_R, W_R, Bool.false_eq_true, ↓reduceIte]

lemma P_pat (f : C4 → ℂ) (π : Equiv.Perm (Fin 4)) (U : Fin 2 → Bool) :
    P f (pat π U) = ∑ a : C2, ∑ b : C2,
      (∑ z : C2, f (W π a z) * star (f (W π (mixU U a b) z))) *
        (∑ w : C2, f (W π b w) * star (f (W π (mixU U b a) w))) := by
  unfold P
  simp only [reidx π, mix_W]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun w _ => by ring))

lemma rho (ψ : StateVector 4 2) (hψ : IsAME ψ) (π : Equiv.Perm (Fin 4)) (a c : C2) :
    (∑ z : C2, ψ (W π a z) * star (ψ (W π c z))) = if a = c then (1 / 4 : ℂ) else 0 := by
  have H : reducedDensityFirst (n := 4) (d := 2) 2 (by decide) (permuteState π ψ) =
      maximallyMixed 2 2 := hψ.2 π
  calc (∑ z : C2, ψ (W π a z) * star (ψ (W π c z)))
      = reducedDensityFirst (n := 4) (d := 2) 2 (by decide) (permuteState π ψ) a c := rfl
    _ = maximallyMixed 2 2 a c := by rw [H]
    _ = if a = c then (1 / 4 : ℂ) else 0 := by
      simp only [maximallyMixed, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      have hc : (Fintype.card (Config 2 2) : ℂ) = 4 := by
        norm_num [Fintype.card_fun]
      rw [hc]
      split_ifs <;> norm_num

def cnt (U : Fin 2 → Bool) : ℤ :=
  ∑ a : C2, ∑ b : C2, (if a = mixU U a b then 1 else 0) * (if b = mixU U b a then 1 else 0)

lemma P_val (ψ : StateVector 4 2) (hψ : IsAME ψ) (π : Equiv.Perm (Fin 4))
    (U : Fin 2 → Bool) : P (fun x => ψ x) (pat π U) = (cnt U : ℂ) / 16 := by
  rw [P_pat]
  simp only [rho ψ hψ π]
  unfold cnt
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  split_ifs <;> norm_num

/-! ### Part 3: the finite bookkeeping -/

def pl : Fin 6 → Equiv.Perm (Fin 4) :=
  ![1, Equiv.swap 0 2, Equiv.swap 0 3, Equiv.swap 1 2, Equiv.swap 1 3,
    Equiv.swap 0 2 * Equiv.swap 1 3]

def v (S : Fin 4 → Bool) : ℤ :=
  let k := (Finset.univ.filter (fun i => S i = true)).card
  if k = 0 ∨ k = 4 then 4 else if k = 1 ∨ k = 3 then 2 else 1

lemma cover_S : ∀ S : Fin 4 → Bool, ∃ k : Fin 6, ∃ U : Fin 2 → Bool,
    (S = pat (pl k) U ∨ S = cpl (pat (pl k) U)) ∧ 4 * v S = cnt U := by
  decide +kernel

lemma sum_sv : (∑ S : Fin 4 → Bool, sgnS S * v S) = -2 := by
  decide +kernel

end AME42

theorem ame_4_2_not_exists : ¬ ExistsAME 4 2 := by
  rintro ⟨ψ, hψ⟩
  have hP : ∀ S, AME42.P (fun x => ψ x) S = (AME42.v S : ℂ) / 4 := by
    intro S
    obtain ⟨k, U, hS, hv⟩ := AME42.cover_S S
    have hc : (AME42.cnt U : ℂ) = 4 * (AME42.v S : ℂ) := by exact_mod_cast hv.symm
    have hval : AME42.P (fun x => ψ x) (AME42.pat (AME42.pl k) U) = (AME42.v S : ℂ) / 4 := by
      rw [AME42.P_val ψ hψ _ U, hc]; ring
    rcases hS with h | h
    · calc AME42.P (fun x => ψ x) S = AME42.P (fun x => ψ x) (AME42.pat (AME42.pl k) U) := by
            rw [h]
        _ = _ := hval
    · calc AME42.P (fun x => ψ x) S
            = AME42.P (fun x => ψ x) (AME42.cpl (AME42.pat (AME42.pl k) U)) := by rw [h]
        _ = AME42.P (fun x => ψ x) (AME42.pat (AME42.pl k) U) := AME42.P_cpl _ _
        _ = _ := hval
  have hsum : (∑ S, (AME42.sgnS S : ℂ) * AME42.P (fun x => ψ x) S) = -1 / 2 := by
    simp only [hP]
    have h2 : (((∑ S : Fin 4 → Bool, AME42.sgnS S * AME42.v S : ℤ)) : ℂ) = -2 := by
      rw [AME42.sum_sv]; norm_num
    push_cast at h2
    rw [show (∑ S : Fin 4 → Bool, (AME42.sgnS S : ℂ) * ((AME42.v S : ℂ) / 4)) =
        (∑ S : Fin 4 → Bool, (AME42.sgnS S : ℂ) * (AME42.v S : ℂ)) / 4 by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun S _ => by ring), h2]
    norm_num
  have key : AME42.T (fun x => ψ x) * star (AME42.T (fun x => ψ x)) = -1 / 2 := by
    rw [← AME42.M_eq_b, AME42.M_eq_a, hsum]
  have hn : AME42.T (fun x => ψ x) * star (AME42.T (fun x => ψ x)) =
      ((Complex.normSq (AME42.T (fun x => ψ x)) : ℝ) : ℂ) := Complex.mul_conj _
  rw [hn] at key
  have h3 : Complex.normSq (AME42.T (fun x => ψ x)) = -1 / 2 := by exact_mod_cast key
  linarith [Complex.normSq_nonneg (AME42.T (fun x => ψ x))]

end OpenQuantumProblem35

#print axioms OpenQuantumProblem35.ame_4_2_not_exists
