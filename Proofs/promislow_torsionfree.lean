import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.Pi
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Data.Fin.VecNotation

def Monoid.IsTorsionFree (G : Type*) [Monoid G] : Prop :=
  ∀ g : G, g ≠ 1 → ¬IsOfFinOrder g

namespace Kaplansky

abbrev PromislowGroup : Type :=
  letI a := FreeGroup.of (0 : Fin 2)
  letI b := FreeGroup.of (1 : Fin 2)
  PresentedGroup {b⁻¹ * a * a * b * a * a, a⁻¹ * b * b * a * b * b}

namespace Prom

def rels : Set (FreeGroup (Fin 2)) :=
  {(FreeGroup.of 1)⁻¹ * FreeGroup.of 0 * FreeGroup.of 0 * FreeGroup.of 1 * FreeGroup.of 0 *
      FreeGroup.of 0,
    (FreeGroup.of 0)⁻¹ * FreeGroup.of 1 * FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1 *
      FreeGroup.of 1}

abbrev G := PresentedGroup rels

def a : G := PresentedGroup.of 0
def b : G := PresentedGroup.of 1

local notation "X" => a * a
local notation "Y" => b * b
local notation "Z" => a * b * a * b

/-! ### Relations in the group -/

theorem R1 : b⁻¹ * a * a * b * a * a = 1 := by
  have h := PresentedGroup.one_of_mem (rels := rels) (Set.mem_insert _ _)
  simp only [map_mul, map_inv] at h
  exact h

theorem R2 : a⁻¹ * b * b * a * b * b = 1 := by
  have h := PresentedGroup.one_of_mem (rels := rels) (Set.mem_insert_of_mem _ rfl)
  simp only [map_mul, map_inv] at h
  exact h

theorem C1 : b⁻¹ * X * b = X⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← R1]; group

theorem C2 : a⁻¹ * Y * a = Y⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← R2]; group

theorem C1inv : b⁻¹ * X⁻¹ * b = X := by
  calc b⁻¹ * X⁻¹ * b = (b⁻¹ * X * b)⁻¹ := by group
    _ = X := by rw [C1, inv_inv]

theorem C2inv : a⁻¹ * Y⁻¹ * a = Y := by
  calc a⁻¹ * Y⁻¹ * a = (a⁻¹ * Y * a)⁻¹ := by group
    _ = Y := by rw [C2, inv_inv]

theorem Cy : b⁻¹ * (b⁻¹ * X * b) * b = X := by
  rw [C1, C1inv]

theorem Cx : a⁻¹ * (a⁻¹ * Y * a) * a = Y := by
  rw [C2, C2inv]

theorem C1' : b * X * b⁻¹ = X⁻¹ := by
  calc b * X * b⁻¹ = b * (b⁻¹ * (b⁻¹ * X * b) * b) * b⁻¹ := by rw [Cy]
    _ = b⁻¹ * X * b := by group
    _ = X⁻¹ := C1

theorem C2' : a * Y * a⁻¹ = Y⁻¹ := by
  calc a * Y * a⁻¹ = a * (a⁻¹ * (a⁻¹ * Y * a) * a) * a⁻¹ := by rw [Cx]
    _ = a⁻¹ * Y * a := by group
    _ = Y⁻¹ := C2

theorem C2'inv : a * Y⁻¹ * a⁻¹ = Y := by
  calc a * Y⁻¹ * a⁻¹ = (a * Y * a⁻¹)⁻¹ := by group
    _ = Y := by rw [C2', inv_inv]

theorem K : Z * (b * a * b * a) = 1 := by
  calc Z * (b * a * b * a) = a * b * a * a * (a⁻¹ * Y * a) * b * a := by group
    _ = a * b * a * a * Y⁻¹ * b * a := by rw [C2]
    _ = a * (b * X * b⁻¹) * a := by group
    _ = a * X⁻¹ * a := by rw [C1']
    _ = 1 := by group

theorem K' : b * a * b * a = Z⁻¹ := eq_inv_of_mul_eq_one_right K

theorem Za' : a * Z * a⁻¹ = Z⁻¹ := by
  calc a * Z * a⁻¹ = b * (b⁻¹ * X * b) * a * b * a⁻¹ := by group
    _ = b * X⁻¹ * a * b * a⁻¹ := by rw [C1]
    _ = b * a * b * a * (a⁻¹ * (b⁻¹ * X⁻¹ * b) * a⁻¹) := by group
    _ = b * a * b * a * (a⁻¹ * X * a⁻¹) := by rw [C1inv]
    _ = b * a * b * a := by group
    _ = Z⁻¹ := K'

theorem Zb' : b * Z * b⁻¹ = Z⁻¹ := by
  calc b * Z * b⁻¹ = b * a * b * a := by group
    _ = Z⁻¹ := K'

theorem hXY : Commute X Y := by
  have h : Y⁻¹ * X * Y = X := by
    calc Y⁻¹ * X * Y = b⁻¹ * (b⁻¹ * X * b) * b := by group
      _ = X := Cy
  have h2 : X * Y = Y * X := by
    calc X * Y = Y * (Y⁻¹ * X * Y) := by group
      _ = Y * X := by rw [h]
  exact h2

theorem hXZ : Commute X Z := by
  have h : X * Z * X⁻¹ = Z := by
    calc X * Z * X⁻¹ = a * (a * Z * a⁻¹) * a⁻¹ := by group
      _ = a * Z⁻¹ * a⁻¹ := by rw [Za']
      _ = (a * Z * a⁻¹)⁻¹ := by group
      _ = Z := by rw [Za']; group
  exact mul_inv_eq_iff_eq_mul.1 h

theorem hYZ : Commute Y Z := by
  have h : Y * Z * Y⁻¹ = Z := by
    calc Y * Z * Y⁻¹ = b * (b * Z * b⁻¹) * b⁻¹ := by group
      _ = b * Z⁻¹ * b⁻¹ := by rw [Zb']
      _ = (b * Z * b⁻¹)⁻¹ := by group
      _ = Z := by rw [Zb']; group
  exact mul_inv_eq_iff_eq_mul.1 h

theorem ba : b * a = Z⁻¹ * X⁻¹ * Y * (a * b) := by
  calc b * a = (b * a * b * a) * X⁻¹ * (a * Y⁻¹ * a⁻¹) * (a * b) := by group
    _ = Z⁻¹ * X⁻¹ * Y * (a * b) := by rw [K', C2'inv]

theorem bab : b * (a * b) = Z⁻¹ * X⁻¹ * a := by
  calc b * (a * b) = (b * a * b * a) * X⁻¹ * a := by group
    _ = Z⁻¹ * X⁻¹ * a := by rw [K']

/-! ### The translation subgroup -/

def T (t : G) : Prop := ∃ i j k : ℤ, t = X ^ i * Y ^ j * Z ^ k

theorem emul {H : Type*} [Group H] {p q r : H} (hpq : Commute p q) (hpr : Commute p r)
    (hqr : Commute q r) (i j k i' j' k' : ℤ) :
    p ^ i * q ^ j * r ^ k * (p ^ i' * q ^ j' * r ^ k') =
      p ^ (i + i') * q ^ (j + j') * r ^ (k + k') := by
  simp only [mul_assoc]
  rw [((hpr.zpow_zpow i' k).symm).left_comm, ((hpq.zpow_zpow i' j).symm).left_comm,
    ← mul_assoc (p ^ i), ← zpow_add, ((hqr.zpow_zpow j' k).symm).left_comm,
    ← mul_assoc (q ^ j), ← zpow_add, ← zpow_add]

theorem T_mul {s t : G} (hs : T s) (ht : T t) : T (s * t) := by
  obtain ⟨i, j, k, rfl⟩ := hs
  obtain ⟨i', j', k', rfl⟩ := ht
  exact ⟨i + i', j + j', k + k', emul hXY hXZ hYZ i j k i' j' k'⟩

theorem T_X : T X := ⟨1, 0, 0, by simp⟩
theorem T_Xi : T X⁻¹ := ⟨-1, 0, 0, by simp⟩
theorem T_Y : T Y := ⟨0, 1, 0, by simp⟩
theorem T_Yi : T Y⁻¹ := ⟨0, -1, 0, by simp⟩
theorem T_Z : T Z := ⟨0, 0, 1, by simp⟩
theorem T_Zi : T Z⁻¹ := ⟨0, 0, -1, by simp⟩
theorem T_one : T 1 := ⟨0, 0, 0, by simp⟩

theorem T_conj_a {t : G} (ht : T t) : T (a * t * a⁻¹) := by
  obtain ⟨i, j, k, rfl⟩ := ht
  refine ⟨i, -j, -k, ?_⟩
  rw [← MulAut.conj_apply, map_mul, map_mul, map_zpow, map_zpow, map_zpow, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, C2', Za', inv_zpow', inv_zpow']
  congr 3
  group

theorem T_conj_b {t : G} (ht : T t) : T (b * t * b⁻¹) := by
  obtain ⟨i, j, k, rfl⟩ := ht
  refine ⟨-i, j, -k, ?_⟩
  rw [← MulAut.conj_apply, map_mul, map_mul, map_zpow, map_zpow, map_zpow, MulAut.conj_apply,
    MulAut.conj_apply, MulAut.conj_apply, C1', Zb', inv_zpow', inv_zpow']
  congr 3
  group

/-! ### Normal form -/

def S (s : G) : Prop := s = 1 ∨ s = a ∨ s = b ∨ s = a * b

def NF (g : G) : Prop := ∃ t s, T t ∧ S s ∧ g = t * s

theorem NF_T {t g : G} (ht : T t) (hg : NF g) : NF (t * g) := by
  obtain ⟨t', s, ht', hs, rfl⟩ := hg
  exact ⟨t * t', s, T_mul ht ht', hs, by group⟩

theorem NF_a {g : G} (hg : NF g) : NF (a * g) := by
  obtain ⟨t, s, ht, hs, rfl⟩ := hg
  have e : a * (t * s) = (a * t * a⁻¹) * (a * s) := by group
  rw [e]
  apply NF_T (T_conj_a ht)
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨1, a, T_one, Or.inr (Or.inl rfl), by group⟩
  · exact ⟨X, 1, T_X, Or.inl rfl, by group⟩
  · exact ⟨1, a * b, T_one, Or.inr (Or.inr (Or.inr rfl)), by group⟩
  · exact ⟨X, b, T_X, Or.inr (Or.inr (Or.inl rfl)), by group⟩

theorem NF_b {g : G} (hg : NF g) : NF (b * g) := by
  obtain ⟨t, s, ht, hs, rfl⟩ := hg
  have e : b * (t * s) = (b * t * b⁻¹) * (b * s) := by group
  rw [e]
  apply NF_T (T_conj_b ht)
  rcases hs with rfl | rfl | rfl | rfl
  · exact ⟨1, b, T_one, Or.inr (Or.inr (Or.inl rfl)), by group⟩
  · exact ⟨Z⁻¹ * X⁻¹ * Y, a * b, T_mul (T_mul T_Zi T_Xi) T_Y, Or.inr (Or.inr (Or.inr rfl)), ba⟩
  · exact ⟨Y, 1, T_Y, Or.inl rfl, by group⟩
  · exact ⟨Z⁻¹ * X⁻¹, a, T_mul T_Zi T_Xi, Or.inr (Or.inl rfl), bab⟩

theorem NF_all (g : G) : NF g := by
  have hg : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin 2 → G)) := by
    rw [PresentedGroup.closure_range_of]; exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨1, 1, T_one, Or.inl rfl, by group⟩
  | mul_left x hx y _ ih =>
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · exact NF_a ih
    · exact NF_b ih
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨i, rfl⟩ := hx
    fin_cases i
    · have e : (PresentedGroup.of (0 : Fin 2) : G)⁻¹ * y = X⁻¹ * (a * y) := by
        simp only [a]; group
      have h := NF_T T_Xi (NF_a ih)
      rw [← e] at h; exact h
    · have e : (PresentedGroup.of (1 : Fin 2) : G)⁻¹ * y = Y⁻¹ * (b * y) := by
        simp only [b]; group
      have h := NF_T T_Yi (NF_b ih)
      rw [← e] at h; exact h

/-! ### The affine action on ℤ³ -/

abbrev V := Fin 3 → ℤ

def αf (v : V) : V := ![v 0 + 1, 1 - v 1, -v 2]
def αg (v : V) : V := ![v 0 - 1, 1 - v 1, -v 2]
def βf (v : V) : V := ![-v 0, v 1 + 1, 1 - v 2]
def βg (v : V) : V := ![-v 0, v 1 - 1, 1 - v 2]

def α : Equiv.Perm V :=
  ⟨αf, αg, fun v => by funext i; fin_cases i <;> simp [αf, αg],
    fun v => by funext i; fin_cases i <;> simp [αf, αg]⟩

def β : Equiv.Perm V :=
  ⟨βf, βg, fun v => by funext i; fin_cases i <;> simp [βf, βg],
    fun v => by funext i; fin_cases i <;> simp [βf, βg]⟩

theorem α_apply (v : V) : α v = αf v := rfl
theorem α_inv_apply (v : V) : α⁻¹ v = αg v := rfl
theorem β_apply (v : V) : β v = βf v := rfl
theorem β_inv_apply (v : V) : β⁻¹ v = βg v := rfl

theorem hrels : ∀ r ∈ rels, FreeGroup.lift ![α, β] r = 1 := by
  intro r hr
  rcases hr with rfl | rfl
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    ext v i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, α_apply, β_apply, β_inv_apply]
    fin_cases i <;> simp [αf, βf, βg]
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
    ext v i
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, α_apply, α_inv_apply, β_apply]
    fin_cases i <;> simp [αf, αg, βf]

noncomputable def ψ : G →* Equiv.Perm V := PresentedGroup.toGroup hrels

theorem ψa : ψ a = α := by simp [ψ, a]
theorem ψb : ψ b = β := by simp [ψ, b]

def IsTr (σ : Equiv.Perm V) (w : V) : Prop := ∀ v, σ v = v + w

theorem IsTr.mul {σ τ : Equiv.Perm V} {w w' : V} (h : IsTr σ w) (h' : IsTr τ w') :
    IsTr (σ * τ) (w + w') := by
  intro v; rw [Equiv.Perm.mul_apply, h', h]; abel

theorem IsTr.inv {σ : Equiv.Perm V} {w : V} (h : IsTr σ w) : IsTr σ⁻¹ (-w) := by
  intro v; rw [Equiv.Perm.inv_eq_iff_eq, h]; abel

theorem IsTr.zpow {σ : Equiv.Perm V} {w : V} (h : IsTr σ w) (n : ℤ) : IsTr (σ ^ n) (n • w) := by
  induction n using Int.induction_on with
  | zero => intro v; simp
  | succ n ih =>
    rw [zpow_add_one, add_smul, one_smul]; exact ih.mul h
  | pred n ih =>
    rw [zpow_sub_one, sub_smul, one_smul, sub_eq_add_neg]; exact ih.mul h.inv

def wX : V := ![2, 0, 0]
def wY : V := ![0, 2, 0]
def wZ : V := ![0, 0, -2]

theorem tr_X : IsTr (ψ X) wX := by
  intro v; rw [map_mul, ψa, Equiv.Perm.mul_apply, α_apply, α_apply]
  funext i; fin_cases i <;> simp [αf, wX] <;> ring

theorem tr_Y : IsTr (ψ Y) wY := by
  intro v; rw [map_mul, ψb, Equiv.Perm.mul_apply, β_apply, β_apply]
  funext i; fin_cases i <;> simp [βf, wY] <;> ring

theorem tr_Z : IsTr (ψ Z) wZ := by
  intro v; rw [map_mul, map_mul, map_mul, ψa, ψb, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, α_apply, α_apply, β_apply, β_apply]
  funext i; fin_cases i <;> simp [αf, βf, wZ] <;> ring

theorem tr_T (i j k : ℤ) :
    IsTr (ψ (X ^ i * Y ^ j * Z ^ k)) (i • wX + j • wY + k • wZ) := by
  rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow]
  exact ((tr_X.zpow i).mul (tr_Y.zpow j)).mul (tr_Z.zpow k)

theorem sq_a {σ : Equiv.Perm V} {c : V} (h : IsTr σ c) :
    IsTr ((σ * α) ^ 2) ![2 + 2 * c 0, 0, 0] := by
  intro v
  rw [sq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, h, α_apply,
    α_apply]
  funext i; fin_cases i <;> simp [αf] <;> ring

theorem sq_b {σ : Equiv.Perm V} {c : V} (h : IsTr σ c) :
    IsTr ((σ * β) ^ 2) ![0, 2 + 2 * c 1, 0] := by
  intro v
  rw [sq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, h, β_apply,
    β_apply]
  funext i; fin_cases i <;> simp [βf] <;> ring

theorem sq_ab {σ : Equiv.Perm V} {c : V} (h : IsTr σ c) :
    IsTr ((σ * (α * β)) ^ 2) ![0, 0, 2 * c 2 - 2] := by
  intro v
  rw [sq, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, h, h, α_apply, α_apply, β_apply, β_apply]
  funext i; fin_cases i <;> simp [αf, βf] <;> ring

/-- A translation of finite order is trivial. -/
theorem tr_zero {σ : Equiv.Perm V} {w : V} (h : IsTr σ w) (hσ : IsOfFinOrder σ) : w = 0 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hσ
  have h1 := h.zpow n 0
  rw [zpow_natCast, hpow, Equiv.Perm.one_apply, zero_add] at h1
  have h2 : (n : ℤ) • w = 0 := h1.symm
  rcases smul_eq_zero.1 h2 with h3 | h3
  · omega
  · exact h3

theorem main : Monoid.IsTorsionFree G := by
  intro g hg hfin
  obtain ⟨t, s, ⟨i, j, k, rfl⟩, hs, rfl⟩ := NF_all g
  have hψ : IsOfFinOrder (ψ (X ^ i * Y ^ j * Z ^ k * s)) := by
    obtain ⟨n, hn, hp⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, by rw [← map_pow, hp, map_one]⟩
  have hT := tr_T i j k
  have c0 : (i • wX + j • wY + k • wZ) 0 = 2 * i := by
    change i • (2 : ℤ) + j • (0 : ℤ) + k • (0 : ℤ) = 2 * i
    simp only [smul_eq_mul]; ring
  have c1 : (i • wX + j • wY + k • wZ) 1 = 2 * j := by
    change i • (0 : ℤ) + j • (2 : ℤ) + k • (0 : ℤ) = 2 * j
    simp only [smul_eq_mul]; ring
  have c2 : (i • wX + j • wY + k • wZ) 2 = -2 * k := by
    change i • (0 : ℤ) + j • (0 : ℤ) + k • (-2 : ℤ) = -2 * k
    simp only [smul_eq_mul]; ring
  rcases hs with rfl | rfl | rfl | rfl
  · rw [mul_one] at hψ hg
    have h0 := tr_zero hT hψ
    have hi : i = 0 := by
      have := congrFun h0 0; rw [c0, Pi.zero_apply] at this; omega
    have hj : j = 0 := by
      have := congrFun h0 1; rw [c1, Pi.zero_apply] at this; omega
    have hk : k = 0 := by
      have := congrFun h0 2; rw [c2, Pi.zero_apply] at this; omega
    subst hi hj hk
    simp at hg
  · rw [map_mul ψ (X ^ i * Y ^ j * Z ^ k) a, ψa] at hψ
    have h0 := tr_zero (sq_a hT) hψ.pow
    have := congrFun h0 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
    rw [c0] at this; omega
  · rw [map_mul ψ (X ^ i * Y ^ j * Z ^ k) b, ψb] at hψ
    have h0 := tr_zero (sq_b hT) hψ.pow
    have := congrFun h0 1
    change 2 + 2 * (i • wX + j • wY + k • wZ) 1 = 0 at this
    rw [c1] at this; omega
  · rw [map_mul ψ (X ^ i * Y ^ j * Z ^ k) (a * b), map_mul ψ a b, ψa, ψb] at hψ
    have h0 := tr_zero (sq_ab hT) hψ.pow
    have := congrFun h0 2
    change 2 * (i • wX + j • wY + k • wZ) 2 - 2 = 0 at this
    rw [c2] at this; omega

end Prom

theorem promislow_group_is_torsionfree :
    Monoid.IsTorsionFree PromislowGroup := Prom.main

end Kaplansky

#print axioms Kaplansky.promislow_group_is_torsionfree
