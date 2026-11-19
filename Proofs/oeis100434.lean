import Mathlib.Algebra.Ring.Int.Defs

namespace OeisA100434

def a : ℕ → ℤ
  | 0 => 3
  | 1 => 4
  | 2 => -17
  | 3 => -24
  | n + 4 => -6 * a (n + 2) - a n

def c : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => -7
  | 3 => 17
  | n + 4 => -6 * c (n + 2) - c n

def d : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => -10
  | 3 => -24
  | n + 4 => -6 * d (n + 2) - d n

def b (n : ℕ) : ℤ :=
  if n % 2 = 0 then -c (n + 1)
  else c (n - 1)

def e (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    d n / 2
  else
    - (d (n - 1) / 2)

def f (n : ℕ) : ℤ :=
  let m := n / 2
  d (2 * m + 1) / 2

def g (n : ℕ) : ℤ :=
  if n % 2 = 0 then 0
  else c n

namespace R

/-- The common recurrence. -/
def Rec (u : ℕ → ℤ) : Prop := ∀ n, u (n + 4) = -6 * u (n + 2) - u n

theorem eq_of_rec {u v : ℕ → ℤ} (hu : Rec u) (hv : Rec v)
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) :
    ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) ∧ u (n + 2) = v (n + 2) ∧
      u (n + 3) = v (n + 3) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2, h3⟩
    | succ k ih =>
      obtain ⟨e0, e1, e2, e3⟩ := ih
      refine ⟨e1, e2, e3, ?_⟩
      have := hu k
      have := hv k
      show u (k + 4) = v (k + 4)
      omega
  intro n
  exact (key n).1

theorem rec_a : Rec a := fun _ => rfl
theorem rec_c : Rec c := fun _ => rfl
theorem rec_d : Rec d := fun _ => rfl

theorem rec_add {u v : ℕ → ℤ} (hu : Rec u) (hv : Rec v) : Rec (fun n => u n + v n) := by
  intro n
  have := hu n
  have := hv n
  show u (n + 4) + v (n + 4) = -6 * (u (n + 2) + v (n + 2)) - (u n + v n)
  omega

theorem rec_b : Rec b := by
  intro n
  unfold b
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos (by omega : (n + 4) % 2 = 0), if_pos (by omega : (n + 2) % 2 = 0), if_pos h]
    have := rec_c (n + 1)
    rw [show n + 1 + 4 = n + 4 + 1 by omega, show n + 1 + 2 = n + 2 + 1 by omega] at this
    omega
  · rw [if_neg (by omega : ¬ (n + 4) % 2 = 0), if_neg (by omega : ¬ (n + 2) % 2 = 0),
      if_neg (by omega : ¬ n % 2 = 0)]
    have := rec_c (n - 1)
    rw [show n - 1 + 4 = n + 4 - 1 by omega, show n - 1 + 2 = n + 2 - 1 by omega] at this
    omega

theorem rec_g : Rec g := by
  intro n
  unfold g
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [if_pos (by omega : (n + 4) % 2 = 0), if_pos (by omega : (n + 2) % 2 = 0), if_pos h]
    omega
  · rw [if_neg (by omega : ¬ (n + 4) % 2 = 0), if_neg (by omega : ¬ (n + 2) % 2 = 0),
      if_neg (by omega : ¬ n % 2 = 0)]
    exact rec_c n

/-- Half of `d`. -/
def h : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => -5
  | 3 => -12
  | n + 4 => -6 * h (n + 2) - h n

theorem rec_h : Rec h := fun _ => rfl

theorem d_eq : ∀ n, d n = 2 * h n := by
  refine eq_of_rec (v := fun n => 2 * h n) rec_d ?_ rfl rfl rfl rfl
  intro n
  have := rec_h n
  show 2 * h (n + 4) = -6 * (2 * h (n + 2)) - 2 * h n
  omega

theorem d_half (n : ℕ) : d n / 2 = h n := by
  rw [d_eq n]
  exact Int.mul_ediv_cancel_left _ (by decide)

theorem rec_e : Rec e := by
  intro n
  unfold e
  simp only [d_half]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · rw [if_pos (by omega : (n + 4) % 2 = 0), if_pos (by omega : (n + 2) % 2 = 0), if_pos hn]
    exact rec_h n
  · rw [if_neg (by omega : ¬ (n + 4) % 2 = 0), if_neg (by omega : ¬ (n + 2) % 2 = 0),
      if_neg (by omega : ¬ n % 2 = 0)]
    have := rec_h (n - 1)
    rw [show n - 1 + 4 = n + 4 - 1 by omega, show n - 1 + 2 = n + 2 - 1 by omega] at this
    omega

theorem rec_f : Rec f := by
  intro n
  unfold f
  simp only [d_half]
  have := rec_h (2 * (n / 2) + 1)
  rw [show 2 * ((n + 4) / 2) + 1 = 2 * (n / 2) + 1 + 4 by omega,
    show 2 * ((n + 2) / 2) + 1 = 2 * (n / 2) + 1 + 2 by omega]
  exact this

end R

open R in
theorem conjecture1 (n : ℕ) : c n + d n = b n :=
  eq_of_rec (u := fun n => c n + d n) (rec_add rec_c rec_d) rec_b rfl rfl rfl rfl n

open R in
theorem conjecture2 (n : ℕ) : e n + f n = b n :=
  eq_of_rec (u := fun n => e n + f n) (rec_add rec_e rec_f) rec_b
    (by decide) (by decide) (by decide) (by decide) n

open R in
theorem conjecture3 (n : ℕ) : g n + a n = b n :=
  eq_of_rec (u := fun n => g n + a n) (rec_add rec_g rec_a) rec_b
    (by decide) (by decide) (by decide) (by decide) n

end OeisA100434

#print axioms OeisA100434.conjecture1
#print axioms OeisA100434.conjecture2
#print axioms OeisA100434.conjecture3
