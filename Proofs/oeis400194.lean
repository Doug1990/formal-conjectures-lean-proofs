import Mathlib.Data.List.SplitBy
import Mathlib.Data.List.Chain
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

namespace OeisA400194

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- The maximum number of terms in a 2-dense sublist of divisors of $n$. -/
def a (n : ℕ) : ℕ := ((denseSublists n).map List.length).foldr max 0

/-- The maximum number of odd terms in a 2-dense sublist of divisors of $n$ (A400195). -/
def b (n : ℕ) : ℕ := ((denseSublists n).map (List.countP fun d => d % 2 = 1)).foldr max 0

namespace Q

lemma le_getLast (l : List ℕ) (h : l ≠ []) (hp : l.Pairwise (· < ·)) (x : ℕ) (hx : x ∈ l) :
    x ≤ l.getLast h := by
  rw [← List.dropLast_append_getLast h] at hp hx
  rw [List.pairwise_append] at hp
  rcases List.mem_append.1 hx with hx | hx
  · exact le_of_lt (hp.2.2 x hx _ (List.mem_singleton_self _))
  · exact le_of_eq (List.mem_singleton.1 hx)

lemma head_le (l : List ℕ) (h : l ≠ []) (hp : l.Pairwise (· < ·)) (x : ℕ) (hx : x ∈ l) :
    l.head h ≤ x := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t =>
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_refl _
    · exact le_of_lt (hp.1 x hx)

lemma G : ∀ (bs : List (List ℕ)), bs.flatten.Pairwise (· < ·) → (∀ b ∈ bs, b ≠ []) →
    bs.IsChain (fun a b => ∃ ha hb, ¬ (b.head hb ≤ 2 * a.getLast ha)) →
    ∀ b ∈ bs, ∀ b' ∈ bs, ∀ x ∈ b, ∀ y ∈ b', x ≤ y → y ≤ 2 * x → y ∈ b ∧ x ∈ b'
  | [], _, _, _ => by simp
  | b₀ :: rest, hp, hne, hc => by
    intro b hb b' hb' x hx y hy hxy hyx
    rw [List.flatten_cons, List.pairwise_append] at hp
    obtain ⟨hp0, hpr, hcross⟩ := hp
    rcases List.mem_cons.1 hb with h | hb
    · subst h
      rcases List.mem_cons.1 hb' with h' | hb'
      · subst h'
        exact ⟨hy, hx⟩
      · exfalso
        cases rest with
        | nil => simp at hb'
        | cons b₁ rest' =>
          rw [List.isChain_cons_cons] at hc
          obtain ⟨⟨ha, hb1, hgt⟩, _⟩ := hc
          have h1 : x ≤ b.getLast ha := le_getLast b ha hp0 x hx
          have h2 : b₁.head hb1 ≤ y := by
            rw [List.flatten_cons, List.pairwise_append] at hpr
            have hy' : y ∈ (b₁ :: rest').flatten := List.mem_flatten.2 ⟨b', hb', hy⟩
            rw [List.flatten_cons, List.mem_append] at hy'
            rcases hy' with hy' | hy'
            · exact head_le b₁ hb1 hpr.1 y hy'
            · exact le_of_lt (hpr.2.2 _ (List.head_mem hb1) y hy')
          omega
    · rcases List.mem_cons.1 hb' with h' | hbr'
      · subst h'
        exfalso
        have := hcross y hy x (List.mem_flatten.2 ⟨b, by assumption, hx⟩)
        omega
      · exact G rest hpr (fun c hc => hne c (List.mem_cons_of_mem _ hc)) hc.tail
          b (by assumption) b' hbr' x hx y hy hxy hyx

lemma mem_D (n : ℕ) (hn : 0 < n) (d : ℕ) : d ∈ divisorList n ↔ d ∣ n := by
  unfold divisorList
  rw [List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨_, h⟩
    simpa using h
  · intro h
    have := Nat.le_of_dvd hn h
    have : 0 < d := Nat.pos_of_dvd_of_pos h hn
    exact ⟨by omega, by simpa using h⟩

lemma pw_D (n : ℕ) : (divisorList n).Pairwise (· < ·) := by
  unfold divisorList
  exact (List.pairwise_lt_range' (s := 1) (n := n)).filter _

lemma struct (n : ℕ) :
    (denseSublists n).flatten.Pairwise (· < ·) ∧ (∀ b ∈ denseSublists n, b ≠ []) ∧
    (denseSublists n).IsChain (fun a b => ∃ ha hb, ¬ (b.head hb ≤ 2 * a.getLast ha)) := by
  unfold denseSublists
  refine ⟨?_, fun b hb => List.ne_nil_of_mem_splitBy hb, ?_⟩
  · rw [List.flatten_splitBy]
    exact pw_D n
  · exact (List.isChain_getLast_head_splitBy _ _).imp
      (fun a b ⟨ha, hb, h⟩ => ⟨ha, hb, of_decide_eq_false h⟩)

lemma close (n : ℕ) (m b' : List ℕ) (hm : m ∈ denseSublists n) (hb' : b' ∈ denseSublists n)
    (x y : ℕ) (hx : x ∈ m) (hy : y ∈ b') (h1 : x ≤ y) (h2 : y ≤ 2 * x) : y ∈ m ∧ x ∈ b' := by
  obtain ⟨h₁, h₂, h₃⟩ := struct n
  exact G _ h₁ h₂ h₃ m hm b' hb' x hx y hy h1 h2

lemma dvd_of_mem (n : ℕ) (hn : 0 < n) (m : List ℕ) (hm : m ∈ denseSublists n) (x : ℕ)
    (hx : x ∈ m) : x ∣ n := by
  have : x ∈ (denseSublists n).flatten := List.mem_flatten.2 ⟨m, hm, hx⟩
  unfold denseSublists at this
  rw [List.flatten_splitBy] at this
  exact (mem_D n hn x).1 this

lemma exists_block (n : ℕ) (hn : 0 < n) (x : ℕ) (hx : x ∣ n) :
    ∃ b ∈ denseSublists n, x ∈ b := by
  have : x ∈ (denseSublists n).flatten := by
    unfold denseSublists
    rw [List.flatten_splitBy]
    exact (mem_D n hn x).2 hx
  obtain ⟨b, hb, hxb⟩ := List.mem_flatten.1 this
  exact ⟨b, hb, hxb⟩

lemma dbl (n : ℕ) (hn : 0 < n) (m : List ℕ) (hm : m ∈ denseSublists n) (y : ℕ) (hy : y ∈ m)
    (h : 2 * y ∣ n) : 2 * y ∈ m := by
  obtain ⟨b', hb', h'⟩ := exists_block n hn _ h
  exact (close n m b' hm hb' y (2 * y) hy h' (by omega) (le_refl _)).1

lemma half (n : ℕ) (hn : 0 < n) (m : List ℕ) (hm : m ∈ denseSublists n) (y : ℕ)
    (hy : 2 * y ∈ m) : y ∈ m := by
  have hd : y ∣ n := Dvd.dvd.trans (dvd_mul_left y 2) (dvd_of_mem n hn m hm _ hy)
  obtain ⟨b', hb', h'⟩ := exists_block n hn _ hd
  exact (close n b' m hb' hm y (2 * y) h' hy (by omega) (le_refl _)).2

lemma up (n : ℕ) (hn : 0 < n) (m : List ℕ) (hm : m ∈ denseSublists n) (o : ℕ) (ho : o ∈ m) :
    ∀ i, o * 2 ^ i ∣ n → o * 2 ^ i ∈ m
  | 0, _ => by simpa using ho
  | i + 1, h => by
    have e : o * 2 ^ (i + 1) = 2 * (o * 2 ^ i) := by ring
    rw [e] at h ⊢
    exact dbl n hn m hm _ (up n hn m hm o ho i (Dvd.dvd.trans (dvd_mul_left _ 2) h)) h

lemma down (n : ℕ) (hn : 0 < n) (m : List ℕ) (hm : m ∈ denseSublists n) (o : ℕ) :
    ∀ k, 2 ^ k * o ∈ m → o ∈ m
  | 0, h => by simpa using h
  | k + 1, h => by
    have e : 2 ^ (k + 1) * o = 2 * (2 ^ k * o) := by ring
    rw [e] at h
    exact down n hn m hm o k (half n hn m hm _ h)

lemma v2 (o i : ℕ) (ho : o % 2 = 1) : padicValNat 2 (o * 2 ^ i) = i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat.mul (by omega) (pow_ne_zero _ (by decide)), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by omega)]
  omega

lemma block_len (n : ℕ) (hn : 0 < n) (m : List ℕ) (hm : m ∈ denseSublists n) :
    m.length = (padicValNat 2 n + 1) * m.countP (fun d => d % 2 = 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₁, -, -⟩ := struct n
  have hpw : m.Pairwise (· < ·) := (List.pairwise_flatten.1 h₁).1 m hm
  have hnd : m.Nodup := hpw.imp (fun h => ne_of_lt h)
  have hc : m.countP (fun d => d % 2 = 1) = (m.toFinset.filter (fun d => d % 2 = 1)).card := by
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnd.filter _),
      List.toFinset_filter]
    simp
  rw [hc, ← List.toFinset_card_of_nodup hnd]
  have himg : m.toFinset = ((m.toFinset.filter (fun d => d % 2 = 1)) ×ˢ
      Finset.range (padicValNat 2 n + 1)).image (fun p => p.1 * 2 ^ p.2) := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range, Prod.exists]
    constructor
    · intro hx
      have hxd := dvd_of_mem n hn m hm x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [zero_dvd_iff] at hxd
        omega
      obtain ⟨k, o, hodd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hx0
      refine ⟨o, k, ⟨⟨down n hn m hm o k hx, Nat.odd_iff.1 hodd⟩, ?_⟩, Nat.mul_comm _ _⟩
      have : 2 ^ k ∣ n := Dvd.dvd.trans (dvd_mul_right _ _) hxd
      rw [padicValNat_dvd_iff_le hn.ne'] at this
      omega
    · rintro ⟨o, i, ⟨⟨ho, hodd⟩, hi⟩, rfl⟩
      apply up n hn m hm o ho i
      have h1 : o ∣ n := dvd_of_mem n hn m hm o ho
      have h2 : 2 ^ i ∣ n :=
        Dvd.dvd.trans (pow_dvd_pow 2 (by omega : i ≤ padicValNat 2 n)) pow_padicValNat_dvd
      have hcop : Nat.Coprime (2 ^ i) o :=
        Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega))
      rw [Nat.mul_comm]
      exact hcop.mul_dvd_of_dvd_of_dvd h2 h1
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * 2 ^ p.2)
      ↑((m.toFinset.filter (fun d => d % 2 = 1)) ×ˢ Finset.range (padicValNat 2 n + 1)) := by
    rintro ⟨o, i⟩ hp ⟨o', j⟩ hq he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter] at hp hq
    simp only at he
    have hij : i = j := by rw [← v2 o i hp.1.2, ← v2 o' j hq.1.2, he]
    subst hij
    have : o = o' := Nat.eq_of_mul_eq_mul_right (pow_pos (by decide) i) he
    rw [this]
  have hcard := Finset.card_image_of_injOn hinj
  rw [← himg, Finset.card_product, Finset.card_range] at hcard
  rw [hcard, Nat.mul_comm]

lemma foldr_mul {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun x => c * f x)).foldr max 0 = c * (l.map f).foldr max 0 := by
  induction l with
  | nil => simp
  | cons x t ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih]
    rcases le_total (f x) ((t.map f).foldr max 0) with h | h
    · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left c h)]
    · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_left c h)]

end Q

theorem conjecture (n : ℕ) (hn : 0 < n) : a n = (padicValNat 2 n + 1) * b n := by
  unfold a b
  rw [List.map_congr_left (fun m hm => Q.block_len n hn m hm), Q.foldr_mul]

end OeisA400194

#print axioms OeisA400194.conjecture
