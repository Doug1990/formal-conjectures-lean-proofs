import Mathlib.Data.List.SplitBy
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace OeisA384222

/-- The divisors of $n$ in increasing order. -/
def divisorList (n : ℕ) : List ℕ := (List.range' 1 n).filter (· ∣ n)

/-- The 2-dense sublists of divisors of $n$. -/
def denseSublists (n : ℕ) : List (List ℕ) :=
  (divisorList n).splitBy fun d d' => d' ≤ 2 * d

/-- Row $n$ of the triangle: the lengths of the 2-dense sublists of divisors of $n$. -/
def row (n : ℕ) : List ℕ := (denseSublists n).map List.length

/-- Row $n$ of A384225: the numbers of odd terms in the 2-dense sublists of divisors of $n$. -/
def oddRow (n : ℕ) : List ℕ := (denseSublists n).map (List.countP fun d => d % 2 = 1)

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

/-! ### Palindrome part -/

lemma chain_imp {α : Type*} {R S : α → α → Prop} : ∀ (b : List α),
    (∀ x ∈ b, ∀ y ∈ b, R x y → S x y) → b.IsChain R → b.IsChain S
  | [], _, _ => by simp
  | [a], _, _ => by simp
  | a :: c :: t, h, hc => by
    rw [List.isChain_cons_cons] at hc ⊢
    exact ⟨h a (by simp) c (by simp) hc.1, chain_imp (c :: t)
      (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hc.2⟩

lemma rev_split {α : Type*} (r : α → α → Bool) (f : α → α) (l : List α)
    (hs : ∀ x ∈ l, ∀ y ∈ l, r (f y) (f x) = r x y) :
    (l.map f).reverse.splitBy r = ((l.splitBy r).map (fun b => (b.map f).reverse)).reverse := by
  have hmem : ∀ b ∈ l.splitBy r, ∀ x ∈ b, x ∈ l := fun b hb x hx => by
    rw [← List.flatten_splitBy r l]
    exact List.mem_flatten.2 ⟨b, hb, hx⟩
  rw [List.splitBy_eq_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← List.flatten_splitBy r l]
    rw [List.map_flatten, List.reverse_flatten, List.map_map]
    rfl
  · simp only [List.mem_reverse, List.mem_map, not_exists, not_and]
    intro b hb h
    exact List.ne_nil_of_mem_splitBy hb (by simpa using h)
  · intro m hm
    simp only [List.mem_reverse, List.mem_map] at hm
    obtain ⟨b, hb, rfl⟩ := hm
    rw [List.isChain_reverse, List.isChain_map]
    refine chain_imp b (fun x hx y hy h => ?_) (List.isChain_of_mem_splitBy hb)
    show r (f y) (f x) = true
    rw [hs x (hmem b hb x hx) y (hmem b hb y hy)]
    exact h
  · rw [List.isChain_reverse, List.isChain_map]
    refine chain_imp _ (fun a ha b hb h => ?_) (List.isChain_getLast_head_splitBy r l)
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨by simpa using h2, by simpa using h1, ?_⟩
    simp only [List.getLast_reverse, List.head_reverse, List.getLast_map, List.head_map]
    rw [hs _ (hmem a ha _ (List.getLast_mem _)) _ (hmem b hb _ (List.head_mem _))]
    exact h3

lemma div_facts (n x : ℕ) (hn : 0 < n) (hx : x ∣ n) : ∃ a, n = x * a ∧ n / x = a ∧ 0 < x ∧ 0 < a := by
  obtain ⟨a, rfl⟩ := hx
  have hx0 : 0 < x := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  exact ⟨a, rfl, Nat.mul_div_cancel_left a hx0, hx0, ha0⟩

lemma rev_D (n : ℕ) (hn : 0 < n) : ((divisorList n).map (n / ·)).reverse = divisorList n := by
  have hpw := pw_D n
  have hpw' : ((divisorList n).map (n / ·)).reverse.Pairwise (· < ·) := by
    rw [List.pairwise_reverse, List.pairwise_map]
    refine hpw.imp_of_mem (fun {x y} hx hy hxy => ?_)
    obtain ⟨a, ha, hax, hx0, ha0⟩ := div_facts n x hn ((mem_D n hn x).1 hx)
    obtain ⟨b, hb, hby, hy0, hb0⟩ := div_facts n y hn ((mem_D n hn y).1 hy)
    rw [hax, hby]
    nlinarith
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (hpw'.imp le_of_lt) (hpw.imp le_of_lt)
  rw [List.perm_ext_iff_of_nodup (hpw'.imp (fun h => ne_of_lt h)) (hpw.imp (fun h => ne_of_lt h))]
  intro d
  rw [List.mem_reverse, List.mem_map, mem_D n hn]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Nat.div_dvd_of_dvd ((mem_D n hn x).1 hx)
  · intro hd
    exact ⟨n / d, (mem_D n hn _).2 (Nat.div_dvd_of_dvd hd), Nat.div_div_self hd hn.ne'⟩

lemma hs_D (n : ℕ) (hn : 0 < n) : ∀ x ∈ divisorList n, ∀ y ∈ divisorList n,
    (fun d d' : ℕ => decide (d' ≤ 2 * d)) (n / y) (n / x) =
      (fun d d' : ℕ => decide (d' ≤ 2 * d)) x y := by
  intro x hx y hy
  obtain ⟨a, ha, hax, hx0, ha0⟩ := div_facts n x hn ((mem_D n hn x).1 hx)
  obtain ⟨b, hb, hby, hy0, hb0⟩ := div_facts n y hn ((mem_D n hn y).1 hy)
  simp only [hax, hby, decide_eq_decide]
  constructor
  · intro h
    by_contra h'
    nlinarith
  · intro h
    by_contra h'
    nlinarith

end Q

theorem conjecture_1 (n : ℕ) (hn : 0 < n) :
    (∀ k ∈ row n, 0 < k) ∧ (row n).sum = n.divisors.card ∧ (row n).reverse = row n := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    unfold row at hk
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hk
    exact List.length_pos_of_ne_nil (List.ne_nil_of_mem_splitBy hb)
  · unfold row
    rw [← List.length_flatten]
    unfold denseSublists
    rw [List.flatten_splitBy]
    have hnd : (divisorList n).Nodup := (Q.pw_D n).imp (fun h => ne_of_lt h)
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext d
    rw [List.mem_toFinset, Q.mem_D n hn, Nat.mem_divisors]
    exact ⟨fun h => ⟨h, hn.ne'⟩, fun h => h.1⟩
  · have key : (divisorList n).splitBy (fun d d' : ℕ => decide (d' ≤ 2 * d)) =
        (((divisorList n).splitBy (fun d d' : ℕ => decide (d' ≤ 2 * d))).map
          (fun b => (b.map (n / ·)).reverse)).reverse := by
      conv_lhs => rw [← Q.rev_D n hn]
      exact Q.rev_split _ _ _ (Q.hs_D n hn)
    unfold row denseSublists
    conv_rhs => rw [key]
    rw [List.map_reverse, List.map_map]
    congr 1
    apply List.map_congr_left
    intro b _
    simp

theorem conjecture_formula (n : ℕ) (hn : 0 < n) :
    row n = (oddRow n).map ((padicValNat 2 n + 1) * ·) := by
  unfold row oddRow
  rw [List.map_map]
  exact List.map_congr_left (fun m hm => Q.block_len n hn m hm)

end OeisA384222

#print axioms OeisA384222.conjecture_1
#print axioms OeisA384222.conjecture_formula
