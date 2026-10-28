module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-!
# Integral columns with Gram matrix `I + 3J`

If at least five integral columns have scalar products `3 + δᵢⱼ` and a
specified row is constantly `-1`, their nonzero entries occupy three common
rows and one distinct additional row for each column. The two other common
rows have constant signs. Each additional row has its own sign.

Removing the specified row leaves columns of squared norm three. Integrality
forces their nonzero entries to be signs. Differences of distinct columns
have squared norm two, so signs agree wherever both columns are nonzero;
their three-element supports therefore intersect in exactly two places.
A family of at least five such triples has a common pair: otherwise all its
members lie in the four-element union of two of them, which admits only four
triples. The proof then constructs the actual row witnesses and coordinate
identity, rather than identifying matrices only up to equivalence.

Source: R. Brauer, *Some applications of the theory of blocks of characters
of finite groups. II*, J. Algebra 1 (1964), §VI, p.318, (6.3)–(6.5).
The argument here is purely about integers and finite sets. In particular,
it permits independent signs in the additional rows.
-/

open scoped BigOperators
open Finset

namespace IntegerGramThree
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
private theorem entry_bound (v : I → ℤ) (h : ∑ k, v k * v k ≤ 3) (k : I) :
    v k = 0 ∨ v k = 1 ∨ v k = -1 := by
  have hb : v k * v k ≤ ∑ l, v l * v l :=
    single_le_sum (fun l _ => mul_self_nonneg (v l)) (mem_univ k)
  have : v k * v k ≤ 3 := hb.trans h
  have hl : -1 ≤ v k := by nlinarith
  have hu : v k ≤ 1 := by nlinarith
  omega

omit [DecidableEq I] in
private theorem support_card (v : I → ℤ) (h : ∑ k, v k * v k = 3) :
    (univ.filter fun k => v k ≠ 0).card = 3 := by
  have he : ∀ k, v k * v k = if v k ≠ 0 then (1 : ℤ) else 0 := by
    intro k
    rcases entry_bound v (le_of_eq h) k with hk | hk | hk <;> simp [hk]
  simp_rw [he] at h
  simp only [sum_boole] at h
  exact_mod_cast h

omit [DecidableEq I] in
private theorem difference_norm (v w : I → ℤ)
    (hv : ∑ k, v k * v k = 3) (hw : ∑ k, w k * w k = 3)
    (hvw : ∑ k, v k * w k = 2) :
    ∑ k, (v k - w k) * (v k - w k) = 2 := by
  calc
    _ = (∑ k, v k * v k) + (∑ k, w k * w k) - 2 * ∑ k, v k * w k := by
      simp only [← sum_add_distrib, ← sum_sub_distrib, mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    _ = 2 := by rw [hv, hw, hvw]; norm_num

omit [DecidableEq I] in
private theorem agree_on_support (v w : I → ℤ)
    (hv : ∑ k, v k * v k = 3) (hw : ∑ k, w k * w k = 3)
    (hvw : ∑ k, v k * w k = 2) (k : I) (hk : v k ≠ 0) (hl : w k ≠ 0) :
    v k = w k := by
  have hd := entry_bound (fun k => v k - w k)
    (le_of_eq (difference_norm v w hv hw hvw) |>.trans (by norm_num)) k
  rcases entry_bound v (le_of_eq hv) k with h | h | h <;>
    rcases entry_bound w (le_of_eq hw) k with h' | h' | h' <;> omega

private theorem support_inter_card (v w : I → ℤ)
    (hv : ∑ k, v k * v k = 3) (hw : ∑ k, w k * w k = 3)
    (hvw : ∑ k, v k * w k = 2) :
    ((univ.filter fun k => v k ≠ 0) ∩ (univ.filter fun k => w k ≠ 0)).card = 2 := by
  have he : ∀ k, v k * w k = if v k ≠ 0 ∧ w k ≠ 0 then (1 : ℤ) else 0 := by
    intro k
    split_ifs with h
    · rw [← agree_on_support v w hv hw hvw k h.1 h.2]
      rcases entry_bound v (le_of_eq hv) k with hk | hk | hk <;> simp_all
    · rcases not_and_or.mp h with h | h <;> simp_all
  simp_rw [he] at hvw
  have heq : (univ.filter fun k => v k ≠ 0) ∩ (univ.filter fun k => w k ≠ 0) =
      univ.filter (fun k => v k ≠ 0 ∧ w k ≠ 0) := by ext; simp
  rw [heq]
  simp only [sum_boole] at hvw
  exact_mod_cast hvw

-- A triple adjacent to two fixed triples either contains their intersection
-- or lies in their union.
omit [Fintype I] in
private theorem triple_dichotomy (A B T : Finset I)
    (hT : T.card = 3) (hC : (A ∩ B).card = 2)
    (hA : (T ∩ A).card = 2) (hB : (T ∩ B).card = 2) :
    A ∩ B ⊆ T ∨ T ⊆ A ∪ B := by
  have h := card_union_add_card_inter (T ∩ A) (T ∩ B)
  rw [← inter_union_distrib_left, ← inter_inter_distrib_left, hA, hB] at h
  have hTU := card_le_card (inter_subset_left : T ∩ (A ∪ B) ⊆ T)
  have hTC := card_le_card (inter_subset_right : T ∩ (A ∩ B) ⊆ A ∩ B)
  by_cases he : (T ∩ (A ∩ B)).card = 2
  · left
    have heq := eq_of_subset_of_card_le inter_subset_right (by omega :
      (A ∩ B).card ≤ (T ∩ (A ∩ B)).card)
    rw [← heq]
    exact inter_subset_left
  · right
    have heq := eq_of_subset_of_card_le inter_subset_left (by omega :
      T.card ≤ (T ∩ (A ∪ B)).card)
    rw [← heq]
    exact inter_subset_right

omit [Fintype I] in
private theorem triple_in_union (C U S T : Finset I)
    (hC : C.card = 2) (hT : T.card = 3) (hCU : C ⊆ U)
    (hSU : S ⊆ U) (hCS : ¬C ⊆ S) (hCT : C ⊆ T)
    (hST : (S ∩ T).card = 2) : T ⊆ U := by
  have hCtu : C ⊆ T ∩ U := subset_inter hCT hCU
  have hstu : S ∩ T ⊆ T ∩ U := by
    intro x hx
    exact mem_inter.mpr ⟨(mem_inter.mp hx).2, hSU (mem_inter.mp hx).1⟩
  have hu := card_le_card (inter_subset_left : T ∩ U ⊆ T)
  by_cases he : (T ∩ U).card = 3
  · have heq := eq_of_subset_of_card_le inter_subset_left (by omega :
      T.card ≤ (T ∩ U).card)
    rw [← heq]
    exact inter_subset_right
  · have heq := eq_of_subset_of_card_le hCtu (by omega : (T ∩ U).card ≤ C.card)
    have heq' := eq_of_subset_of_card_le hstu (by omega :
      (T ∩ U).card ≤ (S ∩ T).card)
    exfalso
    apply hCS
    rw [heq, ← heq']
    exact inter_subset_left

omit [Fintype I] in
private theorem common_pair {r : ℕ} (hr : 5 ≤ r) (s : Fin r → Finset I)
    (hs : ∀ j, (s j).card = 3)
    (hi : ∀ i j, i ≠ j → (s i ∩ s j).card = 2) :
    ∃ C : Finset I, C.card = 2 ∧ ∀ j, C ⊆ s j := by
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let C := s a ∩ s b
  let U := s a ∪ s b
  have hC : C.card = 2 := hi a b hab
  have hU : U.card = 4 := by
    have := card_union_add_card_inter (s a) (s b)
    dsimp [U]
    rw [hs a, hs b, hi a b hab] at this
    omega
  have hd : ∀ j, C ⊆ s j ∨ s j ⊆ U := by
    intro j
    by_cases hja : j = a
    · subst j; exact Or.inl inter_subset_left
    by_cases hjb : j = b
    · subst j; exact Or.inl inter_subset_right
    exact triple_dichotomy (s a) (s b) (s j) (hs j) hC (hi j a hja) (hi j b hjb)
  by_cases hc : ∀ j, C ⊆ s j
  · exact ⟨C, hC, hc⟩
  push Not at hc
  obtain ⟨j, hj⟩ := hc
  have hju : s j ⊆ U := (hd j).resolve_left hj
  have hall : ∀ k, s k ⊆ U := by
    intro k
    by_cases hjk : j = k
    · simpa [← hjk] using hju
    rcases hd k with hk | hk
    · exact triple_in_union C U (s j) (s k) hC (hs k)
        (inter_subset_left.trans subset_union_left) hju hj hk (hi j k hjk)
    · exact hk
  have hinj : Function.Injective s := by
    intro j k he
    by_contra hjk
    have hh := hi j k hjk
    rw [he, inter_self, hs k] at hh
    omega
  have hle : r ≤ 4 := by
    have hmap : univ.image s ⊆ U.powersetCard 3 := by
      intro t ht
      obtain ⟨k, _, rfl⟩ := mem_image.mp ht
      exact mem_powersetCard.mpr ⟨hall k, hs k⟩
    have := card_le_card hmap
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin,
      card_powersetCard, hU] at this
    exact this
  omega

/-- Brauer's integral Gram-matrix normal form, with explicit common rows,
an embedding selecting the additional rows, and the value at every coordinate.
The signs `eps j` are allowed to vary with the column. -/
public theorem exists_normal_form {r : ℕ} (hr : 5 ≤ r) (b : Fin r → I → ℤ) (i0 : I)
    (h0 : ∀ j, b j i0 = -1)
    (hgram : ∀ i j, ∑ k, b i k * b j k = 3 + if i = j then 1 else 0) :
    ∃ (i1 i2 : I) (t : Fin r ↪ I) (d e : ℤ) (eps : Fin r → ℤ),
      i1 ≠ i0 ∧ i2 ≠ i0 ∧ i1 ≠ i2 ∧
      (∀ j, t j ≠ i0 ∧ t j ≠ i1 ∧ t j ≠ i2) ∧
      (d = 1 ∨ d = -1) ∧ (e = 1 ∨ e = -1) ∧
      (∀ j, eps j = 1 ∨ eps j = -1) ∧
      ∀ j k, b j k = if k = i0 then -1 else if k = i1 then d else
        if k = i2 then e else if k = t j then eps j else 0 := by
  let v : Fin r → I → ℤ := fun j k => if k = i0 then 0 else b j k
  have hv0 : ∀ j, v j i0 = 0 := by intro j; simp [v]
  have hvg : ∀ i j, ∑ k, v i k * v j k = 2 + if i = j then 1 else 0 := by
    intro i j
    have he : ∀ k, b i k * b j k = v i k * v j k + if k = i0 then 1 else 0 := by
      intro k
      by_cases hk : k = i0
      · subst k; simp [v, h0]
      · simp [v, hk]
    have hg := hgram i j
    simp_rw [he] at hg
    rw [sum_add_distrib] at hg
    have hone : (∑ k : I, if k = i0 then (1 : ℤ) else 0) = 1 := by simp
    rw [hone] at hg
    omega
  have hv : ∀ j, ∑ k, v j k * v j k = 3 := by intro j; simpa using hvg j j
  have hvw : ∀ i j, i ≠ j → ∑ k, v i k * v j k = 2 := by
    intro i j hij; simpa [hij] using hvg i j
  let s : Fin r → Finset I := fun j => univ.filter (fun k => v j k ≠ 0)
  have hmem : ∀ j k, k ∈ s j ↔ v j k ≠ 0 := by intros; simp [s]
  have hs : ∀ j, (s j).card = 3 := fun j => support_card (v j) (hv j)
  have hi : ∀ i j, i ≠ j → (s i ∩ s j).card = 2 :=
    fun i j hij => support_inter_card (v i) (v j) (hv i) (hv j) (hvw i j hij)
  obtain ⟨C, hC, hCs⟩ := common_pair hr s hs hi
  obtain ⟨i1, i2, h12, hCeq⟩ := card_eq_two.mp hC
  have h1C : i1 ∈ C := by simp [hCeq]
  have h2C : i2 ∈ C := by simp [hCeq]
  have h1 : ∀ j, v j i1 ≠ 0 := fun j => (hmem j i1).mp (hCs j h1C)
  have h2 : ∀ j, v j i2 ≠ 0 := fun j => (hmem j i2).mp (hCs j h2C)
  have ht : ∀ j, ∃ k, k ∈ s j ∧ k ∉ C := by
    intro j
    exact exists_mem_notMem_of_card_lt_card (by rw [hC, hs j]; omega)
  choose t ht using ht
  have hsf : ∀ j, s j = insert (t j) C := by
    intro j
    symm
    apply eq_of_subset_of_card_le (insert_subset (ht j).1 (hCs j))
    rw [card_insert_of_notMem (ht j).2, hC, hs j]
  have htinj : Function.Injective t := by
    intro i j hij
    by_contra hne
    have he : s i = s j := by rw [hsf i, hsf j, hij]
    have hh := hi i j hne
    rw [he, inter_self, hs j] at hh
    omega
  let a : Fin r := ⟨0, by omega⟩
  have ha1 : ∀ j, v j i1 = v a i1 := by
    intro j
    by_cases hja : j = a
    · rw [hja]
    · exact agree_on_support (v j) (v a) (hv j) (hv a) (hvw j a hja) i1 (h1 j) (h1 a)
  have ha2 : ∀ j, v j i2 = v a i2 := by
    intro j
    by_cases hja : j = a
    · rw [hja]
    · exact agree_on_support (v j) (v a) (hv j) (hv a) (hvw j a hja) i2 (h2 j) (h2 a)
  have h10 : i1 ≠ i0 := by intro he; have := h1 a; simp [he, hv0] at this
  have h20 : i2 ≠ i0 := by intro he; have := h2 a; simp [he, hv0] at this
  have ht0 : ∀ j, t j ≠ i0 := by
    intro j he
    have hh := (hmem j (t j)).mp (ht j).1
    simp [he, hv0] at hh
  have ht1 : ∀ j, t j ≠ i1 := by intro j he; exact (ht j).2 (he ▸ h1C)
  have ht2 : ∀ j, t j ≠ i2 := by intro j he; exact (ht j).2 (he ▸ h2C)
  refine ⟨i1, i2, ⟨t, htinj⟩, v a i1, v a i2, (fun j => v j (t j)),
    h10, h20, h12, (fun j => ⟨ht0 j, ht1 j, ht2 j⟩), ?_, ?_, ?_, ?_⟩
  · exact (entry_bound (v a) (le_of_eq (hv a)) i1).resolve_left (h1 a)
  · exact (entry_bound (v a) (le_of_eq (hv a)) i2).resolve_left (h2 a)
  · intro j
    exact (entry_bound (v j) (le_of_eq (hv j)) (t j)).resolve_left
      ((hmem j (t j)).mp (ht j).1)
  · intro j k
    change b j k = if k = i0 then -1 else if k = i1 then v a i1 else
      if k = i2 then v a i2 else if k = t j then v j (t j) else 0
    by_cases hk0 : k = i0
    · subst k; simp [h0]
    have hbk : b j k = v j k := by simp [v, hk0]
    rw [hbk, if_neg hk0]
    by_cases hk1 : k = i1
    · subst k; simp [ha1]
    rw [if_neg hk1]
    by_cases hk2 : k = i2
    · subst k; simp [ha2]
    rw [if_neg hk2]
    by_cases hkt : k = t j
    · simp [hkt]
    rw [if_neg hkt]
    have hks : k ∉ s j := by simp [hsf j, hCeq, hk1, hk2, hkt]
    simpa [hmem] using hks
end IntegerGramThree
