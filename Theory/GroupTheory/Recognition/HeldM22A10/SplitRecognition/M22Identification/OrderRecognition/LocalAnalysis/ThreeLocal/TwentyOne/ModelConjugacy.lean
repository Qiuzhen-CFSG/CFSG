module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.ModelEight

/-!
# Conjugacy of self-centralizing elementary eight-groups in the twisted model

A self-centralizing subgroup contains the central involution `z 0`. Its order
allows us to choose two further elements whose eight binary words exhaust it.
The finite calculation checks every commuting pair of elements with square one:
either both lie in `modelHstar`, both conjugate into it by `z 1`, or one of ten
explicit elements centralizes the pair but lies outside those binary words.
The last case contradicts self-centralization. In the first two cases the
three generators conjugate into `modelHstar`, and equal orders give equality.

The finite alternative is checked by the Lean kernel in the actual semidirect
product. The generator selection and the count of eight distinct words are
proved separately by finite cardinality and group cancellation.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 4, p.8, the local conjugacy step in Lemma 9.
-/

open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Theory.GroupTheory.HeldM22A10
local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance : DecidablePred (· ∈ modelHstar) := fun x =>
  decidable_of_iff (a * x = x * a ∧ b * x = x * b)
    (by simp [modelHstar, mem_centralizer_iff])

-- The words in three commuting elements of square one.
private def words (x y : TwistedModel) : Finset TwistedModel :=
  {1, z 0, x, y, z 0 * x, z 0 * y, x * y, z 0 * x * y}

-- A finite list of possible witnesses to failure of self-centralization.
private def obstacles : Fin 10 → TwistedModel :=
  ![SemidirectProduct.inl (Multiplicative.ofAdd ![1, 1, 0, 0]),
    SemidirectProduct.inl (Multiplicative.ofAdd ![1, 0, 1, 0]),
    b, d, SemidirectProduct.inr (Equiv.swap 1 2),
    SemidirectProduct.inr (Equiv.swap 1 3),
    SemidirectProduct.inr (Equiv.swap 0 1),
    SemidirectProduct.inr (Equiv.swap 0 2), z 1, z 3]

-- The subtype keeps the kernel computation confined to the 52 square-one elements.
set_option maxRecDepth 10000 in
private theorem pair_alternative : ∀ x y : {x : TwistedModel // x * x = 1},
    (x : TwistedModel) * y = y * x →
    ((x : TwistedModel) ∈ modelHstar ∧ (y : TwistedModel) ∈ modelHstar) ∨
    ((MulAut.conj (z 1)) x ∈ modelHstar ∧ (MulAut.conj (z 1)) y ∈ modelHstar) ∨
    ∃ i : Fin 10, (x : TwistedModel) * obstacles i = obstacles i * x ∧
      (y : TwistedModel) * obstacles i = obstacles i * y ∧ obstacles i ∉ words x y := by
  decide +kernel

-- Independent cardinality argument for the eight binary words.
private theorem words_card {G : Type*} [Group G] [DecidableEq G]
    (z x y : G) (hz : z * z = 1) (hx : x * x = 1) (hzx : z * x = x * z)
    (hz1 : z ≠ 1) (hx1 : x ≠ 1) (hxz : x ≠ z)
    (hy : y ∉ ({1, z, x, z * x} : Finset G)) :
    ({1, z, x, y, z * x, z * y, x * y, z * x * y} : Finset G).card = 8 := by
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hx_inv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hzx1 : z * x ≠ 1 := by
    intro h
    have := eq_inv_of_mul_eq_one_right h
    exact hxz (this.trans hz_inv)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  have hzy1 : z * y ≠ 1 := by
    intro h
    exact hy.2.1 ((eq_inv_of_mul_eq_one_right h).trans hz_inv)
  have hxy1 : x * y ≠ 1 := by
    intro h
    exact hy.2.2.1 ((eq_inv_of_mul_eq_one_right h).trans hx_inv)
  have hzx_inv : (z * x)⁻¹ = z * x := by simp [mul_inv_rev, hz_inv, hx_inv, hzx]
  have hzxy1 : z * x * y ≠ 1 := by
    intro h
    exact hy.2.2.2 ((eq_inv_of_mul_eq_one_right h).trans hzx_inv)
  have hzyx : z * y ≠ x := by
    intro h
    apply hy.2.2.2
    calc y = z * (z * y) := by simp [← mul_assoc, hz]
         _ = z * x := by rw [h]
  have hxyz : x * y ≠ z := by
    intro h
    apply hy.2.2.2
    calc y = x * (x * y) := by simp [← mul_assoc, hx]
         _ = z * x := by rw [h, ← hzx]
  have hzxy_z : z * x * y ≠ z := by
    intro h
    have : x * y = 1 := mul_left_cancel (show z * (x * y) = z * 1 by simpa [mul_assoc] using h)
    exact hxy1 this
  have hzxy_x : z * x * y ≠ x := by
    intro h
    have : z * y = 1 := mul_left_cancel (show x * (z * y) = x * 1 by simpa [← mul_assoc, ← hzx] using h)
    exact hzy1 this
  have hzxy_y : z * x * y ≠ y := by simpa using hzx1
  have hzy_zx : z * y ≠ z * x := by simpa using hy.2.2.1
  have hxy_zx : x * y ≠ z * x := by simpa [hzx] using hy.2.1
  repeat rw [Finset.card_insert_of_notMem]
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or,
      Finset.card_singleton, Nat.reduceAdd] <;>
      grind only [mul_left_cancel_iff, mul_right_cancel_iff, mul_eq_left, mul_eq_right]

private theorem words_subset (H : Subgroup TwistedModel) {x y : TwistedModel}
    (hz : z 0 ∈ H) (hx : x ∈ H) (hy : y ∈ H) :
    ∀ t ∈ words x y, t ∈ H := by
  intro t ht
  simp only [words, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact H.one_mem
  · exact hz
  · exact hx
  · exact hy
  · exact H.mul_mem hz hx
  · exact H.mul_mem hz hy
  · exact H.mul_mem hx hy
  · exact H.mul_mem (H.mul_mem hz hx) hy

private theorem generators (S : Subgroup TwistedModel) (hE : IsElementaryAbelian 2 S)
    (hcard : Nat.card S = 8) (hzS : z 0 ∈ S) :
    ∃ x ∈ S, ∃ y ∈ S,
      (∀ t, t ∈ S ↔ t ∈ words x y) ∧ S = closure {z 0, x, y} := by
  classical
  let := hE
  have hc : (S : Set TwistedModel).toFinset.card = 8 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨x, hxS, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({1, z 0} : Finset TwistedModel).card < (S : Set TwistedModel).toFinset.card from
      Finset.card_le_two.trans_lt (by omega))
  obtain ⟨y, hyS, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({1, z 0, x, z 0 * x} : Finset TwistedModel).card <
      (S : Set TwistedModel).toFinset.card from Finset.card_le_four.trans_lt (by omega))
  rw [Set.mem_toFinset] at hxS hyS
  have hz1 : z 0 ≠ 1 := by
    intro h
    simpa [h] using z_order 0
  have hzsq : z 0 * z 0 = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (z 0) hzS
  have hxsq : x * x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxS
  have hx' : x ≠ 1 ∧ x ≠ z 0 := by simpa using hx
  have hwordcard : (words x y).card = 8 :=
    words_card (z 0) x y hzsq hxsq (z_zero_mem_center.comm x).eq
      hz1 hx'.1 hx'.2 hy
  have hcover : words x y = (S : Set TwistedModel).toFinset :=
    Finset.eq_of_subset_of_card_le
      (fun t ht => Set.mem_toFinset.mpr (words_subset S hzS hxS hyS t ht))
      (by omega)
  refine ⟨x, hxS, y, hyS, (fun t => by rw [hcover]; exact Set.mem_toFinset.symm),
    le_antisymm ?_ ?_⟩
  · intro t ht
    apply words_subset (closure {z 0, x, y}) (x := x) (y := y)
      (subset_closure (by simp)) (subset_closure (by simp)) (subset_closure (by simp))
    rw [hcover]
    exact Set.mem_toFinset.mpr ht
  · exact (closure_le _).mpr (by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · exact hzS
      · exact hxS
      · exact hyS)

/-- Every self-centralizing elementary abelian subgroup of order eight in the
parity-twisted local model is conjugate to Janko's `H*`. -/
public theorem modelHstar_conjugacy
    (S : Subgroup TwistedModel) (hE : IsElementaryAbelian 2 S)
    (hcard : Nat.card S = 8) (hC : centralizer (S : Set TwistedModel) = S) :
    ∃ c : TwistedModel, S.map (MulAut.conj c).toMonoidHom = modelHstar := by
  classical
  let := hE
  have hzS : z 0 ∈ S := by
    rw [← hC]
    exact center_le_centralizer _ z_zero_mem_center
  obtain ⟨x, hxS, y, hyS, hwords, hgen⟩ := generators S hE hcard hzS
  have hx : x * x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) x hxS
  have hy : y * y = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) y hyS
  have hxy : x * y = y * x :=
    congrArg Subtype.val (mul_comm (⟨x, hxS⟩ : S) ⟨y, hyS⟩)
  have hconj (c : TwistedModel) (hcx : (MulAut.conj c) x ∈ modelHstar)
      (hcy : (MulAut.conj c) y ∈ modelHstar) :
      S.map (MulAut.conj c).toMonoidHom = modelHstar := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [map_le_iff_le_comap, hgen]
      apply (closure_le _).mpr
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl
      · change c * z 0 * c⁻¹ ∈ modelHstar
        rw [mem_center_iff.mp z_zero_mem_center c, mul_inv_cancel_right]
        exact modelHstar_generators.1
      · exact hcx
      · exact hcy
    · rw [card_map_of_injective (MulAut.conj c).injective, hcard, modelHstar_card]
  rcases pair_alternative ⟨x, hx⟩ ⟨y, hy⟩ hxy with hh | hh | ⟨i, hix, hiy, hi⟩
  · exact ⟨1, hconj 1 (by simpa using hh.1) (by simpa using hh.2)⟩
  · exact ⟨z 1, hconj (z 1) hh.1 hh.2⟩
  · exfalso
    apply hi
    apply (hwords _).mp
    rw [← hC, hgen, centralizer_closure]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · exact (z_zero_mem_center.comm _).eq
    · exact hix
    · exact hiy

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
