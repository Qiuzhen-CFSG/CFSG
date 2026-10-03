module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveSectionFunctions

/-!
# Root support of the genuine local section columns

Ordinary column orthogonality separates an element outside the cyclic roots of
`w` from every `w * u`, for `u` in the order-five complement. The actual signed
section expansion and Fourier uniqueness on that complement force each local
column to vanish. No block projection or ambient induction identity is assumed.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), p. 381,
Brauer's transfer argument preceding Lemma 4.
-/

public section
open scoped BigOperators
open Subgroup
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
attribute [local instance] Fintype.ofFinite
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    {α : FiveComplement →* MulAut S}

private theorem column_sum {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℤ) (b : I → ℂ) (v : J → ℂ) :
    (∑ j, (∑ i, (a i j : ℂ) * b i) * star (v j)) =
      ∑ i, b i * star (∑ j, (a i j : ℂ) * v j) := by
  simp only [star_sum, star_mul, star_intCast, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem five_fourier_zero (a : FiveLinearIndex → ℂ)
    (ha : ∀ v : FiveComplement, ∑ k, a k * star (k v) = 0) (j : FiveLinearIndex) :
    a j = 0 := by
  classical
  let : Fintype FiveComplement := Fintype.ofFinite _
  calc
    a j = ∑ k : FiveLinearIndex, a k * scalarProduct FiveComplement
        (j : FiveComplement → ℂ) (k : FiveComplement → ℂ) := by
      simp only [AbelianLinearCharacters.orthogonal, mul_ite, mul_one, mul_zero]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = (Nat.card FiveComplement : ℂ)⁻¹ * ∑ v : FiveComplement,
        j v * (∑ k : FiveLinearIndex, a k * star (k v)) := by
      simp only [scalarProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = 0 := by simp only [ha, mul_zero, Finset.sum_const_zero]

/-- The complement fixes the embedded central Sylow involutions. -/
theorem localFive_inl_mem_center (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (w : QuarticCentralIndex S) :
    SemidirectProduct.inl (φ := α) w.1.1 ∈ center (LocalFiveGroup S α) := by
  rw [mem_center_iff]
  intro x
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    rw [localFive_action_fixes_center h β hβ α hα x.right w.1]
    exact (mem_center_iff.mp w.1.property) x.left
  · simp


/-- A genuine signed section column vanishes away from cyclic roots of its central involution. -/
theorem LocalFiveCharacterTable.sectionClassFunction_eq_zero_of_not_root (T : LocalFiveCharacterTable S α)
    (h : SylowStructure S) (β : MulAut S) (hβ : orderOf β = 15)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ))
    (w : QuarticCentralIndex S) (j : FiveLinearIndex)
    (x : LocalFiveGroup S α)
    (hx : SemidirectProduct.inl w.1.1 ∉ zpowers x) :
    T.sectionClassFunction w j x = 0 := by
  classical
  let : Fintype (QuarticCentralIndex S) := Fintype.ofFinite _
  let z : LocalFiveGroup S α := SemidirectProduct.inl w.1.1
  have hz : z ∈ center (LocalFiveGroup S α) :=
    localFive_inl_mem_center h β hβ hα w
  have hz2 : z ^ 2 = 1 := by
    let _ := h.center_elementary
    change (SemidirectProduct.inl w.1.1 : LocalFiveGroup S α) ^ 2 = 1
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian (p := 2)
      w.1.1 w.1.property, map_one]
  have hs (v : FiveComplement) :
      ∑ k : FiveLinearIndex, T.sectionClassFunction w k x * star (k v) = 0 := by
    let u : LocalFiveGroup S α := SemidirectProduct.inr v
    have huv : u ^ 5 = 1 := by
      rw [show u = SemidirectProduct.inr v from rfl, ← map_pow]
      have hv : v ^ 5 = 1 := by
        have hv := pow_card_eq_one' (x := v)
        simpa [FiveComplement, Nat.card_eq_fintype_card] using hv
      rw [hv, map_one]
    have hu : Odd (orderOf u) := (by decide : Odd 5).of_dvd_nat
      (orderOf_dvd_of_pow_eq_one huv)
    have hcomm : Commute z u := (mem_center_iff.mp hz u).symm
    have hpow : (z * u) ^ 5 = z := by
      rw [hcomm.mul_pow, huv, mul_one]
      calc
        z ^ 5 = (z ^ 2) ^ 2 * z := by simp only [← pow_mul, ← pow_succ]
        _ = z := by rw [hz2]; simp
    have hne : ConjClasses.mk x ≠ ConjClasses.mk (z * u) := by
      intro he
      obtain ⟨g, hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)
      have hp : g * x ^ 5 * g⁻¹ = z := by
        change (MulAut.conj g) (x ^ 5) = z
        rw [map_pow, MulAut.conj_apply, hg, hpow]
      have hxp : x ^ 5 = z := by
        calc
          x ^ 5 = g⁻¹ * (g * x ^ 5 * g⁻¹) * g := by group
          _ = g⁻¹ * z * g := by rw [hp]
          _ = z := by rw [mem_center_iff.mp hz g⁻¹]; simp [mul_assoc]
      apply hx
      change z ∈ zpowers x
      rw [← hxp]
      exact pow_mem (mem_zpowers x) 5
    have hcomplete : IsCompleteIrreducibleCharacterFamily T.row :=
      ⟨T.row_complete.1, T.row_complete.2.1, T.row_complete.2.2⟩
    obtain ⟨B, hB⟩ := completeFamily_form_basis hcomplete
    have ho : ∑ r : LocalFiveRowIndex S,
        T.row r (ConjClasses.mk x) * star (T.row r (ConjClasses.mk (z * u))) = 0 := by
      rw [basis_sum_character_projection hcomplete B hB]
      exact classProjection_apply_ne hne
    simp only [T.sectionClassFunction_apply]
    rw [column_sum (localFiveSectionRow S w)
      (fun r => T.row r (ConjClasses.mk x)) (fun k : FiveLinearIndex => k v)]
    convert ho using 1
    apply Finset.sum_congr rfl
    intro r _
    rw [T.section_expansion h w r u hu]
    rfl
  exact five_fourier_zero (fun k => T.sectionClassFunction w k x) hs j

end Stellmacher.Recognition.LyonsU3Four
