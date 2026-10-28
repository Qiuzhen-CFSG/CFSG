module

public import Stellmacher.Recognition.LyonsU3Four.LocalFiveOrdinaryTable

/-!
# Ordinary restriction and section coefficients for the local group

The complete ordinary table restricts on odd-order elements to five linear
characters, with rows of types `e_j`, `1 - e_j`, and `1`. Their Gram matrix is
`4 * (3 + δ_jk)`. At a nonidentity central Sylow element the quartic rows
acquire the sign determined by their central kernel; the other rows keep
their coefficients. These identities concern actual ordinary characters.

The Gram computation becomes a principal Cartan computation only after
identifying the five linear functions with genuine simple Brauer characters
and establishing principal-block membership. Neither fact is asserted here.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 4, p. 381.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (α : FiveComplement →* MulAut S)

/-- The nonnegative coefficients of restriction to odd-order elements. -/
def localFiveDecompositionRow : LocalFiveRowIndex S → FiveLinearIndex → ℕ :=
  Sum.elim (fun χ j => if χ = j then 1 else 0)
    (Sum.elim (fun p j => if p.2 = j then 0 else 1) (fun _ _ => 1))

variable {S α}
/-- These coefficients express the actual ordinary values on odd-order elements. -/
theorem LocalFiveCharacterTable.odd_expansion (T : LocalFiveCharacterTable S α)
    (i : LocalFiveRowIndex S) (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) :
    T.row i (ConjClasses.mk u) =
      ∑ j : FiveLinearIndex, (localFiveDecompositionRow S i j : ℂ) * j u.right := by
  rcases i with χ | (⟨z, χ⟩ | i)
  · simp [localFiveDecompositionRow, T.linear_value]
  · rw [T.quartic_odd_value z χ u hu]
    have hs : (∑ j : FiveLinearIndex,
        (localFiveDecompositionRow S (.inr (.inl (z, χ))) j : ℂ) * j u.right) =
        ∑ j ∈ Finset.univ.erase χ, j u.right := by
      simp only [localFiveDecompositionRow, Sum.elim_inr, Sum.elim_inl,
        Nat.cast_ite, Nat.cast_zero, Nat.cast_one, ite_mul, zero_mul, one_mul,
        Finset.sum_ite, Finset.sum_const_zero, zero_add]
      rw [Finset.filter_ne]
    rw [hs, fiveLinear_sum_erase]
    simp only [localFive_odd_right_eq_one_iff S α u hu]
  · rw [T.quintic_odd_value i u hu]
    simp only [localFiveDecompositionRow, Sum.elim_inr, Nat.cast_one, one_mul]
    rw [AbelianLinearCharacters.sum_apply, localFive_odd_right_eq_one_iff S α u hu]
    simp

variable (S)
/-- The ordinary restriction coefficient matrix has diagonal 16 and off-diagonal 12. -/
theorem localFiveDecompositionRow_gram (h : SylowStructure S) (j k : FiveLinearIndex) :
    ∑ i : LocalFiveRowIndex S, localFiveDecompositionRow S i j * localFiveDecompositionRow S i k =
      4 * (3 + if j = k then 1 else 0) := by
  have hc : Fintype.card FiveLinearIndex = 5 := by
    rw [← Nat.card_eq_fintype_card, fiveLinearIndex_card]
  have hz : Fintype.card (QuarticCentralIndex S) = 3 := by
    rw [← Nat.card_eq_fintype_card, quarticCentralIndex_card S h]
  have hlin : (∑ χ : FiveLinearIndex,
      (if χ = j then 1 else 0) * (if χ = k then 1 else 0) : ℕ) =
      if j = k then 1 else 0 := by simp [eq_comm]
  have hquart : (∑ χ : FiveLinearIndex,
      (if χ = j then 0 else 1) * (if χ = k then 0 else 1) : ℕ) =
      if j = k then 4 else 3 := by
    by_cases he : j = k
    · subst k
      have hs : (∑ χ : FiveLinearIndex,
          (if χ = j then 0 else 1) * (if χ = j then 0 else 1) : ℕ) =
          ∑ χ : FiveLinearIndex, if χ ≠ j then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro χ _
        by_cases hh : χ = j <;> simp [hh]
      rw [hs]
      rw [Finset.sum_boole, Nat.cast_id, Finset.filter_ne',
        Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, hc]
      norm_num
    · have hcount : (Finset.univ.filter (fun χ : FiveLinearIndex => χ ≠ j ∧ χ ≠ k)).card = 3 := by
        have hset : Finset.univ.filter (fun χ : FiveLinearIndex => χ ≠ j ∧ χ ≠ k) =
            (Finset.univ.erase j).erase k := by ext χ; simp [and_comm]
        rw [hset, Finset.card_erase_of_mem (by simp [Ne.symm he]),
          Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, hc]
      calc
        _ = ∑ χ : FiveLinearIndex, if χ ≠ j ∧ χ ≠ k then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro χ _
          by_cases hj : χ = j <;> by_cases hk : χ = k <;> simp [hj, hk]
        _ = 3 := by simp only [Finset.sum_boole, Nat.cast_id, hcount]
        _ = _ := by simp [he]
  simp only [localFiveDecompositionRow, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fintype.sum_prod_type, hlin, hquart,
    Finset.sum_const, Finset.card_univ, hz, Fintype.card_fin, nsmul_eq_mul, mul_one]
  split_ifs <;> norm_num

/-- The signed section coefficients at a nonidentity central Sylow element. -/
def localFiveSectionRow (w : QuarticCentralIndex S) :
    LocalFiveRowIndex S → FiveLinearIndex → ℤ :=
  Sum.elim (fun χ j => if χ = j then 1 else 0)
    (Sum.elim (fun p j => (if p.1 = w then 1 else -1) *
      (if p.2 = j then 0 else 1)) (fun _ _ => 1))

variable {S}
/-- The coefficients give the actual values throughout the central section. -/
theorem LocalFiveCharacterTable.section_expansion (T : LocalFiveCharacterTable S α)
    (h : SylowStructure S) (w : QuarticCentralIndex S) (i : LocalFiveRowIndex S)
    (u : LocalFiveGroup S α) (hu : Odd (orderOf u)) :
    T.row i (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u)) =
      ∑ j : FiveLinearIndex, (localFiveSectionRow S w i j : ℂ) * j u.right := by
  rcases i with χ | (⟨z, χ⟩ | i)
  · simp [localFiveSectionRow, T.linear_value]
  · have he : T.row (.inr (.inl (z, χ)))
        (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u)) =
        quarticCentralSign z w * T.row (.inr (.inl (z, χ))) (ConjClasses.mk u) := by
      change χ (SemidirectProduct.inl w.1.1 * u : LocalFiveGroup S α).right *
        T.quartic z (ConjClasses.mk (SemidirectProduct.inl w.1.1 * u)) =
        quarticCentralSign z w * (χ u.right * T.quartic z (ConjClasses.mk u))
      rw [(T.extension_spec z).central_mul]
      simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
      ring
    rw [he, T.odd_expansion _ u hu, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hzw : z = w <;> by_cases hχj : χ = j <;>
      simp [localFiveSectionRow, localFiveDecompositionRow, quarticCentralSign, hzw, hχj]
  · rw [T.quintic_section h i w.1 u hu]
    simp [localFiveSectionRow]
end
end Stellmacher.Recognition.LyonsU3Four
