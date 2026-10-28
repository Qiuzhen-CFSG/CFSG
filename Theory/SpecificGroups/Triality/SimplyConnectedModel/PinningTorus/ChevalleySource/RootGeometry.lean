module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.ChevalleySource.Weyl
public import Theory.AlgebraicGroup.RootData.Chevalley

/-!
# The mixed-root terms in the actual D4 pinning

The symmetric D4 pairing gives a strict square bound for independent roots.
Pairing a proposed positive mixed root with the two input coroots forces both
coefficients to be one. Base reflection induction and the connected D4 Cartan
matrix also show that the canonical root-form lengths are equal. These facts
exclude every exceptional Chevalley coefficient in the concrete source system.

Source: GLS3 1.12.1(b), in the simply laced D4 case.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.SimplyConnected.Pinning.ChevalleySource
public noncomputable section

private theorem pairing_symmetric (r s : RootIndex) : (typeDRootPairing 2).pairing r s = (typeDRootPairing 2).pairing s r := by
  simp only [typeDRootPairing_pairing]
  exact dot_comm _ _

private theorem simple_length (i : Fin 4) :
    RootSquaredLength (typeDRootPairing 2) (simpleRoot i) = RootSquaredLength (typeDRootPairing 2) (simpleRoot 1) := by
  classical
  let := Fintype.ofFinite RootIndex
  have h := (typeDRootPairing 2).toInvariantForm.pairing_mul_eq_pairing_mul_swap (simpleRoot i) (simpleRoot 1)
  change (typeDRootPairing 2).pairing (simpleRoot 1) (simpleRoot i) * RootSquaredLength (typeDRootPairing 2) (simpleRoot i) =
    (typeDRootPairing 2).pairing (simpleRoot i) (simpleRoot 1) * RootSquaredLength (typeDRootPairing 2) (simpleRoot 1) at h
  have hp (i j : Fin 4) : (typeDRootPairing 2).pairing (simpleRoot i) (simpleRoot j) =
      (typeDCartanMatrix 2 i j : ℝ) := by
    exact typeDRootPairing_simpleIndex_pairing 2 i j
  simp only [hp] at h
  fin_cases i
  · norm_num [typeDCartanMatrix, Fin.ext_iff, Fin.val_last] at h ⊢
    exact h
  · rfl
  · norm_num [typeDCartanMatrix, Fin.ext_iff, Fin.val_last] at h ⊢
    exact h
  · norm_num [typeDCartanMatrix, Fin.ext_iff, Fin.val_last] at h ⊢
    exact h

theorem root_squaredLength_equal (r s : RootIndex) : RootSquaredLength (typeDRootPairing 2) r = RootSquaredLength (typeDRootPairing 2) s := by
  classical
  let := Fintype.ofFinite RootIndex
  have hall (r : RootIndex) : RootSquaredLength (typeDRootPairing 2) r = RootSquaredLength (typeDRootPairing 2) (simpleRoot 1) := by
    apply (typeDRootPairing_base 2).induction_reflect r
    · intro a ha
      simpa only [RootSquaredLength, (typeDRootPairing 2).root_reflectionPerm, (typeDRootPairing 2).rootForm_reflection_reflection_apply] using ha
    · intro a ha
      obtain ⟨i,hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨a,ha⟩
      have hie : simpleRoot i = a := congrArg Subtype.val hi
      rw [← hie]
      exact simple_length i
    · intro a b ha hb
      simpa only [RootSquaredLength, (typeDRootPairing 2).root_reflectionPerm, (typeDRootPairing 2).rootForm_reflection_reflection_apply] using ha
  exact (hall r).trans (hall s).symm

/-- Positive mixed roots in D4 can only have the two coefficients one. -/
theorem mixed_root_coefficients (r s t : RootIndex) (i j : ℕ) (hi : 0 < i) (hj : 0 < j)
    (hli : LinearIndependent ℝ ![(typeDRootPairing 2).root r, (typeDRootPairing 2).root s])
    (hroot : (typeDRootPairing 2).root t = (i:ℝ) • (typeDRootPairing 2).root r + (j:ℝ) • (typeDRootPairing 2).root s) : i = 1 ∧ j = 1 := by
  have hsym : (typeDRootPairing 2).pairingIn ℤ r s = (typeDRootPairing 2).pairingIn ℤ s r := by
    apply Int.cast_injective (α := ℝ)
    change algebraMap ℤ ℝ _ = algebraMap ℤ ℝ _
    simpa only [(typeDRootPairing 2).algebraMap_pairingIn] using pairing_symmetric r s
  have hsq := (typeDRootPairing 2).coxeterWeightIn_le_four ℤ r s
  have hne := ((typeDRootPairing 2).linearIndependent_iff_coxeterWeightIn_ne_four ℤ).mp hli
  rw [RootPairing.coxeterWeightIn, ← hsym] at hsq hne
  have hlt : (typeDRootPairing 2).pairingIn ℤ r s * (typeDRootPairing 2).pairingIn ℤ r s < 4 := lt_of_le_of_ne hsq hne
  have hint : (-1:ℤ) ≤ (typeDRootPairing 2).pairingIn ℤ r s := by nlinarith
  have hbound : (-1:ℝ) ≤ (typeDRootPairing 2).pairing r s := by
    rw [← (typeDRootPairing 2).algebraMap_pairingIn ℤ]
    change (-1:ℝ) ≤ ((typeDRootPairing 2).pairingIn ℤ r s : ℝ)
    exact_mod_cast hint
  have hpair (q : RootIndex) : (typeDRootPairing 2).pairing t q =
      (i:ℝ) * (typeDRootPairing 2).pairing r q + (j:ℝ) * (typeDRootPairing 2).pairing s q := by
    have h := congrArg ((typeDRootPairing 2).coroot' q) hroot
    simpa only [map_add, map_smul, smul_eq_mul, RootPairing.root_coroot'_eq_pairing] using h
  have h1 := hpair r
  have h2 := hpair s
  have h3 := hpair t
  rw [(typeDRootPairing 2).pairing_same] at h1 h2 h3
  rw [pairing_symmetric s r] at h1
  rw [pairing_symmetric r t, pairing_symmetric s t, h1, h2] at h3
  have hi' : (1:ℝ) ≤ i := by exact_mod_cast hi
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hp : 0 ≤ (i:ℝ) * j * ((typeDRootPairing 2).pairing r s + 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hij : (i:ℝ) * j ≤ 1 := by nlinarith [sq_nonneg ((i:ℝ)-j)]
  have hi1 : (i:ℝ) = 1 := by nlinarith
  have hj1 : (j:ℝ) = 1 := by nlinarith
  exact ⟨by exact_mod_cast hi1, by exact_mod_cast hj1⟩
end
end Triality.SimplyConnected.Pinning.ChevalleySource
