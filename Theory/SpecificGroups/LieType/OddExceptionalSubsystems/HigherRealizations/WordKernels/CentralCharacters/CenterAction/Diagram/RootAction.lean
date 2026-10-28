module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Diagram.Words

/-!
# The E6 opposition word on the ambient E7 and E8 roots

The published opposition word sends each of the six marked simple roots to
the negative of its pinned diagram image, in both ambient root systems.
Evaluation of integral coefficients as a sum of marked roots commutes with
each simple reflection because the restricted Cartan matrix is E6. Induction
on the word then transports `oppositionWord_coefficients` to the actual root
permutation, with the rightmost listed reflection acting first.

These are the root-action inputs for the ambient signed-operator comparison;
the operator signs and kernel assembly are separate results.

Sources: GLS3 Remark 1.8.9 (E6 opposition), §1.12 (reflection action of Tits
lifts), and §2.5 (pinned diagram action), for the exceptional inclusions in
Aschbacher–Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

public section
noncomputable section

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped BigOperators

variable {ι R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}

private theorem reflectCoefficients_eq_sub_single (k : Fin 6) (c : Fin 6 → ℤ) :
    reflectCoefficients k c = c - Pi.single k (∑ i, c i * typeE6CartanMatrix i k) := by
  ext i
  by_cases h : i = k
  · subst i
    simp [reflectCoefficients]
  · simp [reflectCoefficients, h]

private theorem reflection_rootCombination (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (k : Fin 6) (c : Fin 6 → ℤ) :
    P.reflection (j k) (∑ i, c i • P.root (j i)) =
      ∑ i, reflectCoefficients k c i • P.root (j i) := by
  rw [map_sum, reflectCoefficients_eq_sub_single]
  simp only [map_zsmul, RootPairing.reflection_apply_root' ℤ, hj, smul_sub,
    smul_smul, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_smul]
  simp [Pi.single_apply, ite_smul]

/-- Coefficient reflection calculations evaluate in the ambient root space. -/
theorem reflectionWord_root_eq_wordCoefficients (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (w : List (Fin 6)) (a : ι) (c : Fin 6 → ℤ)
    (hc : P.root a = ∑ i, c i • P.root (j i)) :
    P.root (reflectionWord (w.map j) a) =
      ∑ i, wordCoefficients w c i • P.root (j i) := by
  induction w with
  | nil => exact hc
  | cons k w ih =>
      rw [List.map_cons, reflectionWord, P.root_reflectionPerm, ih]
      exact reflection_rootCombination j hj k (wordCoefficients w c)

/-- An E6 Cartan restriction transports the opposition certificate to roots. -/
theorem oppositionWord_root_of_pairing (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (i : Fin 6) :
    reflectionWord (oppositionWord.map j) (j i : ι) =
      P.reflectionPerm (j (typeE6DiagramPermutation i)) (j (typeE6DiagramPermutation i)) := by
  apply P.root.injective
  rw [P.root_reflectionPerm, P.reflection_apply_self]
  calc
    _ = ∑ k, wordCoefficients oppositionWord (Pi.single i 1) k • P.root (j k) :=
      reflectionWord_root_eq_wordCoefficients j hj oppositionWord (j i) (Pi.single i 1)
        (by simp [Pi.single_apply, ite_smul])
    _ = -P.root (j (typeE6DiagramPermutation i)) := by
      rw [oppositionWord_coefficients]
      simp [Pi.single_apply, ite_smul]

/-- The published E6 word acts as minus the pinned diagram in E7. -/
theorem e7_oppositionWord_root (i : Fin 6) :
    reflectionWord (P := typeE7RootPairing) (oppositionWord.map e7Node)
        (e7Node i : typeE7Roots) =
      typeE7RootPairing.reflectionPerm (e7Node (typeE6DiagramPermutation i))
        (e7Node (typeE6DiagramPermutation i)) := by
  apply oppositionWord_root_of_pairing e7Node _ i
  intro a k
  exact (typeE7RootPairing_base_cartan_apply _ _).trans (e7_cartan_restrict a k)

/-- The published E6 word acts as minus the pinned diagram in E8. -/
theorem e8_oppositionWord_root (i : Fin 6) :
    reflectionWord (P := typeE8RootPairing) (oppositionWord.map e8Node)
        (e8Node i : typeE8Roots) =
      typeE8RootPairing.reflectionPerm (e8Node (typeE6DiagramPermutation i))
        (e8Node (typeE6DiagramPermutation i)) := by
  apply oppositionWord_root_of_pairing e8Node _ i
  intro a k
  exact (typeE8RootPairing_base_cartan_apply _ _).trans (e8_cartan_restrict a k)

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
