module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.Contracts
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization.Layout

/-!
# Binary markers in the literal Ree root coordinates

The Parrott marker s₁ is the square of the first B₂ quartet word. The
fixed-coordinate factorization and type-V product law identify that square
with `centralWord 0 0 1`. The marker s₄ is exactly `rootWord 0 3 1`.
Entrywise coefficient transport preserves both parameter-one words for
every binary-field embedding.

Source: Parrott (1972), §5, p.683; GLS3, Table 2.4, types V and VI;
Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8, p.57.
-/

public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization
open ReeF4.NormalizedRootCentralizers.CenterExponent
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Parabolics Parabolics.RadicalCoordinates.FixedCoordinates
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open DerivedTits.Realization Tits.InvolutionRootGeometry

private theorem root_zero (m : ℕ) (r : F4Chevalley.Root) :
    rootGeneratorInGroup m r 0 = 1 := Subtype.ext (F4Chevalley.rootCurve_zero r)

private theorem root_sq (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    rootGeneratorInGroup m r t ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change F4Chevalley.rootCurve r t * F4Chevalley.rootCurve r t = 1
  rw [← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero, F4Chevalley.rootCurve_zero]

private theorem central_zero_sq (m : ℕ) (t : CoefficientField m) :
    centralWord m 0 t ^ 2 = 1 := by
  have hc := positiveRootWordLayout.quartet_top_commute m (mixedRootCommutation m) (0 : Fin 4)
    t (rootFieldEnd m (longRoot 0) t)
  rw [positive_quartet_indices] at hc
  change Commute (rootGeneratorInGroup m (highRoot 0) t)
    (rootGeneratorInGroup m (mixedRoot 0) (rootFieldEnd m (longRoot 0) t)) at hc
  rw [centralWord, hc.mul_pow, root_sq, root_sq, one_mul]

private theorem root_zero_one_sq : rootWord 0 0 1 ^ 2 = centralWord 0 0 1 := by
  simpa [pow_two, CharTwo.add_self_eq_zero, rootWord, root_zero] using
    mainParameterProduct 0 0 (by decide) 1

theorem quartet_zero_sq : quartetElement 0 ^ 2 = centralWord 0 0 1 := by
  have hf := positiveRootWordLayout.quartet_factorization 0 (mixedRootCommutation 0) (0 : Fin 4) 1 0
  rw [positive_layout_blocks, positive_quartet_indices] at hf
  change quartetElement 0 = rootWord 0 0 1 * centralWord 0 0 (titsEnd 0 0 + 1 * titsEnd 0 1) at hf
  simp only [map_zero, map_one, one_mul, zero_add] at hf
  rw [hf, ← root_zero_one_sq]
  have h4 : rootWord 0 0 1 ^ 4 = 1 := by
    change (rootWord 0 0 1) ^ (2 * 2) = 1
    rw [pow_mul, root_zero_one_sq, central_zero_sq]
  calc
    _ = rootWord 0 0 1 ^ 6 := by group
    _ = rootWord 0 0 1 ^ 4 * rootWord 0 0 1 ^ 2 := by rw [← pow_add]
    _ = _ := by rw [h4, one_mul]

theorem binary_long_matrix (m : ℕ) (e : CoefficientField 0 →+* CoefficientField m) :
    toSplitGroup m (Subfield.reeMap (by simp) e (fixedGenerator .s1)) =
      centralWord m 0 1 := by
  rw [Subfield.toSplitGroup_reeMap]
  have hm : toSplitGroup 0 (fixedGenerator .s1) = quartetElement 0 ^ 2 := by
    simpa only [Tits.InvolutionRootGeometry.longRoot, derivedEquiv_coe,
      embedding_generator] using longRoot_matrix
  rw [hm, quartet_zero_sq]
  simp [centralWord]

theorem binary_short_matrix (m : ℕ) (e : CoefficientField 0 →+* CoefficientField m) :
    toSplitGroup m (Subfield.reeMap (by simp) e (fixedGenerator .s4)) =
      rootWord m 3 1 := by
  rw [Subfield.toSplitGroup_reeMap]
  have hm : toSplitGroup 0 (fixedGenerator .s4) = pairElement 3 := by
    simpa only [Tits.InvolutionRootGeometry.shortRoot, derivedEquiv_coe,
      embedding_generator] using shortRoot_matrix
  rw [hm, pairElement_eq]
  have hl := positiveRootWordLayout.pair_long (3 : Fin 4)
  have hs := positiveRootWordLayout.pair_short (3 : Fin 4)
  rw [positive_layout_blocks, positive_pair_indices] at hl hs
  change DerivedTits.Realization.pairRoots 3 0 = longRoot 3 at hl
  change DerivedTits.Realization.pairRoots 3 1 = shortRoot 3 at hs
  simp [hl, hs, rootWord]

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.Normalization
