module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.Contracts
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization.Marking
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization.WeylTransport
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization.ParameterScaling

/-!
# Binary normalization of both actual Ree involution curves

The marked s₁ maps to the first block's central parameter one. Two relative
Weyl rotations carry it to the fifth block, where the fixed end-node torus
scales by any prescribed nonzero parameter. The marked s₄ already maps to
the fourth curve. That curve is a fixed Weyl conjugate of the paired end
curve, whose middle-node torus character is the inverse square. Squaring is
bijective in the finite coefficient field of characteristic two.

All conjugators are elements of the literal exceptional-twist fixed group,
and the binary transport is the published `Subfield.reeMap` for each given
coefficient embedding. No involution-exhaustion premise is used.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
p.57; Parrott (1972), §5, p.683; GLS3, Table 2.4 and §2.4.
-/

public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
open EvenInvolutionGeometry Normalization
open Parabolics.OuterLocal.SuzukiCommutators
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

private theorem short_parameter_conjugate (m : ℕ) (a : CoefficientField m) (ha : a ≠ 0) :
    IsConj (shortRootElement m 1) (shortRootElement m a) := by
  obtain ⟨h, hh⟩ := end_parameter_conjugator m a ha
  refine isConj_iff.mpr ⟨shortWeyl m * h * (shortWeyl m)⁻¹, ?_⟩
  apply toSplitGroup_injective m
  simp only [map_mul, map_inv, shortRootElement_coe]
  rw [← shortWeyl_conjugate m 1, ← shortWeyl_conjugate m a]
  calc
    _ = toSplitGroup m (shortWeyl m) *
        (toSplitGroup m h * endRootWord m 1 * (toSplitGroup m h)⁻¹) *
        (toSplitGroup m (shortWeyl m))⁻¹ := by group
    _ = _ := by rw [hh]

/-- Both nonzero root curves are conjugate to their literal binary Tits
markers, for every coefficient embedding. -/
theorem binaryRootNormalization (m : ℕ) (_hm : 1 ≤ m) : BinaryRootNormalization m := by
  intro e a ha
  constructor
  · have h1 : IsConj (Subfield.reeMap (by simp) e
        (Tits.InvolutionRootGeometry.fixedGenerator .s1)) (longRootElement m 1) := by
      refine isConj_iff.mpr ⟨longWeyl m, ?_⟩
      apply toSplitGroup_injective m
      simpa only [map_mul, map_inv, binary_long_matrix, longRootElement_coe] using
        longWeyl_conjugate m 1
    exact h1.trans (long_parameter_conjugate m a ha)
  · have h1 : Subfield.reeMap (by simp) e (Tits.InvolutionRootGeometry.fixedGenerator .s4) =
        shortRootElement m 1 := by
      apply toSplitGroup_injective m
      rw [binary_short_matrix, shortRootElement_coe]
    rw [h1]
    exact short_parameter_conjugate m a ha

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
