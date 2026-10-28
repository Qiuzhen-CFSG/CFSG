module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.Basic
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization

/-!
# Compatible diagonal matrices in the Ree fixed group

The simple-coroot word identities put every integral diagonal torus matrix
in the actual root-generated split group. The twist preserves the coroot
torus, so the image of such a matrix under the twist is again diagonal.
For compatible parameters, applying the twist to root-curve conjugation
at parameter one shows that the two diagonal matrices have the same root
characters. Root-curve injectivity and the diagonal character formula then
prove equality of the matrices themselves.

Thus the inverse diagonal matrix belongs to the supplied fixed group.
The inverse is required by the integral torus convention: basis weights
are negative and the root action is `T⁻¹ * x * T`. The proof works for every
`m`, including the binary endpoint, without simplicity or perfectness.

This supplies the fixed-torus realization used in GLS3, 2.4.7 and 2.5.1(b),
in `refs/KGroup/GLS3/chapter2.tex`. The coroot-word calculations are provided
by `ParabolicAmalgam/Geometry/CorootRealization.lean`; the unequal root powers
are exactly those of `LocalBlockInput.twist_root`.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open ReeF4.Parabolics

namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters
variable {m : ℕ}

private theorem rootGenerator_injective (r : F4Chevalley.Root) :
    Function.Injective (rootGeneratorInGroup m r) := by
  intro s t h
  apply rootElement_injective (P := typeF4RootPairing)
    (b := typeF4RootPairing_base) (k := CoefficientField m) r
  simp only [rootElement, rootMorphismFamily, rootMorphism_apply]
  congr 1
  change Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r s) =
    Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r t)
  exact congrArg Matrix.GeneralLinearGroup.toLin (congrArg Subtype.val h)

private theorem torus_conjugation (u : TorusParameters m)
    (h : SplitGroup m) (hh : h.val = torusMatrix u)
    (r : F4Chevalley.Root) (t : CoefficientField m) :
    h⁻¹ * rootGeneratorInGroup m r t * h =
      rootGeneratorInGroup m r ((rootScale u r : CoefficientField m) * t) := by
  apply Subtype.ext
  change h.val⁻¹ * F4Chevalley.rootCurve r t * h.val = _
  rw [hh]
  exact torusMatrix_conjugation u r t

/-- Every diagonal parameter matrix lies in the root-generated split carrier,
as witnessed by the actual simple-coroot words. -/
theorem torusMatrix_mem_splitGroup (u : TorusParameters m) :
    torusMatrix u ∈ SplitGroup m := by
  obtain ⟨h, _, hh⟩ := diagonalTorusHom_mem_splitTorus_map m u
  change h.val = torusMatrix u at hh
  exact hh ▸ h.property

/-- Root-character compatibility fixes the diagonal representative itself. -/
theorem twist_torusMatrix (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u)
    (h : SplitGroup m) (hh : h.val = torusMatrix u) :
    d.twist h = h := by
  have ht : h ∈ splitTorus m := by
    rw [splitTorus_eq_diagonalTorus]
    exact ⟨u, hh.symm⟩
  have htw : d.twist h ∈ splitTorus m := by
    rw [d.twist_eq_reeAutomorphism, ← splitTorus_invariant m]
    exact Subgroup.mem_map_of_mem _ ht
  rw [splitTorus_eq_diagonalTorus] at htw
  obtain ⟨v, hv⟩ := htw
  change torusMatrix v = (d.twist h).val at hv
  have hroot (r : F4Chevalley.Root) :
      rootScale v (exceptionalRootPermutation r) =
        rootScale u (exceptionalRootPermutation r) := by
    have he := congrArg d.twist (torus_conjugation u h hh r 1)
    simp only [map_mul, map_inv, d.twist_root, ← rootFieldEnd_apply, map_one] at he
    rw [torus_conjugation v (d.twist h) hv.symm, mul_one, mul_one,
      rootFieldEnd_apply, hu r] at he
    exact Units.ext (rootGenerator_injective (exceptionalRootPermutation r) he)
  apply Subtype.ext
  rw [← hv, hh]
  apply F4Chevalley.torusConjugation.character_compatibility v u |>.mpr
  intro r
  simpa only [rootScale, Equiv.apply_symm_apply] using
    hroot (exceptionalRootPermutation.symm r)

/-- The inverse diagonal matrix is an actual fixed-group element and hence
can serve as the inner representative for the torus action. -/
theorem exists_fixedGroup_torusMatrix_inv (d : LocalBlockInput m)
    (u : TorusParameters m) (hu : TwistCompatible u) :
    ∃ g : d.fixedGroup, g.val.val = (torusMatrix u)⁻¹ := by
  let h : SplitGroup m := ⟨torusMatrix u, torusMatrix_mem_splitGroup u⟩
  have hh : d.twist h = h := twist_torusMatrix d u hu h rfl
  refine ⟨⟨h⁻¹, ?_⟩, rfl⟩
  change d.twist h⁻¹ = h⁻¹
  rw [map_inv, hh]

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters
