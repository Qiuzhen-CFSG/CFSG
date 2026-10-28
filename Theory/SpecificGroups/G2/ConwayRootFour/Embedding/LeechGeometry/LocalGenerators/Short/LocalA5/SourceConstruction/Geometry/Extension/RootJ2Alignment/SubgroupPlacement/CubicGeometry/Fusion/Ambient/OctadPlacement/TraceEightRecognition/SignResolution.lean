module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightRecognition.Reduction

/-!
# Golay coboundaries for the marked octad permutation

On the Golay code, the image of `1 + p` is exactly the subspace of
p-invariant words vanishing on its fixed octad, for the permutation p of
`normalGenerationMonomial`. Four explicit coefficients give a preimage.
The identity expressing the error through the fixed-coordinate values and
one invariance equation is checked on the twelve Golay basis vectors.

The consumer in `Monomial` turns this preimage into an integral sign
conjugator. Source context: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5
and 49.3–49.4. This is a new calculation on the existing attributed ATLAS
Golay coordinates, not an assumed class-fusion statement.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

namespace TraceEightSigns

private def wordCoordinates (w : Fin 24 → Bit) : BinaryWord :=
  fun p => w (finProdFinEquiv (hexIndexEquiv p.1, p.2))

private def resolution (c : golay) : golay :=
  c.val ((1,0),3) • golayBasis 1 + c.val ((2,0),3) • golayBasis 2 +
  c.val ((0,1),3) • golayBasis 3 +
  (c.val ((2,0),1) + c.val ((2,0),3)) • golayBasis 11

private def resolutionMap : golay →ₗ[Bit] golay where
  toFun := resolution
  map_add' c d := by
    simp only [resolution, Submodule.coe_add, Pi.add_apply, add_smul]
    abel
  map_smul' r c := by
    simp only [resolution, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      ← mul_add, smul_add, smul_smul]
    rfl

private def difference : golay →ₗ[Bit] golay :=
  LinearMap.id + (golayPermutationEquiv normalGenerationMonomial.right).toLinearMap

private def obstruction (c : golay) : BinaryWord :=
  c.val ((1,1),0) • wordCoordinates ![1,0,1,1,0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,0,0,0,1] +
  c.val ((1,1),1) • wordCoordinates ![1,1,1,0,0,0,1,0,0,1,0,0,0,1,0,0,0,0,1,0,0,0,0,1] +
  c.val ((1,1),3) • wordCoordinates ![1,1,1,0,0,1,0,0,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,1] +
  c.val ((2,1),1) • wordCoordinates ![1,0,1,0,1,1,0,0,0,1,1,0,0,0,0,0,0,0,0,0,0,1,0,1] +
  (c.val ((0,0),0) + c.val ((0,0),2)) • wordCoordinates ![1,0,0,1,1,1,0,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,0,0] +
  c.val ((1,1),2) • wordCoordinates ![0,1,0,0,0,1,0,0,1,1,1,0,0,0,1,0,0,0,1,0,0,0,0,1] +
  c.val ((2,1),0) • wordCoordinates ![0,1,0,1,0,1,1,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,0,1] +
  c.val ((2,1),2) • wordCoordinates ![0,0,0,0,1,0,1,0,0,1,1,0,0,0,0,0,1,0,1,0,0,0,1,1]

private def obstructionMap : golay →ₗ[Bit] BinaryWord where
  toFun := obstruction
  map_add' c d := by
    simp only [obstruction, Submodule.coe_add, Pi.add_apply, add_smul]
    abel
  map_smul' r c := by
    simp only [obstruction, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      ← mul_add, smul_add, smul_smul]
    rfl

private theorem difference_val (c : golay) :
    (difference c).val = c.val +
      coordinatePermutation normalGenerationMonomial.right.val c.val := rfl

private theorem resolution_val (c : golay) :
    (resolutionMap c).val =
      c.val ((1,0),3) • golayGenerators 1 + c.val ((2,0),3) • golayGenerators 2 +
      c.val ((0,1),3) • golayGenerators 3 +
      (c.val ((2,0),1) + c.val ((2,0),3)) • golayGenerators 11 := by
  simp only [resolutionMap, LinearMap.coe_mk, AddHom.coe_mk, resolution,
    Submodule.coe_add, Submodule.coe_smul, golayBasis_coe]

private theorem resolving_identity :
    golay.subtype.comp (difference.comp resolutionMap) + obstructionMap = golay.subtype := by
  apply golayBasis.ext
  intro i
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    difference_val, resolution_val, golayBasis_coe]
  change _ + obstruction (golayBasis i) = _
  simp only [obstruction, golayBasis_coe]
  revert i
  decide +kernel

/-- A Golay sign fixed by the marked permutation and zero on its fixed octad
is a coboundary. The displayed linear identity is checked on the Golay basis. -/
theorem fixed_zero_sign_eq_coboundary (c : golay)
    (hinv : ∀ i, c.val (normalGenerationMonomial.right.val.symm i) = c.val i)
    (hfix : ∀ i, normalGenerationMonomial.right.val.symm i = i → c.val i = 0) :
    ∃ b : golay, ∀ i,
      b.val i + b.val (normalGenerationMonomial.right.val.symm i) = c.val i := by
  have hz (k : Fin 4) : c.val ((1,1),k) = 0 := hfix _ (by rfl)
  have hz' (k : Fin 4) : c.val ((2,1),k) = 0 := hfix _ (by rfl)
  have hd : c.val ((0,0),0) + c.val ((0,0),2) = 0 := by
    have h := hinv ((0,0),0)
    change c.val ((0,0),2) = c.val ((0,0),0) at h
    rw [h]
    exact CharTwo.add_self_eq_zero _
  have ho : obstructionMap c = 0 := by
    change obstruction c = 0
    simp only [obstruction, hz, hz', hd, zero_smul, add_zero]
  have h := DFunLike.congr_fun resolving_identity c
  change (difference (resolutionMap c)).val + obstructionMap c = c.val at h
  rw [ho, add_zero] at h
  exact ⟨resolutionMap c, fun i => congrFun h i⟩

end TraceEightSigns



end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
