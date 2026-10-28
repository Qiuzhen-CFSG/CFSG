module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.LocalData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.LiftMatrices

/-!
# A fixed-free cubic in the actual projective icosian model

The fourth power of the concrete ATLAS pair's commutator has quaternion
matrix `comm4`. The checked coefficient tables give T² + T + 1 = 0.
Transport through the rational Leech comparison, its integral restriction,
and reduction modulo two proves this polynomial on the entire binary Leech
module. In characteristic two it excludes every nonzero fixed vector.

The reference cubic is an actual element, independent of a long frame or a
carrier comparison. Identifying the image of the degree-100 marking under
an arbitrary equivalence with this cubic remains a separate conjugacy problem.
Likewise no assertion about its full ambient common centralizer is made here.

Source: Aschbacher, *Sporadic Groups* (1994), 49.1–49.2, p.280, and the
fixed-vector step of 49.5, p.283. The imported exact pair and coefficient
tables use ATLAS `J2G1-P2` and Gerald Höhn's icosian coordinates; their
attribution and license are retained in the imported modules and LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section

open Atlas.Conway Atlas.Algebra Atlas.Lattices Atlas.Codes
open Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Sporadic.LeechRelated.J2.IcosianComparison.Generators.RelatorMatrices

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel

local instance : DecidableEq IcosianQuaternion := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
    QuaternionAlgebra.ext_iff.symm

/-- A literal word in the retained integral Hermitian group. -/
def referenceLift : icosianHermitianGroup :=
  (xLift⁻¹ * yLift⁻¹ * xLift * yLift) ^ 4

theorem referenceLift_matrix : matrixHom referenceLift = comm4 := by
  simp only [referenceLift, map_pow, map_mul, matrixHom_xLift_inv,
    matrixHom_yLift_inv, matrixHom_xLift, matrixHom_yLift, c0_mul, c1_mul, comm_mul]
  calc
    comm ^ 4 = (comm * comm) * (comm * comm) := by noncomm_ring
    _ = comm4 := by rw [comm2_mul, comm4_mul]

theorem referenceLift_matrix_polynomial :
    matrixHom referenceLift * matrixHom referenceLift + matrixHom referenceLift + 1 = 0 := by
  rw [referenceLift_matrix, comm8_mul]
  decide +kernel

theorem referenceLift_polynomial (v : IcosianRationalCoordinates) :
    referenceLift.val (referenceLift.val v) + referenceLift.val v + v = 0 := by
  simp only [apply_eq_matrix]
  change (matrixHom referenceLift).mulVec ((matrixHom referenceLift).mulVec v) +
    (matrixHom referenceLift).mulVec v + v = 0
  have h := congrArg (fun M : QMatrix => M.mulVec v) referenceLift_matrix_polynomial
  simpa only [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec] using h

private theorem hermitian_polynomial_to_binary (f : icosianHermitianGroup)
    (hf : ∀ v, f.val (f.val v) + f.val v + v = 0) (v : LeechModTwo) :
    quotientModTwoRepresentation (icosianProjectiveToCo1 (icosianProjectiveProjection f))
        (quotientModTwoRepresentation (icosianProjectiveToCo1 (icosianProjectiveProjection f)) v) +
      quotientModTwoRepresentation (icosianProjectiveToCo1 (icosianProjectiveProjection f)) v + v = 0 := by
  let g := icosianHermitianToCo0 f
  have hr (w : RationalCoordinates) :
      (fullIsometryEquiv g).val ((fullIsometryEquiv g).val w) +
        (fullIsometryEquiv g).val w + w = 0 := by
    rw [show fullIsometryEquiv g = icosianHermitianToRational f from
      icosianHermitianToCo0_extension f]
    change icosianComparison (f.val (icosianComparison.symm
      (icosianComparison (f.val (icosianComparison.symm w))))) +
      icosianComparison (f.val (icosianComparison.symm w)) + w = 0
    rw [icosianComparison.symm_apply_apply]
    simpa only [map_add, map_zero, LinearEquiv.apply_symm_apply] using
      congrArg icosianComparison (hf (icosianComparison.symm w))
  have hi (z : leech) : g.val (g.val z) + g.val z + z = 0 := by
    apply Subtype.ext
    apply rationalEmbedding_injective
    change rationalEmbedding ((g.val (g.val z)).val + (g.val z).val + z.val) =
      rationalEmbedding 0
    rw [map_add, map_add, map_zero]
    have h := hr (rationalEmbedding z.val)
    change rationalExtension g.val (rationalExtension g.val (rationalEmbedding z.val)) +
      rationalExtension g.val (rationalEmbedding z.val) + rationalEmbedding z.val = 0 at h
    simpa only [rationalExtension_agrees] using h
  obtain ⟨z, rfl⟩ := leechReduction_surjective v
  rw [icosianProjectiveToCo1_mk, quotientModTwoRepresentation_compatible,
    leechModTwoRepresentation_reduce, leechModTwoRepresentation_reduce]
  simpa only [map_add, map_zero] using congrArg leechReduction (hi z)

/-- The reference cubic in the quotient by exactly the two central signs. -/
def referenceProjective : IcosianProjectiveModel :=
  icosianProjectiveProjection referenceLift

/-- The same reference in the actual Conway central quotient. -/
def referenceCubic : LeechCentralQuotient :=
  icosianProjectiveToCo1 referenceProjective

/-- This is the literal full ambient common centralizer required by 49.2. -/
def referenceCentralizer : Subgroup LeechCentralQuotient :=
  centralizerI ⊓ Subgroup.centralizer (Subgroup.zpowers referenceCubic : Set LeechCentralQuotient)

theorem referenceCubic_mem : referenceCubic ∈ centralizerI :=
  janko_mem_centralizerI _

theorem referenceCubic_polynomial (v : LeechModTwo) :
    quotientModTwoRepresentation referenceCubic
        (quotientModTwoRepresentation referenceCubic v) +
      quotientModTwoRepresentation referenceCubic v + v = 0 :=
  hermitian_polynomial_to_binary referenceLift referenceLift_polynomial v

/-- The reference acts without nonzero fixed vectors on all 24 binary dimensions. -/
theorem referenceCubic_fixedFree : CubicFixedFree referenceCubic := by
  intro v hv
  have h := referenceCubic_polynomial v
  rw [hv, hv] at h
  have hz : v + v = 0 := by
    have hz := two_smul Bit v
    simpa using hz.symm
  simpa only [hz, zero_add] using h

theorem referenceLift_cube : referenceLift ^ 3 = 1 := by
  apply matrixHom_injective
  rw [map_pow, referenceLift_matrix, map_one]
  calc
    comm4 ^ 3 = (comm4 * comm4) * comm4 := by noncomm_ring
    _ = 1 := by rw [comm8_mul, comm12_mul]

theorem referenceProjective_ne_one : referenceProjective ≠ 1 := by
  intro h
  have hs : referenceLift ∈ icosianCentralSigns := (QuotientGroup.eq_one_iff _).mp h
  rcases hs with h | h
  · have hm := congrArg matrixHom h
    rw [referenceLift_matrix, map_one] at hm
    exact (by decide +kernel : comm4 ≠ 1) hm
  · have hm := congrArg matrixHom h
    rw [referenceLift_matrix, matrixHom_centralSign] at hm
    exact (by decide +kernel : comm4 ≠ -1) hm

theorem referenceProjective_order : orderOf referenceProjective = 3 := by
  apply orderOf_eq_prime _ referenceProjective_ne_one
  exact (map_pow icosianProjectiveProjection referenceLift 3).symm.trans
    (by rw [referenceLift_cube, map_one])

theorem referenceCubic_order : orderOf referenceCubic = 3 := by
  rw [referenceCubic, orderOf_injective icosianProjectiveToCo1
    icosianProjectiveToCo1_injective, referenceProjective_order]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
