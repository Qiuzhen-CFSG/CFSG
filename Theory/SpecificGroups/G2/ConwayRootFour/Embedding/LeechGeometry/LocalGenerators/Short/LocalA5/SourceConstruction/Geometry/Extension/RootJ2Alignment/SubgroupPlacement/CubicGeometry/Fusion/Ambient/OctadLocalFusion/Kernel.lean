module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Restriction
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalPairGeometry
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# The actual octad restriction has a two-group kernel

A pointwise fixer of the octad sublattice fixes one coordinate-eight vector,
so the existing cross-stabilizer theorem places it in the actual Golay monomial
group. Its permutation fixes every coordinate of the marked octad. The proved
ATLAS/native Mathieu coordinate equivalence identifies this octad with native
block number 100 and takes that permutation into the native octad pointwise
two-core. A two-power of the monomial element therefore belongs to the Golay
sign subgroup, which has exponent two. This proves that the literal restriction
kernel is a two-group, without needing its full extraspecial presentation.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.2. This proves the
kernel property consumed by `octadLocalFusion_of_imageFusion`; it makes no
claim of a full centralizer identification.

The proof reuses the ATLAS lattice and monomial constructions of Gerald Höhn
and ATLAS contributors, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`,
through the existing CFSG ports and their genuine native coordinate comparison.
See `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff` for the ATLAS Research
and Attribution License 1.0 and attribution.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

private def nativeOctad : Sporadic.Mathieu.M24LocalGeometry.Octad :=
  ⟨Sporadic.Mathieu.m24BlockAt 100,
    Finset.mem_image.mpr ⟨100, Finset.mem_univ _, rfl⟩⟩

private theorem nativeOctad_support (i : Fin 24) :
    i ∈ nativeOctad.val ↔ (golayBasis 0).val (MathieuCode.atlasPointEquiv.symm i) ≠ 0 := by
  change i ∈ Sporadic.Mathieu.m24BlockAt 100 ↔
    (golayBasis 0 : BinaryWord) (MathieuCode.atlasPointEquiv.symm i) ≠ 0
  rw [golayBasis_coe]
  revert i
  decide +kernel

private theorem axis_mem_lattice {a : Omega} (ha : (golayBasis 0).val a ≠ 0) :
    coordinateEight a ∈ lattice := by
  rw [mem_lattice_iff_support]
  intro i hi
  have hia : i ≠ a := by intro he; subst i; exact ha hi
  simp [coordinateEight, coordinateVector, hia]

private theorem kernel_fixes_axis (g : action.ker) {a : Omega}
    (ha : (golayBasis 0).val a ≠ 0) :
    g.val.val.val (coordinateEight a) = coordinateEight a :=
  (mem_action_ker g.val).mp g.prop ⟨coordinateEight a, axis_mem_lattice ha⟩

private theorem kernel_mem_monomial (g : action.ker) : g.val.val ∈ monomialSubgroup := by
  have hn : (golayBasis 0 : BinaryWord) ≠ 0 := by
    intro hz
    have hw := Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.ambientOctad_weight
    rw [hz] at hw
    simp at hw
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hn
  exact coordinateEight_fixer_mem_monomial g.val.val a (kernel_fixes_axis g ha)

private theorem monomial_kernel_permutation (g : action.ker) (m : GolayMonomialGroup)
    (hm : monomialEmbedding m = g.val.val) :
    ∃ k : ℕ, m.right ^ (2 ^ k) = 1 := by
  let n := Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv.symm m.right
  have hn : n ∈ MathieuCode.octadPointwiseKernel nativeOctad := by
    rw [MathieuCode.mem_octadPointwiseKernel]
    intro i hi
    have hfix := (monomial_axis_fixed_iff m (MathieuCode.atlasPointEquiv.symm i)).mp
      (by rw [hm]; exact kernel_fixes_axis g ((nativeOctad_support i).mp hi))
    have hh : (Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv n).val
        (MathieuCode.atlasPointEquiv.symm i) = MathieuCode.atlasPointEquiv.symm i := by
      simpa only [n, MulEquiv.apply_symm_apply] using hfix.1
    change MathieuCode.atlasPointEquiv.symm
      (n.val (MathieuCode.atlasPointEquiv (MathieuCode.atlasPointEquiv.symm i))) = _ at hh
    rw [MathieuCode.atlasPointEquiv.apply_symm_apply] at hh
    exact MathieuCode.atlasPointEquiv.symm.injective hh
  have hp : IsPGroup 2 (MathieuCode.octadPointwiseKernel nativeOctad) := by
    rw [← MathieuCode.octad_core_map_eq_pointwise]
    exact pCore_isPGroup.map _
  obtain ⟨k, hk⟩ := hp ⟨n, hn⟩
  have hnk : n ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have hmk := congrArg Sporadic.Mathieu.M24LocalGeometry.SextetCore.groupEquiv hnk
  simpa only [map_pow, map_one, n, MulEquiv.apply_symm_apply] using hmk

private theorem monomial_sq_of_right_one (m : GolayMonomialGroup) (hm : m.right = 1) :
    m ^ 2 = 1 := by
  have he : m = SemidirectProduct.inl m.left := by
    have h := SemidirectProduct.inl_left_mul_inr_right m
    simpa only [hm, map_one, mul_one] using h.symm
  rw [he, ← map_pow]
  have hs : m.left ^ 2 = 1 := by
    rw [pow_two]
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    ext i
    change m.left.toAdd.val i + m.left.toAdd.val i = 0
    rw [← two_mul, show (2 : Bit) = 0 by decide, zero_mul]
  rw [hs, map_one]

/-- The kernel of the literal integral octad restriction is a two-group. -/
theorem kernel_isTwoGroup : IsPGroup 2 action.ker := by
  intro g
  obtain ⟨m, hm⟩ := kernel_mem_monomial g
  obtain ⟨k, hk⟩ := monomial_kernel_permutation g m hm
  have hr : (m ^ (2 ^ k)).right = 1 := by
    exact (map_pow (SemidirectProduct.rightHom : GolayMonomialGroup →* Mathieu24CodeModel) m
      (2 ^ k)).trans hk
  have hp : m ^ (2 ^ (k + 1)) = 1 := by
    rw [pow_succ, pow_mul]
    exact monomial_sq_of_right_one _ hr
  refine ⟨k + 1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg monomialEmbedding hp
  simpa [hm] using he

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
