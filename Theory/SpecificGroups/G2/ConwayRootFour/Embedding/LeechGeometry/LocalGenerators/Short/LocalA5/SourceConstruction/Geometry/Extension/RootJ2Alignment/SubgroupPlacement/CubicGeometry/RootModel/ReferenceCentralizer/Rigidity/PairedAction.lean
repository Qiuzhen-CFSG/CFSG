module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Coordinates
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Paired eigenspaces for the actual reference cubic

The literal cubic polynomial and the two nontrivial fourth-field scalars split
`fixedSpace` into its two reference eigenspaces. No dimension equality, source
root marking, or local-subgroup identification is used in this decomposition.

An invariant nondegenerate F-bilinear form makes each eigenspace totally
isotropic and pairs it nondegenerately with the other. An element fixing the
selected eigenspace must therefore fix its opposite. This identifies the
selected-action kernel with the kernel on all U-fixed vectors, and the last
theorem applies it to the exact integral hypothesis from `Coordinates`.

`ReferenceInvariantPairing` specifies genuine bilinear data. Its existence is
still a lattice obligation; none of the theorems here asserts that it exists.
The separate full-fixed-space kernel calculation is also not assumed proved.
`Rigidity` gives their conditional application to eigenspace faithfulness.

Source context: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and the
natural-plus-dual action in 49.5, p.283. This is a linear-algebra reduction of
the actual lattice problem, not a new proof of the source centralizer
identification. Imported ATLAS coordinate and scalar conventions are retained.
-/

@[expose] public noncomputable section

open Atlas.Conway Atlas.Algebra Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long

private theorem scalar_add_inv : referenceScalar + referenceScalar⁻¹ = 1 := by
  apply Long.scalarFieldEquiv.injective
  simp only [map_add, referenceScalar, map_inv₀, RingEquiv.apply_symm_apply, map_one]
  decide +kernel

private theorem fixed_neg (w : fixedSpace) : -w = w := by
  apply Subtype.ext
  have hz := two_smul Bit w.val
  exact (eq_neg_of_add_eq_zero_left (by simpa using hz.symm)).symm

private theorem operator_square (v : fixedSpace) :
    referenceOperator (referenceOperator v) = referenceOperator v + v := by
  have h : referenceOperator (referenceOperator v) + referenceOperator v + v = 0 := by
    apply Subtype.ext
    exact referenceCubic_polynomial v.val
  exact (eq_neg_of_add_eq_zero_left (by simpa only [add_assoc] using h)).trans (fixed_neg _)

private theorem project_eigen (a b : F) (hab : a + b = 1) (hmul : a * b = 1)
    (v : fixedSpace) : referenceOperator v + b • v ∈ referenceEigenspace a := by
  rw [mem_referenceEigenspace, map_add, map_smul, operator_square, smul_add, smul_smul, hmul, one_smul]
  have he : 1 + b = a := by
    rw [← hab]
    have hb : b + b = 0 := by
      apply Long.scalarFieldEquiv.injective
      simp only [map_add, map_zero]
      exact (by decide +kernel : ∀ c : GoldenFour, c + c = 0) _
    rw [add_assoc, hb, add_zero]
  calc
    (referenceOperator v + v) + b • referenceOperator v =
        (1 + b) • referenceOperator v + v := by module
    _ = a • referenceOperator v + v := by rw [he]

/-- Every U-fixed vector splits into the two nontrivial cubic eigenspaces. -/
theorem referenceEigenspaces_span :
    referenceEigenspace referenceScalar ⊔ referenceEigenspace referenceScalar⁻¹ = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro v
  let u := referenceOperator v + referenceScalar⁻¹ • v
  let w := referenceOperator v + referenceScalar • v
  have hu : u ∈ referenceEigenspace referenceScalar :=
    project_eigen _ _ scalar_add_inv (mul_inv_cancel₀ referenceScalar_ne_zero) v
  have hw : w ∈ referenceEigenspace referenceScalar⁻¹ :=
    project_eigen _ _ (by rw [add_comm]; exact scalar_add_inv)
      (inv_mul_cancel₀ referenceScalar_ne_zero) v
  have hs : u + w = v := by
    have hd : referenceOperator v + referenceOperator v = 0 := by
      exact (eq_neg_iff_add_eq_zero.mp (fixed_neg _).symm)
    calc
      u + w = (referenceOperator v + referenceOperator v) +
          (referenceScalar + referenceScalar⁻¹) • v := by dsimp [u, w]; module
      _ = v := by rw [hd, scalar_add_inv, one_smul, zero_add]
  exact Submodule.mem_sup.mpr ⟨u, hu, w, hw, hs⟩

/-- The two literal eigenspaces form a direct-sum decomposition of fixedSpace. -/
theorem referenceEigenspaces_isCompl :
    IsCompl (referenceEigenspace referenceScalar) (referenceEigenspace referenceScalar⁻¹) := by
  refine ⟨?_, ?_⟩
  · exact (Module.End.eigenspaces_iSupIndep referenceOperator.toLinearMap).pairwiseDisjoint
      referenceScalar_ne_inv
  · rw [codisjoint_iff]
    exact referenceEigenspaces_span

/-- Genuine bilinear data on the literal fixed space. Its construction is a
separate lattice problem; this record contains no faithfulness assertion. -/
structure ReferenceInvariantPairing where
  form : LinearMap.BilinForm F fixedSpace
  nondegenerate : form.Nondegenerate
  invariant : ∀ (g : referenceCentralizer) (v w : fixedSpace),
    form (referenceFixedAction g v) (referenceFixedAction g w) = form v w

private theorem cubic_self_mem : referenceCubic ∈ referenceCentralizer := by
  refine ⟨referenceCubic_mem, ?_⟩
  intro z hz
  obtain ⟨n, rfl⟩ := hz
  exact (Commute.self_zpow referenceCubic n).symm.eq

private theorem pairing_operator (B : ReferenceInvariantPairing) (v w : fixedSpace) :
    B.form (referenceOperator v) (referenceOperator w) = B.form v w :=
  B.invariant ⟨referenceCubic, cubic_self_mem⟩ v w

private theorem same_eigen_zero (B : ReferenceInvariantPairing) (a : F)
    (ha : a * a ≠ 1) {v w : fixedSpace}
    (hv : v ∈ referenceEigenspace a) (hw : w ∈ referenceEigenspace a) :
    B.form v w = 0 := by
  have h := pairing_operator B v w
  rw [(mem_referenceEigenspace a v).mp hv, (mem_referenceEigenspace a w).mp hw,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right] at h
  have hz : (a * a - 1) * B.form v w = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

private theorem inv_square_ne_one : referenceScalar⁻¹ * referenceScalar⁻¹ ≠ 1 := by
  intro h
  apply referenceScalar_ne_inv
  have he : referenceScalar⁻¹ = referenceScalar := by
    calc
      referenceScalar⁻¹ = referenceScalar⁻¹ * (referenceScalar⁻¹ * referenceScalar) := by
        rw [inv_mul_cancel₀ referenceScalar_ne_zero, mul_one]
      _ = referenceScalar := by rw [← mul_assoc, h, one_mul]
  exact he.symm

/-- The selected eigenspace separates the opposite eigenspace under an
invariant nondegenerate form. -/
theorem referencePairing_separates_opposite (B : ReferenceInvariantPairing)
    {w : fixedSpace} (hw : w ∈ referenceEigenspace referenceScalar⁻¹)
    (hzero : ∀ v ∈ referenceEigenspace referenceScalar, B.form v w = 0) : w = 0 := by
  apply B.nondegenerate.2
  intro v
  have hv : v ∈ referenceEigenspace referenceScalar ⊔ referenceEigenspace referenceScalar⁻¹ := by
    rw [referenceEigenspaces_span]
    trivial
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
  rw [LinearMap.BilinForm.add_left, hzero p hp,
    same_eigen_zero B _ inv_square_ne_one hq hw, add_zero]

/-- Pointwise fixation on one eigenspace forces fixation on its paired
opposite, without assuming that the two representations commute with the inverter. -/
theorem referenceFixedAction_eq_one_of_pairing (B : ReferenceInvariantPairing)
    (g : referenceCentralizer) (hg : referenceEigenAction referenceScalar g = 1) :
    referenceFixedAction g = 1 := by
  have hleft (v : fixedSpace) (hv : v ∈ referenceEigenspace referenceScalar) :
      referenceFixedAction g v = v := by
    exact congrArg (fun f : referenceEigenspace referenceScalar ≃ₗ[F]
      referenceEigenspace referenceScalar => (f ⟨v, hv⟩).val) hg
  have hright (w : fixedSpace) (hw : w ∈ referenceEigenspace referenceScalar⁻¹) :
      referenceFixedAction g w = w := by
    apply sub_eq_zero.mp
    apply referencePairing_separates_opposite B
      ((referenceEigenspace referenceScalar⁻¹).sub_mem
        (referenceFixedAction_preserves g _ hw) hw)
    intro v hv
    rw [LinearMap.BilinForm.sub_right]
    apply sub_eq_zero.mpr
    have h := B.invariant g v w
    rwa [hleft v hv] at h
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ referenceEigenspace referenceScalar ⊔ referenceEigenspace referenceScalar⁻¹ := by
    rw [referenceEigenspaces_span]
    trivial
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
  exact (map_add (referenceFixedAction g) p q).trans (congrArg₂ (· + ·) (hleft p hp) (hright q hq))

/-- A lattice pairing identifies the eigenspace kernel with the kernel on
all U-fixed vectors; the geometric exclusion of that kernel is separate. -/
theorem referenceEigenAction_ker_eq_of_pairing (B : ReferenceInvariantPairing) :
    (referenceEigenAction referenceScalar).ker = referenceFixedAction.ker := by
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · exact referenceFixedAction_eq_one_of_pairing B g
  · intro hg
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun f : fixedSpace ≃ₗ[F] fixedSpace => f v.val) hg

/-- The literal integral hypothesis in Coordinates suffices to fix all of
fixedSpace once the invariant lattice pairing has been constructed. -/
theorem referenceEigen_fixes_fixedSpace_of_pairing (B : ReferenceInvariantPairing)
    (g : LeechIsometryGroup) (hg : leechCentralProjection g ∈ referenceCentralizer)
    (hfix : ∀ v ∈ fixedSpace,
      quotientModTwoRepresentation referenceCubic v = quotientModTwoRepresentation y v →
        leechModTwoRepresentation g v = v) :
    ∀ v ∈ fixedSpace, leechModTwoRepresentation g v = v := by
  have he : referenceEigenAction referenceScalar ⟨leechCentralProjection g, hg⟩ = 1 := by
    rw [referenceEigenAction_eq_one_iff]
    simpa only [quotientModTwoRepresentation_compatible] using hfix
  have hall := referenceFixedAction_eq_one_of_pairing B ⟨leechCentralProjection g, hg⟩ he
  intro v hv
  exact congrArg (fun f : fixedSpace ≃ₗ[F] fixedSpace => (f ⟨v, hv⟩).val) hall

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
