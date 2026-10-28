module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.AmbientGeometry.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.AmbientNormalizer.FixedSpace
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.FixedVector

/-!
# The embedded max1 core and its normalizer action

The intrinsic normal closure `localKernel` is O₂(max1). Mapping this equality
through the literal subgroup inclusion identifies its eleven matrix generators
with generators of `certifiedMathieuSubgroup.pCoreIn 2` in J₄. Their checked
common fixed line therefore bounds the ambient core normalizer by the concrete
vector stabilizer. This does not identify that stabilizer with max1.

Two separate obligations give a more direct route to the desired normalizer
bound: realize a normalizer element's action on the eleven generators by an
element of max1, and bound the ambient centralizer of the core. Agreement on
the generators makes the quotient of the two elements centralize the core.
The contracts below assert neither obligation as a theorem. They require no
simplicity, perfectness, or order assumption on the ambient matrix group.

Source: GLS3 Table 5.3i, printed p.270, asserts
N(O₂(C(2B))) = E₂¹¹.M₂₄. The literal matrix words and intrinsic core
identification are documented in `Janko4.Model.Cardinality.Subgroup` and
`Janko4.Model.LocalStructure.Mathieu`. The fixed-space certificate concerns
the eleven core words themselves; the distinct subgroup of order 2²¹ is not
used here.
-/

public section

open Subgroup Janko4 Janko4.Cardinality
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry

/-- Equality of the actual ambient embeddings, not just of abstract cores. -/
theorem literalCore_eq_embedded_localKernel : certifiedMathieuSubgroup.pCoreIn 2 =
    (localKernel matrixA_mul_self matrixB_pow_four).map
      (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype := by
  change (pCore 2 (max1Subgroup matrixA_mul_self matrixB_pow_four)).map _ = _
  rw [LocalStructure.localKernel_eq_twoCore]
  rfl

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

/-- The eleven certified core words, embedded in the ambient matrix carrier. -/
@[expose] def literalCoreGenerator (i : Fin 11) : Model :=
  KernelCount.basis matrixA_mul_self matrixB_pow_four i

/-- These words generate the embedded two-core in J₄. -/
theorem literalCoreGenerators_generate : closure (Set.range literalCoreGenerator) =
    certifiedMathieuSubgroup.pCoreIn 2 := by
  rw [literalCore_eq_embedded_localKernel,
    ← QuotientCount.Image.closure_basis_eq_localKernel, MonoidHom.map_closure,
    ← Set.range_comp]
  rfl

/-- Each matrix used by the fixed-space certificate belongs to the actual core. -/
theorem literalCoreGenerator_mem (i : Fin 11) :
    literalCoreGenerator i ∈ certifiedMathieuSubgroup.pCoreIn 2 := by
  rw [literalCore_eq_embedded_localKernel]
  exact ⟨_, KernelCount.basis_mem_localKernel _ _ i, rfl⟩

/-- The embedded core has the same unique fixed line as its eleven matrices. -/
theorem literalCore_fixed_row_eq (v : CosetVector)
    (hv : ∀ g ∈ certifiedMathieuSubgroup.pCoreIn 2, vectorRight v g = v) :
    v = v 0 • cosetBaseVector := by
  apply Janko4.OuterReduction.OddIndex.FixedSpaceCertificate.fixed_row_eq
  intro i
  have h := hv _ (literalCoreGenerator_mem i)
  change Matrix.vecMul v (KernelCount.representation matrixA_mul_self matrixB_pow_four
    (KernelCount.basis matrixA_mul_self matrixB_pow_four i)) = v at h
  rwa [KernelCount.representation_basis] at h

private theorem literalCore_fixed_row_eq_of_ne_zero (v : CosetVector) (hn : v ≠ 0)
    (hv : ∀ g ∈ certifiedMathieuSubgroup.pCoreIn 2, vectorRight v g = v) :
    v = cosetBaseVector := by
  have he := literalCore_fixed_row_eq v hv
  have htwo : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases htwo (v 0) with h | h
  · rw [h, zero_smul] at he
    exact (hn he).elim
  · simpa only [h, one_smul] using he

/-- A normalizer element fixes the unique nonzero fixed vector of the core. -/
theorem literalCore_normalizer_le_vectorStabilizer :
    normalizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) ≤
      cosetVectorStabilizer := by
  intro g hg
  have hbase : ∀ s ∈ certifiedMathieuSubgroup.pCoreIn 2,
      vectorRight cosetBaseVector s = cosetBaseVector := by
    intro s hs
    apply max1Subgroup_le_cosetVectorStabilizer matrixA_mul_self matrixB_pow_four
    exact certifiedMathieuSubgroup.pCoreIn_le 2 hs
  change vectorRight cosetBaseVector g = cosetBaseVector
  apply literalCore_fixed_row_eq_of_ne_zero
  · intro hz
    have he := congrArg (fun v => vectorRight v g⁻¹) hz
    rw [← vectorRight_mul, mul_inv_cancel, vectorRight_one] at he
    exact cosetBaseVector_ne_zero (he.trans (Matrix.zero_vecMul _))
  · intro s hs
    have hconj : g * s * g⁻¹ ∈ certifiedMathieuSubgroup.pCoreIn 2 :=
      (mem_normalizer_iff.mp hg s).mp hs
    calc
      vectorRight (vectorRight cosetBaseVector g) s =
          vectorRight (vectorRight cosetBaseVector (g * s * g⁻¹)) g := by
        simp only [← vectorRight_mul, inv_mul_cancel_right]
      _ = vectorRight cosetBaseVector g := by rw [hbase _ hconj]

/-- The outstanding action-image calculation: every ambient normalizer element
induces the same core action as some element of literal max1. Eleven equations
suffice by `literalCoreGenerators_generate`. -/
@[expose] def LiteralCoreActionRealization : Prop :=
  ∀ g : Model, g ∈ normalizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) →
    ∃ h ∈ certifiedMathieuSubgroup, ∀ i : Fin 11,
      g * literalCoreGenerator i * g⁻¹ = h * literalCoreGenerator i * h⁻¹

/-- The outstanding ambient centralizer calculation for the entire literal
core. This is distinct from `LiteralCentralizerControl`, which concerns the
center of a source-local section's two-core. -/
@[expose] def LiteralCoreCentralizerControl : Prop :=
  centralizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) ≤ certifiedMathieuSubgroup

/-- The centralizer obligation can be checked against exactly eleven words. -/
theorem mem_literalCoreCentralizer_iff (g : Model) :
    g ∈ centralizer (certifiedMathieuSubgroup.pCoreIn 2 : Set Model) ↔
      ∀ i : Fin 11, g * literalCoreGenerator i = literalCoreGenerator i * g := by
  rw [← literalCoreGenerators_generate, centralizer_closure, mem_centralizer_iff]
  constructor
  · intro h i
    exact (h _ (Set.mem_range_self i)).symm
  · rintro h x ⟨i, rfl⟩
    exact (h i).symm

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.AmbientGeometry
