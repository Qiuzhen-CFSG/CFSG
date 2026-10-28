module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.ColumnDuality
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativePointCentralizer.Reference.OuterProjective.FiniteData

/-!
# The outer endpoint action and the reference row

The original matrix generators C and D transport the published scalar lines
through two kernel-checked endpoint permutations. Multiplicative compatibility
extends this action to their entire generated group. Its restriction to the
perfect core is the existing endpoint action, so conjugation on the core shows
that it normalizes the native M₂₂. Faithfulness of design conjugation then
identifies it with the literal projection through the core's central quotient.

The resulting uniform compatibility proves that the inverse right-row action
fixes the scalar line of representative 228 exactly when `referenceProjection`
stabilizes its published endpoint pair {11,19}. This discharges the outer-row
premise of `referencePointCentralizerEquivOfComparisons`; the independent
quintet identification belongs to the reference-comparison assembly owner.

Source: Aschbacher--Smith H.12.1(2,5,9), printed pp.393--394, and the
point-centralizer calculation in 14.4.12, printed pp.1011--1012 (1 March 2004
manuscript). Coordinate provenance is retained in `OuterProjective/source/README.md`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open CoreProjectiveAction Sporadic.Mathieu
open scoped Pointwise
namespace ReferenceOuterAction
private theorem compatible_exists_outer (g : Model) : ∃ p, Compatible g.val p := by
  let S : Submonoid Matrix12ˣ :=
    { carrier := {u | ∃ p, Compatible u p}
      one_mem' := ⟨1, compatible_one⟩
      mul_mem' := by
        rintro u v ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p * q, compatible_mul hp hq⟩ }
  have h : actionGroup.toSubmonoid ≤ S := by
    rw [actionGroup, Subgroup.closure_toSubmonoid_of_finite]
    apply Submonoid.closure_le.mpr
    rintro u (rfl | rfl)
    · exact ⟨permC, compatible_C⟩
    · exact ⟨permD, compatible_D⟩
  exact h g.property

/-- The degree-22 endpoint action of the full original matrix extension. -/
private noncomputable def permutationAction : Model →* Equiv.Perm (Fin 22) where
  toFun g := Classical.choose (compatible_exists_outer g)
  map_one' := compatible_unique (Classical.choose_spec (compatible_exists_outer 1)) compatible_one
  map_mul' g h := compatible_unique (Classical.choose_spec (compatible_exists_outer (g * h)))
    (compatible_mul (Classical.choose_spec (compatible_exists_outer g))
      (Classical.choose_spec (compatible_exists_outer h)))

private theorem permutationAction_spec (g : Model) : Compatible g.val (permutationAction g) :=
  Classical.choose_spec (compatible_exists_outer g)

section Identification
variable (f : Model →* Equiv.Perm (Fin 22)) (hf : ∀ g, Compatible g.val (f g))
include hf

private theorem restrict_core (x : derivedGroup) :
    f (componentInclusion x) = corePermutationAction x :=
  compatible_unique (hf (componentInclusion x)) (corePermutationAction_spec x)

private theorem conjugation (g : Model) (x : derivedGroup) :
    corePermutationAction (derivedConjugation g x) =
      f g * corePermutationAction x * (f g)⁻¹ := by
  have hi : componentInclusion (derivedConjugation g x) =
      g * componentInclusion x * g⁻¹ := by
    apply Subtype.ext
    rfl
  rw [← restrict_core f hf, hi, map_mul, map_mul, map_inv, restrict_core f hf]

private theorem mem_design (g : Model) : f g ∈ m22DesignAut := by
  have hc (g : Model) (p : Equiv.Perm (Fin 22)) (hp : p ∈ M22) :
      f g * p * (f g)⁻¹ ∈ M22 := by
    rw [← corePermutationAction_range_eq_M22] at hp ⊢
    obtain ⟨x, rfl⟩ := hp
    exact ⟨derivedConjugation g x, conjugation f hf g x⟩
  apply m22_normalizer_le_designAut
  rw [Subgroup.mem_normalizer_iff]
  intro p
  constructor
  · exact hc g p
  · intro hp
    have h := hc g⁻¹ _ hp
    have he : f g⁻¹ * (f g * p * (f g)⁻¹) * (f g⁻¹)⁻¹ = p := by
      rw [map_inv]
      group
    rwa [he] at h

private theorem equals_projection (g : Model) :
    f g = (referenceProjection g : Equiv.Perm (Fin 22)) := by
  let d : m22DesignAut := ⟨f g, mem_design f hf g⟩
  have hd : m22DesignAutToAut d =
      MulAut.centralQuotientAction derivedQuotientEquivM22 (derivedConjugation g) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨z, rfl⟩ := derivedQuotientEquivM22.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center derivedGroup) z
    apply Subtype.ext
    rw [m22DesignAutToAut_apply_perm, MulAut.centralQuotientAction_apply]
    change f g * corePermutationAction x * (f g)⁻¹ =
      corePermutationAction (derivedConjugation g x)
    exact (conjugation f hf g x).symm
  have he : d = referenceProjection g := by
    apply referenceDesignEquiv.injective
    change m22DesignAutToAut d = referenceDesignEquiv
      (referenceDesignEquiv.symm
        (MulAut.centralQuotientAction derivedQuotientEquivM22 (derivedConjugation g)))
    rw [referenceDesignEquiv.apply_symm_apply]
    exact hd
  exact congrArg Subtype.val he

end Identification
end ReferenceOuterAction

/-- The canonical projection matches the row-line action on the full outer
extension, with the same inverse endpoint convention as on the core. -/
theorem referenceProjection_compatible (g : Model) :
    Compatible g.val (referenceProjection g : Equiv.Perm (Fin 22)) := by
  rw [← ReferenceOuterAction.equals_projection ReferenceOuterAction.permutationAction
    ReferenceOuterAction.permutationAction_spec g]
  exact ReferenceOuterAction.permutationAction_spec g

/-- The marked inverse right-row scalar line corresponds to the literal
native unordered pair {11,19}, including the outer matrix generators. -/
theorem referenceRowPairComparison (g : Model) :
    Matrix.vecMul (projectiveVector 228) ((g.val⁻¹ : Matrix12ˣ) : Matrix12) ∈
      scalarLine (projectiveVector 228) ↔
        referenceProjection g ∈ referencePairStabilizer referencePair := by
  let p : Equiv.Perm (Fin 22) := referenceProjection g
  have h := referenceProjection_compatible g⁻¹ 228
  have hp : ((referenceProjection g⁻¹ : m22DesignAut) : Equiv.Perm (Fin 22)) = p⁻¹ :=
    congrArg Subtype.val (map_inv referenceProjection g)
  rw [hp, inv_inv] at h
  have hm : Matrix.vecMul (projectiveVector 228) ((g.val⁻¹ : Matrix12ˣ) : Matrix12) ∈
      scalarLine (projectiveVector (pairAction p 228)) := by
    rw [← h]
    exact Set.mem_image_of_mem (rightRow (g⁻¹).val) (Or.inl rfl)
  have hi : Matrix.vecMul (projectiveVector 228) ((g.val⁻¹ : Matrix12ˣ) : Matrix12) ∈
      scalarLine (projectiveVector 228) ↔ pairAction p 228 = 228 := by
    constructor
    · intro hv
      exact line_inj ((scalarLine_of_mem hm).symm.trans (scalarLine_of_mem hv))
    · intro he
      rwa [he] at hm
  rw [hi]
  change pairAction p 228 = 228 ↔ p • referencePair = referencePair
  rw [← endpointPair_injective.eq_iff, pairAction_spec, referenceVector_endpoints]
  rfl
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
