module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.Bounds
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.FixedSpaces.Native
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.InvariantCandidate.LiteralGeometry.FixedSpaces.Conjugacy
import all CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Reduction

/-!
# Octad-kernel fixed-space bounds in literal J₄ max1

The certified Mathieu quotient agrees with the actual left-conjugation
representation after its prescribed star relabeling. The binary-coordinate
bijection therefore identifies centralizers inside the intrinsic E₂¹¹ core
with fixed masks for the native octad translations. Their checked counts
give 128 fixed vectors for every nonidentity translation and at most 64
common fixed vectors. Native octad transitivity and lifts through the
surjective quotient map transport both bounds to every octad.

The `import all` edge is an intentional internal comparison with the body
of `certifiedMathieuQuotientEquiv`: it verifies that the quotient used in
`Bounds` is the marked star comparison, without changing the shared API.
No splitting or alternate representation is assumed.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and the J₄ local
configuration in the proof of 1.3.9, p.514; GLS3 Table 5.3i.
-/

public section
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Janko4 Janko4.Cardinality Janko4.Cardinality.QuotientCount
open Janko4.Cardinality.QuotientCount.Image
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open LiteralBinary

set_option maxRecDepth 10000
attribute [local irreducible] Janko4.modelGroup Janko4.Cardinality.max1Subgroup

private theorem literalMathieuMap_starProjection (g : certifiedMathieuSubgroup) :
    (literalMathieuMap g : Equiv.Perm (Fin 24)) =
      MulAut.conj StarOrderCertificate.relabel
        (starProjection matrixA_mul_self matrixB_pow_four g) := by
  change (starGroupEquivM24 _ : Equiv.Perm (Fin 24)) = _
  exact starGroupEquivM24_apply _

private theorem literalStarProjection_eq_translation (g : certifiedMathieuSubgroup)
    (n : Fin 16) (hg : literalMathieuMap g = nativeTranslation n) :
    starProjection matrixA_mul_self matrixB_pow_four g = translationStar n := by
  rw [translationStar_eq, ← hg, literalMathieuMap_starProjection]
  change _ = (MulAut.conj StarOrderCertificate.relabel).symm
    ((MulAut.conj StarOrderCertificate.relabel) _)
  exact ((MulAut.conj StarOrderCertificate.relabel).symm_apply_apply _).symm

private theorem literalElementFixed_card (g : certifiedMathieuSubgroup) :
    Nat.card ((centralizer ({g} : Set certifiedMathieuSubgroup)).subgroupOf
      (pCore 2 certifiedMathieuSubgroup)) =
    Nat.card {m : Fin 2048 // maskImage
      (starMasks (starProjection matrixA_mul_self matrixB_pow_four g)) m.val = m.val} := by
  change Nat.card ((centralizer ({g} : Set (max1Subgroup matrixA_mul_self matrixB_pow_four))).subgroupOf
    (pCore 2 (max1Subgroup matrixA_mul_self matrixB_pow_four))) = _
  rw [← LocalStructure.localKernel_eq_twoCore]
  exact elementFixed_card matrixA_mul_self matrixB_pow_four g

private theorem literalCommonFixed_card (s : Set certifiedMathieuSubgroup) :
    Nat.card ((centralizer s).subgroupOf (pCore 2 certifiedMathieuSubgroup)) =
    Nat.card {m : Fin 2048 // ∀ g ∈ s, maskImage
      (starMasks (starProjection matrixA_mul_self matrixB_pow_four g)) m.val = m.val} := by
  change Nat.card ((centralizer s).subgroupOf
    (pCore 2 (max1Subgroup matrixA_mul_self matrixB_pow_four))) = _
  rw [← LocalStructure.localKernel_eq_twoCore]
  exact commonFixed_card matrixA_mul_self matrixB_pow_four s

/-- Every nonkernel element above the octad two-core fixes at most 128 kernel elements. -/
theorem literalOctad_elementFixedBound : LiteralOctadElementFixedBound := by
  apply literalOctad_elementFixedBound_of_seed
  intro g hg hng
  obtain ⟨n, hn⟩ := nativeTranslation_surjective hg
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hng
    rw [← literalMathieuMap_ker]
    exact hn.symm.trans nativeTranslation_zero
  rw [literalElementFixed_card, literalStarProjection_eq_translation g n hn.symm,
    translation_fixed_card n hn0]

/-- Two independent native translations already cut the common fixed space to 64. -/
theorem literalOctad_commonFixedBound : LiteralOctadCommonFixedBound := by
  apply literalOctad_commonFixedBound_of_seed
  obtain ⟨g₁, hg₁⟩ := literalMathieuMap_surjective (nativeTranslation 1)
  obtain ⟨g₂, hg₂⟩ := literalMathieuMap_surjective (nativeTranslation 2)
  have h₁ : g₁ ∈ literalOctadTwoPreimage LinearFourCore.seedOctad := by
    change literalMathieuMap g₁ ∈ (octadStabilizer LinearFourCore.seedOctad).pCoreIn 2
    rw [hg₁]
    exact nativeTranslation_mem 1
  have h₂ : g₂ ∈ literalOctadTwoPreimage LinearFourCore.seedOctad := by
    change literalMathieuMap g₂ ∈ (octadStabilizer LinearFourCore.seedOctad).pCoreIn 2
    rw [hg₂]
    exact nativeTranslation_mem 2
  rw [literalCommonFixed_card]
  let f : {m : Fin 2048 // ∀ g ∈ literalOctadTwoPreimage LinearFourCore.seedOctad,
      maskImage (starMasks (starProjection matrixA_mul_self matrixB_pow_four g)) m.val = m.val} →
      {m : Fin 2048 //
        maskImage (starMasks (translationStar 1)) m.val = m.val ∧
        maskImage (starMasks (translationStar 2)) m.val = m.val} := fun m => ⟨m.val, by
    constructor
    · have h := m.property g₁ h₁
      rwa [literalStarProjection_eq_translation g₁ 1 hg₁] at h
    · have h := m.property g₂ h₂
      rwa [literalStarProjection_eq_translation g₂ 2 hg₂] at h⟩
  have hf : Function.Injective f := by
    intro a b h
    have he : (f a).val = (f b).val := congrArg Subtype.val h
    exact Subtype.ext he
  have h := Nat.card_le_card_of_injective f hf
  rw [translation_pair_fixed_card] at h
  exact h.trans_lt (by decide)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
