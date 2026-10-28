module
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Outer

/-!
# Compatible Sylows and their largest elementary subgroups in M22

The corrected ambient Sylow stabilizes the source octad, sextet and trio.
Its literal preimages are Sylow subgroups of the native inner M22 and the
setwise pair stabilizer. The intrinsic hexad core and the inner sextet
translations are precisely its two inner E16 subgroups; the outer sextet
translations are its unique outer E32 subgroup.

The raw translation catalogue is unconditional. The source's intrinsic
quintet-kernel formulation below takes exactly the two independent kernel
identities. Their producer and the final H.14.3 assembly remain with the
quintet-structure branch and the parent local-classification module.

Source: Aschbacher--Smith H.14 setup and H.14.3(1), printed pp.396--397,
combined manuscript of 1 March 2004. The proof uses the checked M23 E16
catalogue via the actual M22 embedding and small native centralizer checks.
-/

public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
namespace Sporadic.Mathieu.M22ChapterH.CompatibleSylow

/-- Both inner candidates exist in the chosen Sylow and are distinct. -/
theorem inner_candidates :
    (IsElementaryAbelian 2 (m22InnerHexadKernel m22SourceOctad) ∧
      Nat.card (m22InnerHexadKernel m22SourceOctad) = 16 ∧
      m22InnerHexadKernel m22SourceOctad ≤ inner.toSubgroup) ∧
    (IsElementaryAbelian 2 Sextet.innerTranslations ∧
      Nat.card Sextet.innerTranslations = 16 ∧ Sextet.innerTranslations ≤ inner.toSubgroup) ∧
    m22InnerHexadKernel m22SourceOctad ≠ Sextet.innerTranslations :=
  ⟨⟨Hexad.inner_kernel_elementary, Hexad.inner_kernel_card, innerHexad_le⟩,
    ⟨innerTranslations_elementary, innerTranslations_card, innerTranslations_le⟩,
    inner_candidates_distinct⟩

/-- An exact catalogue, including existence and containment in both directions. -/
theorem inner_catalogue (A : Subgroup M22) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≤ inner.toSubgroup) ↔
      A = m22InnerHexadKernel m22SourceOctad ∨ A = Sextet.innerTranslations := by
  constructor
  · rintro ⟨hA, hc, hAS⟩
    exact inner_card16 A hA hc hAS
  · rintro (rfl | rfl)
    · exact inner_candidates.1
    · exact inner_candidates.2.1

/-- The outer candidate exists and is the unique elementary subgroup of order 32. -/
theorem outer_catalogue (A : Subgroup m22PairStabilizer) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 32 ∧ A ≤ outer.toSubgroup) ↔
      A = Sextet.outerTranslations := by
  constructor
  · rintro ⟨hA, hc, hAS⟩
    exact outer_card32 A hA hc hAS
  · rintro rfl
    exact ⟨outerTranslations_elementary, outerTranslations_card, outerTranslations_le⟩

/-- Substitution of the two independently proved quintet-core identities keeps
the source's literal intersection with native M22 in the pair group. -/
theorem intrinsic_inner_intersection
    (hi : Sextet.innerTranslations = m22InnerQuintetKernel m22SourceSextet)
    (ho : Sextet.outerTranslations = m22OuterQuintetKernel m22SourceSextet) :
    (m22InnerQuintetKernel m22SourceSextet).map m22ToPairStabilizer =
      m22OuterQuintetKernel m22SourceSextet ⊓ m22ToPairStabilizer.range := by
  rw [← hi, ← ho]
  exact Sextet.innerTranslations_map_pair

/-- The complete intrinsic-kernel form of H.14.3(1) for the compatible Sylows.
Only recognition of the two translation restrictions as quintet cores remains
explicit; the parent assembly must supply both identities. -/
theorem intrinsic_catalogue
    (hi : Sextet.innerTranslations = m22InnerQuintetKernel m22SourceSextet)
    (ho : Sextet.outerTranslations = m22OuterQuintetKernel m22SourceSextet) :
    m22InnerHexadKernel m22SourceOctad ≠ m22InnerQuintetKernel m22SourceSextet ∧
    (∀ A : Subgroup M22,
      (IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≤ inner.toSubgroup) ↔
        A = m22InnerHexadKernel m22SourceOctad ∨ A = m22InnerQuintetKernel m22SourceSextet) ∧
    (∀ A : Subgroup m22PairStabilizer,
      (IsElementaryAbelian 2 A ∧ Nat.card A = 32 ∧ A ≤ outer.toSubgroup) ↔
        A = m22OuterQuintetKernel m22SourceSextet) := by
  rw [← hi, ← ho]
  exact ⟨inner_candidates_distinct, inner_catalogue, outer_catalogue⟩

/-- The inner alternatives written in the source's outer ambient group are
exactly KH and KQ intersected with L, using the literal inclusion. -/
theorem intrinsic_inner_images
    (hi : Sextet.innerTranslations = m22InnerQuintetKernel m22SourceSextet)
    (ho : Sextet.outerTranslations = m22OuterQuintetKernel m22SourceSextet)
    (A : Subgroup M22) (hA : IsElementaryAbelian 2 A)
    (hc : Nat.card A = 16) (hAS : A ≤ inner.toSubgroup) :
    A.map m22ToPairStabilizer = m22OuterHexadKernel m22SourceOctad ∨
    A.map m22ToPairStabilizer =
      m22OuterQuintetKernel m22SourceSextet ⊓ m22ToPairStabilizer.range := by
  rcases inner_card16 A hA hc hAS with rfl | rfl
  · exact Or.inl Hexad.inner_kernel_map_pair
  · rw [hi]
    exact Or.inr (intrinsic_inner_intersection hi ho)

end Sporadic.Mathieu.M22ChapterH.CompatibleSylow
