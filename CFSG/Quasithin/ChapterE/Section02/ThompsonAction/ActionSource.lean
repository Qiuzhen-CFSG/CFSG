module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.GlobalThompsonSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ImagesSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.AlphaSource

/-!
# Common original E.2.3 action identities

The complete source classification identifies the actual global Thompson
image and the original Thompson–Baumann image. The proved Baumann arguments
supply the exact alpha and residual orbit identities on the same original
reduced subgroup. This packages the common conclusions without introducing
an earlier-classification, recognition, kernel, or geometric premise.
The factorwise natural-module and Sylow statements remain in their marked
source branches, and the block exit is the separate C.1.29 argument.

Source: Aschbacher–Smith E.2.3(1)–(3), printed pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_action_conclusions
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    pResidual 2 G ≤ elementaryAbelianMaxJ (⊤ : Subgroup G) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = offenderSubgroup α ∧
      (elementaryAbelianMaxJ (T : Subgroup G)).map q = (baumann (T : Subgroup G)).map q ∧
      thompsonAlpha (T : Subgroup G) =
        ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
          centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ∧
      conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
        (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
          (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let := hU.normal
  let := hU.elementary
  exact ⟨(residual_le_thompson T hP U hU hJ).1,
    source_global_thompson_image hG T hP U hU hJ,
    source_thompson_baumann_image hG T hP U hU hJ,
    source_alpha_and_orbit_span hG T hP U hU hJ⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
