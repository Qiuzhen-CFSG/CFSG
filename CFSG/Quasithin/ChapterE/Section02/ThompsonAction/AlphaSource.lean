module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteOrbitSpan
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairedFiveOrbitSpan
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveOrbitSpan
/-!
# The unconditional original-source alpha and residual orbit identities

The complete known-simple action classification gives the actual natural
single factor or exchanged pair. All linear and symmetric-five branches
now prove the same literal residual orbit identity. Intersecting that
identity with alpha gives the exact moved-alpha decomposition. Both
conclusions retain the original group, Sylow, reduced subgroup and residual;
no model, classification, kernel saturation or geometric conclusion is an input.
Source: Aschbacher–Smith B.6.10 and E.2.3, pp.117 and216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

theorem source_alpha_and_orbit_span
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    thompsonAlpha (T : Subgroup G) =
      ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
        centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ∧
    conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
  let := hU.normal
  let := hU.elementary
  have hspan : conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
      (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) := by
    rcases source_linear_conclusions_or_symmetric_five hG T hP U hU hJ with
      h | ⟨hqs,c,⟨e⟩⟩ | ⟨d,t,ht₁,ht₂,⟨c⟩⟩
    · exact h.2.2
    · exact quasisimple_five_source_orbit_span T hP U hU hJ _
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hqs c.sectionData e
    · exact paired_five_source_orbit_span T hP U hU hJ _
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) d c ⟨t,ht₁,ht₂⟩
  exact ⟨RankOneBaumann.thompsonAlpha_decomposition_of_orbit_span T _
    ((commutator_le_left U (pResidual 2 G)).trans
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T))) _ hspan,hspan⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
