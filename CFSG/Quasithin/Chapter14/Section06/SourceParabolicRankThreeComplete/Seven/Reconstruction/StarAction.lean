module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels.Actor

/-!
# The full seven-letter star action on the original module

The central kernel of the two-core-to-star map vanishes because the given
A7 quotient is centerless. Its actual star image is self-centralizing, so
the complete B.5 classification supplies the whole moved module and its
fixed complement. No shortness or whole-block conclusion is assumed.

Source: Aschbacher--Smith, C.2.7(1--2), B.5.1 and14.6.10(5), pp.145--147,
99--103 and1029.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
open CFSG.Quasithin
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

@[expose] noncomputable def sevenStarEquiv (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    (K ⧸ pCore 2 K) ≃* starImage K R K := by
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' : e x ∈ center (alternatingGroup (Fin 7)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hx'
    exact e.injective (by simpa using hx')
  exact MulEquiv.ofBijective (coreToStar h.normalizes)
    ⟨(coreToStar h.normalizes).ker_eq_bot_iff.mp
      (le_bot_iff.mp ((coreToStar_ker_central_from_source h).trans_eq hz)),
      coreToStar_surjective h.normalizes⟩

@[simp] theorem sevenStarEquiv_apply (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : K ⧸ pCore 2 K) :
    sevenStarEquiv h e x = coreToStar h.normalizes x := rfl

theorem star_actionData (h : Input KnownSimple.IsKnownSimple H R M K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    Nonempty (AlternatingModels.ActionData (starRepresentation K R) (starImage K R K)) := by
  let E := (sevenStarEquiv h e).symm.trans e
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  let : (starImage K R K).Normal := Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hfit := (star_fitting_quasisimple (source_join_input h)).1
  let : IsQuasisimple (starImage K R K) := (star_fitting_quasisimple (source_join_input h)).2
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (starImage K R K) := E.isSimpleGroup
  have hz : center (starImage K R K) = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' : E x ∈ center (alternatingGroup (Fin 7)) := (centerCongr E ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp)] at hx'
    exact E.injective (by simpa using hx')
  have hcentral : centralizer (starImage K R K : Set (StarQuotient K R)) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxK : x ∈ starImage K R K := by
      rw [← hfit] at hx ⊢
      exact centralizer_generalizedFitting_le _ hx
    have hxz : (⟨x,hxK⟩ : starImage K R K) ∈ center (starImage K R K) := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hz] at hxz
    exact congrArg Subtype.val hxz
  have hsqK : IsSQTK KnownSimple.IsKnownSimple K :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.component.1)).mp
      (h.setup.sqtk.subgroup (K.subgroupOf H))
  have hsq : IsSQTK KnownSimple.IsKnownSimple (starImage K R K) :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hsqK
      (ChapterA.Section02.IsSectionOf.of_surjective (toStarImage K R) (toStarImage_surjective K R))
  exact AlternatingModels.nonempty_actionData _ _ E hcentral hsq
    (starRepresentation_injective K R) (star_moved_section_from_source h).1

end CFSG.Quasithin.Chapter14.Section06.Seven.Reconstruction
