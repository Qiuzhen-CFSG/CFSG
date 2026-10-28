module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Conditions

/-!
# The exact classifier input for the original Baumann reduction

The native binary MS input has ambient product L R. Its inclusion equivalence
with that product transports characteristic two, while the same subgroup
supplies the odd-index radical and characteristic-normality conditions. This
gives the existing SmallMSPair interface consumed by the universal binary
C.1.34 theorem, preserving the full special-linear quotient marking.

The source Rudvalis countercase applies this construction to the MS group
produced inside its original LT. This module proves the input transport only;
qt-rank-two-ms93 owns the classifier and qt-d-14710-baumann retains its
chief-factor application.

Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, and the natural-point
reduction in C.1.37, pp.141--143.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {X : Type u} [Group X] [Finite X] {κ : GroupClass.{u}} {L R : Subgroup X}

/-- All existing small-MS source hypotheses follow from the intrinsic binary
input, with the literal product and quotient unchanged. -/
theorem smallMSPair_of_input (h : ChapterC.BinaryMS.Input κ L R) : SmallMSPair κ L R := by
  refine {
    finite := inferInstance
    sqtk := h.sqtk.subgroup _
    fitting := generalizedFitting_eq_pCore_of_selfCentralizing 2
      ((Theory.Quasithin.centralizer_pCore_le_iff 2 h.joinEquiv).mpr h.core_selfCentralizing)
    product := fun g _ => h.product g
    component := h.component.subgroupOf le_sup_left
    rankTwo := Or.inl ⟨h.derivedQuotientEquiv⟩
    radical := ?_
    characteristic := ?_ }
  · obtain ⟨P, hP, hodd, hcore⟩ := h.radical
    refine ⟨P, h.sup_eq_top.symm ▸ hP, ?_, hcore⟩
    have he : (P.subgroupOf (L ⊔ R)).index = P.index := by
      rw [h.sup_eq_top]
      exact P.index_comap_of_surjective topEquiv.surjective
    exact he.symm ▸ hodd
  · intro C hc hn
    by_contra hne
    apply h.characteristic C hc hne
    have he : h.joinEquiv.toMonoidHom = (L ⊔ R).subtype := by
      ext x
      exact h.joinEquiv_apply x
    have hh := hn.map h.joinEquiv.toMonoidHom h.joinEquiv.surjective
    rwa [he, map_subgroupOf_eq_of_le ((map_subtype_le C).trans le_sup_right)] at hh

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource
