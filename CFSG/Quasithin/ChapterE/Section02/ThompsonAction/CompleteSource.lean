module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SourceAlternatives
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SolvableBaumann
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
/-!
# Unconditional classification in the original E.2.3 Sylow argument

The complete known-simple B.5 theorem is applied to the original faithful
centralizer quotient. The solvable and quasisimple rows and the linear pair
are discharged by the proved Baumann and symmetric-five source theorems.
Only the actual paired symmetric-five action remains, retaining its two
factors and the exchange by the prescribed Sylow subgroup. No earlier
classification or module-recognition input remains.

Source: Aschbacher--Smith E.2.3 and3.1.7, pp.216--217 and575--576.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original-source Sylow alternative with all earlier classification inputs discharged. -/
theorem source_sylow_or_paired_five
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    SourceSylowAlternative T hP ∨
      SymmetricFivePairSource T U (QuotientGroup.mk' C)
        (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) := by
  classical
  let := hU.normal
  let := hU.elementary
  by_cases hs : Group.IsSolvable G
  · let := hs
    exact Or.inl (Or.inl (source_solvable_baumann_sylow_and_alpha T hP U hU hJ
      (hG.stronglyQuasithin 3 (by decide) (by decide)) inferInstance).1)
  · exact nonsolvable_sylow_or_paired_five
      ChapterB.SourceInduction.adequateClassification_knownSimple hG T hP U hU hJ
      _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hs

/-- In the nonsolvable branch the actual factors are natural SL2 or symmetric-five,
with the original source decomposition and without an earlier-classification premise. -/
theorem source_nonsolvable_natural_factors
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U) (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup ρ
    let σ := ρ.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ (generalizedFitting Y),
        (∃ F : ChapterB.QuasisimpleSource.BinaryField, ChapterB.QuasisimpleSource.IsLinearNatural
          (c.sectionData.action.comp (generalizedFitting Y).subtype) F 2) ∨
        Nonempty (ChapterB.QuasisimpleSource.MarkedActionEquiv c.sectionData.action
          (offenderSubgroup c.sectionData.action) (generalizedFitting Y)
          (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) ∨
      ∃ c : ChapterB.SourceInduction.SourceTwoFactorCase σ,
        ChapterB.SourceRankOneFactor σ c.first c.firstSpace ∧
          ChapterB.SourceRankOneFactor σ c.second c.secondSpace := by
  let := hU.normal
  let := hU.elementary
  exact nonsolvable_natural_factors
    ChapterB.SourceInduction.adequateClassification_knownSimple
    hG T hP U _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hU.quotient_pCore_eq_bot hs hJ
end CFSG.Quasithin.ChapterE.ThompsonAction
