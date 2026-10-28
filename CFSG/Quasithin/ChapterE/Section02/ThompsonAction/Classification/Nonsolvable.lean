module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Classification
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NonsolvableAlternatives
/-!
# Nonsolvable source classification on the literal offender action

The centralizer kernel lies in the solvable minimal-parabolic core, so a
nonsolvable original group has a nonsolvable faithful quotient. Apply the
complete earlier classifier to its actual offender subgroup. The solvable
and outer A6–C3 branches are excluded by its original perfect residual.
The surviving quasisimple, two-factor and hyperplane rows retain every
source module assertion and the original action and quotient maps.

Source: Aschbacher–Smith, B.6.9 and E.2.3, pp.115–116 and 216–217.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H] {K : GroupClass.{u}}

/-- The actual quotient leaves only the three nonsolvable B.5.6 rows. -/
theorem nonsolvable_offender_alternatives
    (earlier : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} K)
    (hG : IsSQTK K G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hs : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    let Y := offenderSubgroup ρ
    let σ := ρ.comp Y.subtype
    (IsQuasisimple (generalizedFitting Y) ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ
        (generalizedFitting Y))) ∨
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase σ) := by
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [← hker,he]
    exact le_top
  obtain ⟨hk,hp⟩ := ChapterB.minimalParabolic_reduced_image T hP q hq hcore hn
  have hsH : ¬ Group.IsSolvable H := by
    intro hh
    let := hh
    let := ChapterB.minimalParabolic_core_solvable T hP
    let : Group.IsSolvable q.ker :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hk) (inclusion_injective hk)
    exact hs (Group.isSolvable_of_ker_le_range q.ker.subtype q (by rw [range_subtype]))
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_,hff,_,_,_⟩ := ChapterB.lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  let c : ChapterB.SourceInduction.SQTKQuotient K H := {
    Cover := G
    kernel := q.ker
    sqtk := hG
    equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
  exact ChapterB.nonsolvable_offender_classification ρ earlier (T.mapSurjective hq) hp hsH
    (NormalElementaryQuotient.representation_injective U q hq hker) hff hcore ⟨c⟩

/-- Known-simple source application using only the genuine earlier classification inputs. -/
theorem source_nonsolvable_offender_alternatives_of_earlier
    (hA : ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput.{u}
      KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ChapterB.SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
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
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion σ
        (generalizedFitting Y))) ∨
      Nonempty (ChapterB.SourceInduction.SourceTwoFactorCase σ) ∨
      Nonempty (ChapterB.SourceInduction.HyperplaneCase σ) := by
  let := hU.normal
  let := hU.elementary
  exact nonsolvable_offender_alternatives
    (ChapterB.SourceInduction.adequateClassification_knownSimple_of_earlier_classification hA h36 h4)
    hG T hP U _ (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hU.quotient_pCore_eq_bot hs hJ
end CFSG.Quasithin.ChapterE.ThompsonAction
