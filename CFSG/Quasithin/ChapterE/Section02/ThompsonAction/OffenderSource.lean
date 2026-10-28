module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.OffenderSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.Basic
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# B.5.3 preparation on the original E.2.3 offender action

Thompson movement produces an FF module on the literal centralizer quotient.
Its offender subgroup inherits a genuine SQTK cover from the original group;
no strongly-quasithin quotient assertion is used. All original B.5.3 inputs,
together with the original residual containment and Sylow supplement, follow
from the supplied reduced module and minimal parabolic.

Source: Aschbacher–Smith B.6.9 and E.2.3, printed pp.116 and 216–217.
This supplies the full earlier B.5.6 classifier's input, not a classification
of the resulting factors.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H] {K : GroupClass.{u}}

/-- Every original E.2.3 quotient supplies B.5.3 on its actual offender subgroup. -/
theorem offender_source_hypotheses
    (hG : IsSQTK K G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    let ρ := NormalElementaryQuotient.representation U q hq hker
    let Y := offenderSubgroup ρ
    ChapterB.SourceInduction.FFHypothesis K (ρ.comp Y.subtype) ∧
      pResidual 2 H ≤ Y ∧ Y ⊔ (T : Subgroup G).map q = ⊤ := by
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [← hker,he]
    exact le_top
  have hp := (ChapterB.minimalParabolic_reduced_image T hP q hq hcore hne).2
  have hff : IsFFModule ρ := by
    obtain hf | ⟨_,hff,_,_,_⟩ := ChapterB.lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  let c : ChapterB.SourceInduction.SQTKQuotient K H := {
    Cover := G
    kernel := q.ker
    sqtk := hG
    equiv := QuotientGroup.quotientKerEquivOfSurjective q hq }
  exact ChapterB.minimalParabolic_offender_source_hypotheses ρ (T.mapSurjective hq) hp
    (NormalElementaryQuotient.representation_injective U q hq hker) hcore hff ⟨c⟩

/-- B.5.3 preparation for the literal centralizer quotient of the original reduced module. -/
theorem source_offender_hypotheses
    (hG : IsSQTK K G)
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    let Y := offenderSubgroup ρ
    ChapterB.SourceInduction.FFHypothesis K (ρ.comp Y.subtype) ∧
      pResidual 2 (G ⧸ C) ≤ Y ∧ Y ⊔ (T : Subgroup G).map q = ⊤ := by
  let := hU.normal
  let := hU.elementary
  exact offender_source_hypotheses hG T hP U _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hU.quotient_pCore_eq_bot hJ

end CFSG.Quasithin.ChapterE.ThompsonAction
