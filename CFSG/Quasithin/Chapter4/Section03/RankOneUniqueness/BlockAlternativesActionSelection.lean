module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesLinearThree
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ActionIrreducibility
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedIrreducibility
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeActor

/-!
# Source action selection for the rank-one block argument

The intrinsic block interval makes the actual star moved/fixed section
irreducible, also after restriction to the offender-generated subgroup.
The proved B.5 theorem therefore supplies its irreducible action catalogue.
On an SL₃ star component the full marked table selects a natural action;
the existing quotient, degree and parabolic transports then prove the block
contradiction. No action-selection or degree premise remains in this branch.
The full module W remains distinct from the original chosen V.

The finite, symplectic and large G₂ C.4.1 rows remain with the assembly owner
qt-d-1222-rankone-uniqueness-block. This module proves the SL₃ row only.
Source: Aschbacher–Smith B.5.1, C.4.7 and original 4.3.7,
printed pp.99–103,153,615–616.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Block irreducibility holds on every correctly restricted star moved section. -/
theorem SourceConfiguration.block_restricted_star_irreducible
    (c : SourceConfiguration T L) (hb : IsBlock c.K)
    (J : Subgroup (StarQuotient (c.K.map c.H.subtype) (c.I.pCoreIn 2)))
    (hCJ : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≤ J)
    (s : MovedSection ((starRepresentation (c.K.map c.H.subtype)
      (c.I.pCoreIn 2)).comp J.subtype)
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J)) :
    IsIrreducible (s.action.comp
      ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf J).subtype) := by
  apply IsLinearBlockModel.action_irreducible hb.short
  exact c.block_model_of_restricted_star_moving hb J hCJ s _
    ⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩

/-- Apply the proved B.5 irreducible branch to the literal offender subgroup. -/
theorem SourceConfiguration.block_star_irreducible_source
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K) :
    let ρ := starRepresentation (c.K.map c.H.subtype) (c.I.pCoreIn 2)
    let J := offenderSubgroup ρ
    let C := starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)
    C ≤ J ∧ ∃ s : MovedSection (ρ.comp J.subtype) (C.subgroupOf J),
      IsIrrPlus (ρ.comp J.subtype) (C.subgroupOf J) s.space.toSubmodule ∧
      ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase s.action
        (C.subgroupOf J) (offenderSubgroup s.action) := by
  let A := c.K.map c.H.subtype
  let R := c.I.pCoreIn 2
  let hi := c.block_source_input hf
  let : (A.subgroupOf (A ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer c.block_radical_normalizes)
  have hs := C27Source.star_offender_hypothesis_knownSimple (C27Source.source_join_input hi)
  obtain ⟨hCJ,⟨a⟩⟩ := C27Source.star_moved_section_from_source hi
  let := hs.quasisimple
  have hI := a.sectionData.irrPlus_of_irreducible
    (c.block_restricted_star_irreducible hb _ hCJ a.sectionData)
  obtain ⟨_,_,_,hcase,_⟩ := hs.irreducible_source_data
    ChapterB.SourceClassification.irreducibleClassification_knownSimple
    ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups
    a.sectionData hI
  exact ⟨hCJ,a.sectionData,hI,hcase⟩

/-- The SL₃ group row selects its natural action and the original field degree. -/
theorem SourceConfiguration.linearThree_block_of_star_group
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (F : BinaryField)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : IsSL3EvenBlock c.K n := by
  have hF := c.linearThree_degree_gt_one hn F.degree_pos hpsl F.card_eq
    ((c.block_star_quotientEquiv hb).trans e)
  obtain ⟨hCJ,s,_,hs⟩ := c.block_star_irreducible_source hf hb
  obtain ⟨E,⟨a⟩⟩ := linearThree_natural_of_irreducible_source s.action hs F hF
    ((subgroupOfEquivOfLe hCJ).trans e)
  exact c.linearThree_block_of_source_moved_action hn hpsl hf hb _ hCJ s E a

/-- The actual source SL₃ row contradicts the crossed full-module configuration. -/
theorem SourceConfiguration.false_of_linearThree_star_group
    {V : Subgroup G} (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (F : BinaryField)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 3) F.Carrier) : False :=
  c.false_of_linearThree_block D hn hf hb
    (c.linearThree_block_of_star_group hn hpsl hf hb F e)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
