module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalOffender
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.CriticalSelection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Offender
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalSelection
public import Theory.Representation.BinaryOffender.CommonCenterBound

/-!
# Displacement of the selected local alternating actor

Apply the existing local common-center estimate with the exact section kernel. The selected reciprocal rank comparison and the point-core rank bound give displacement at most three for each actor element.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- The common-center estimate on the literal reciprocal intersection.
Its two summands are the actual starred actor rank and U/(U∩Qα) rank. -/
theorem critical_fixedCodim_bounds_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* ChapterJ.S5)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) :
    fixedCodim ρ (c.Uα.subgroupOf F.H) ≤
      Nat.log 2 (Nat.card (star F c.Uα)) + Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ∧
      ∀ a : F.H, (a:G) ∈ c.Uα →
        Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 :=
  critical_fixedCodim_bounds_of_kernel_at h hab structural (action_kernel_eq_core h e s) s c

/-- The actual selected actor satisfies the source two-offender bound. -/
theorem selected_critical_fixedCodim_bound_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* ChapterJ.S5)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (selection : c.RankSelection) :
    fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) := by
  have hh := (critical_fixedCodim_bounds_at h hab structural e s c).1
  have hr := selection.comparison
  omega


/-- Every element of the selected critical actor moves at most three dimensions.
This is the literal reciprocal intersection estimate used against two
noncentral alternating chief factors. -/
theorem selected_critical_displacement_le_three_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* ChapterJ.S5)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (selection : c.RankSelection)
    (a : F.H) (ha : (a:G) ∈ c.Uα) :
    Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 3 := by
  have hh := (critical_fixedCodim_bounds_at h hab structural e s c).2 a ha
  have hr := selection.comparison
  rcases critical_actor_rank_at h hab structural e c with he | he <;> omega

/-- The original section receives the selected quadratic actor with its
actual factor-two offender inequality and the individual displacement bound. -/
theorem exists_selected_critical_action_of_alternating_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hAlt : AlternatingResidual F)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      IsQuadratic ρ (c.Uα.subgroupOf F.H) ∧
      fixedCodim ρ (c.Uα.subgroupOf F.H) ≤ 2 * Nat.log 2 (Nat.card (star F c.Uα)) ∧
      Nat.log 2 (Nat.card (star F c.Uα)) ≤ 2 ∧
      ∀ a : F.H, (a:G) ∈ c.Uα → Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 3 := by
  obtain ⟨c,hs,hplace,_,hr⟩ := exists_selected_critical_geometry_of_alternating_at h hab structural hAlt
  obtain ⟨e⟩ := exists_symmetric_star_at h structural hAlt
  exact ⟨c,hs,hplace,critical_quadratic h hab s c,
    selected_critical_fixedCodim_bound_at h hab structural e s c hs,hr,
    selected_critical_displacement_le_three_at h hab structural e s c hs⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
