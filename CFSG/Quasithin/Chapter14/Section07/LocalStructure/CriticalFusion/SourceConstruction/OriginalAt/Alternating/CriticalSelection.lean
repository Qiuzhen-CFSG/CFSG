module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalSelection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.CriticalActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Selection

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.CriticalSelection.Orientation
public import Theory.GroupTheory.PCoreImage

/-!
# Selection in the local alternating branch

Apply the existing same-G,T critical geometry and reversal. One orientation satisfies the original reciprocal rank comparison; the literal point-core four-group bounds the critical actor rank by two.

Only Structural1222At at the original G,T is used. Independent model and
section lemmas are reused from LocalReduction; its universal APIs are preserved.
Source: Aschbacher–Smith, final paragraph of 14.7.40, printed p.1063,
and 14.7.52–63, printed pp.1065–1069. Earlier structural source discharge
and the unconditional classification remain with their existing owners.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Subgroup.CosetGeometry.RankTwo
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
local notation "S5" => ChapterJ.S5

/-- The alternating star marking gives escape and hence the original critical path. -/
theorem exists_criticalPath_of_alternating_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hAlt : AlternatingResidual F) : Nonempty (CriticalPath (L := L) F) := by
  obtain ⟨e⟩ := exists_symmetric_star_at h structural hAlt
  exact exists_criticalPath_at h hab (alternating_escape_at h hab structural e) structural

/-- Choose the original path or its explicitly constructed reverse. Both
quotient indices use the same original U/V₁ conjugation action. -/
theorem select_critical_orientation_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5) (c : CriticalPath (L := L) F) :
    ∃ a : CriticalPath (L := L) F, a.RankSelection := by
  exact select_critical_orientation_of_nontrivial_star_at h structural c
    (critical_star_nontrivial_at h hab structural e c)

/-- The point core is a literal four-group in the original star quotient. -/
theorem point_core_star_card_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5) : Nat.card (star F (F.Ri L 1)) = 4 := by
  have hm : (star F (F.Ri L 1)).map e.toMonoidHom =
      ((F.Ri L 1).subgroupOf F.H).map (quotientMarking e) := by
    rw [CriticalFusion.Source.star,map_map]
    rfl
  rw [←card_map_of_injective (K:=star F (F.Ri L 1)) (f:=e.toMonoidHom) e.injective,
    hm,point_core_image_card_at h structural e]

/-- Before natural recognition, every critical actor in the alternating
branch has rank one or two. -/
theorem critical_actor_rank_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (e : HStar F.H ≃* S5) (c : CriticalPath (L := L) F) :
    Nat.log 2 (Nat.card (star F c.Uα)) = 1 ∨
      Nat.log 2 (Nat.card (star F c.Uα)) = 2 := by
  have hle : star F c.Uα ≤ star F (F.Ri L 1) :=
    map_mono (comap_mono (critical_le_Ri_at h structural c))
  have hd := card_dvd_of_le hle
  rw [point_core_star_card_at h structural e] at hd
  have hn : 1 < Nat.card (star F c.Uα) :=
    (one_lt_card_iff_ne_bot _).mpr (critical_star_nontrivial_at h hab structural e c)
  have hd' : Nat.card (star F c.Uα) ∣ 2^2 := hd
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
  interval_cases k <;> norm_num at he <;> simp_all <;> decide

/-- The genuine critical rank comparison on the selected original path,
including the source bound k ≤ 2. No natural-module identification is used. -/
theorem exists_selected_critical_geometry_of_alternating_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hAlt : AlternatingResidual F) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧
      c.Uα ≤ F.Ri L 1 ∧ F.U ≤ conjugate F.H c.conjugator ∧
      Nat.log 2 (Nat.card (star F c.Uα)) ≤ 2 := by
  obtain ⟨c⟩ := exists_criticalPath_of_alternating_at h hab structural hAlt
  obtain ⟨e⟩ := exists_symmetric_star_at h structural hAlt
  obtain ⟨a,ha⟩ := select_critical_orientation_at h hab structural e c
  refine ⟨a,ha,critical_le_Ri_at h structural a,G2Source.reciprocal_placement h a,?_⟩
  rcases critical_actor_rank_at h hab structural e a with he | he <;> omega

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
