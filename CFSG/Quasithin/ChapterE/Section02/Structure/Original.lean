module
public import CFSG.Quasithin.ChapterE.Section02.Structure.CoreLayer
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.Quotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Quasithin.Rank

/-!
# The original E.2.2 component before removing O₂

Pass through the literal quotient H/O₂(H), whose odd-prime ranks decrease.
The actual minimal parabolic, prescribed Sylow, unique maximal and normal
core descend through this quotient. The core-free source reduction produces
a quasisimple component. Its genuine C-component lift generates H with T,
and its intrinsic two-core quotient is precisely its image downstairs.

Source: Aschbacher–Smith E.2.2, printed pp.215–216. The subsequent finite
simple model classification is not assumed by this opening theorem.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H]

/-- SQTK descends through the genuine normal two-subgroup quotient. -/
theorem sqtk_two_quotient {κ : GroupClass.{u}} (hH : IsSQTK κ H)
    (N : Subgroup H) [N.Normal] (hN : IsPGroup 2 N) : IsSQTK κ (H ⧸ N) := by
  refine ⟨?_,hH.isKGroup.quotient N⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho N hN).trans
    (hH.stronglyQuasithin p hp ho)

/-- The generating source component of E.2.2 in the original group. -/
theorem source_original_component {κ : GroupClass.{u}} (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K ⊔ (T : Subgroup H) = ⊤ ∧
      IsComponent (H ⧸ pCore 2 H) (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  let N := pCore 2 H
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  let S := T.mapSurjective hq
  have hnT : N ≤ (T : Subgroup H) := pCore_isPGroup.le_sylow_of_normal T
  have hPq := ChapterB.minimalParabolic_surjective T hP q hq
    (by simpa only [q,QuotientGroup.ker_mk'] using hnT)
  let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  have hsq : ¬ Group.IsSolvable (H ⧸ N) := fun h => hs
    ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,h⟩)
  obtain ⟨L,hL,hLC,hgen⟩ := exists_generating_quasisimple_component
    (sqtk_two_quotient hH N pCore_isPGroup) S hPq hsq (pCore_quotient_pCore_eq_bot (G := H) 2)
  obtain ⟨K,hK,he⟩ := hLC.exists_map_quotient_eq N
  have hKcomp : IsComponent (H ⧸ N) (K.map q) := he.symm ▸ hL
  let : IsQuasisimple (K.map q) := hKcomp.2
  have hquasi : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm
  refine ⟨K,hK,hquasi,?_,hKcomp⟩
  have hm : (K ⊔ (T : Subgroup H)).map q = ⊤ := by
    rw [Subgroup.map_sup,he]
    exact hgen
  have hh := congrArg (Subgroup.comap q) hm
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top,
    sup_eq_left.mpr (hnT.trans le_sup_right)] at hh
  exact hh

/-- The original core image is the actual center of the quotient layer. -/
theorem source_original_core_center {κ : GroupClass.{u}} (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) :
    (ChapterB.minimalParabolicCore T hP).map (QuotientGroup.mk' (pCore 2 H)) =
      (center (componentLayer (H ⧸ pCore 2 H))).map
        (componentLayer (H ⧸ pCore 2 H)).subtype := by
  let N := pCore 2 H
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hk : q.ker ≤ (T : Subgroup H) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal T
  have hPq := ChapterB.minimalParabolic_surjective T hP q hq hk
  let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  have hsq : ¬ Group.IsSolvable (H ⧸ N) := fun h => hs
    ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,h⟩)
  obtain ⟨K,hK,_,hgen,_,hcenter,_⟩ := source_component_reduction
    (sqtk_two_quotient hH N pCore_isPGroup) (T.mapSurjective hq) hPq hsq
    (pCore_quotient_pCore_eq_bot (G := H) 2)
  exact (ChapterB.minimalParabolicCore_map T hP q hq hk).trans hcenter
end CFSG.Quasithin.ChapterE.Structure
