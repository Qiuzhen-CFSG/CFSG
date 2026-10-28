module
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
/-!
# Minimal parabolics on their own carrier

Restrict the given Sylow subgroup and marked maximal overgroup to the
parabolic. Subgroup correspondence preserves maximality and its uniqueness.
This is the literal carrier restriction used in B.6.8 and E.2.9.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
variable {X : Type*} [Group X] [Finite X]
theorem intrinsic_minimalParabolic (T : Sylow 2 X) (H N : Subgroup X)
    (hP : ChapterB.IsMinimalParabolicOver T H)
    (hTN : (T : Subgroup X) ≤ N) (hNH : N ⋖ H) :
    ChapterB.IsMinimalParabolicOver (T.subtype (hTN.trans hNH.le)) ⊤ ∧
      IsCoatom (N.subgroupOf H) := by
  have hmax : IsCoatom (N.subgroupOf H) := by
    refine ⟨?_, ?_⟩
    · intro he
      exact hNH.lt.not_ge (subgroupOf_eq_top.mp he)
    · intro L hL
      have hNL : N < L.map H.subtype := by
        have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hL
        rwa [map_subgroupOf_eq_of_le hNH.le] at hh
      have he : L.map H.subtype = H :=
        (hNH.eq_or_eq hNL.le (map_subtype_le L)).resolve_left (ne_of_gt hNL)
      apply map_injective H.subtype_injective
      simpa only [← MonoidHom.range_eq_map, range_subtype] using he
  refine ⟨(ChapterB.isMinimalParabolicOver_top_iff _).mpr ?_, hmax⟩
  refine ⟨⟨N.subgroupOf H, ⟨hmax, comap_mono hTN⟩, ?_⟩,
    (ChapterB.isMinimalParabolicOver_iff T H).mp hP |>.2⟩
  intro L hL
  have hSL : (T : Subgroup X) ≤ L.map H.subtype := by
    have hh := map_mono (f := H.subtype) hL.2
    change ((T : Subgroup X).subgroupOf H).map H.subtype ≤ _ at hh
    rwa [map_subgroupOf_eq_of_le (hTN.trans hNH.le)] at hh
  have hLH : L.map H.subtype < H := by
    have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hL.1.lt_top
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hh
  have hLN : L ≤ N.subgroupOf H :=
    map_le_iff_le_comap.mp (hP.1.le_maximal ⟨hTN, hNH⟩ hSL hLH)
  exact ((hL.1.le_iff.mp hLN).resolve_left hmax.ne_top).symm

end CFSG.Quasithin.ChapterB
