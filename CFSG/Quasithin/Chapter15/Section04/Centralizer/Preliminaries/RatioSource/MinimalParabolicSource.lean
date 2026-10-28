module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.OutsideWitness.Source
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd

import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# B.6.8(5) on the actual maximal-overgroup core

Restrict the given ambient Sylow subgroup to the minimal parabolic H.
Its original maximal overgroup N becomes the canonical intrinsic maximal
subgroup. The proved B.6.8(5) theorem then gives a Sylow two-subgroup of
the literal core of N in H. This subgroup is the pullback of O₂(H), so
it is normal and its image under the original inclusion is O₂(H).

This supplies the universal earlier B.6.8(5) input of the outside-core
branch of 15.4.2(4), without an additional source assumption.
The internal Structure import identifies its canonical core definition with
the normal core of the original specified maximal subgroup; no body is exposed.
Source: Aschbacher–Smith, B.6.8(5), printed pp.113–115.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
universe u
variable {X : Type u} [Group X] [Finite X]

private theorem intrinsic_minimalParabolic (T : Sylow 2 X) (H N : Subgroup X)
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

/-- The original B.6.8(5) universal input, now supplied by its proved
intrinsic source theorem with the literal core and inclusion maps retained. -/
theorem source_earlierB685 : OutsideWitness.EarlierB685.{u} := by
  intro X _ _ T H N hP hTN hNH
  let S := T.subtype (hTN.trans hNH.le)
  obtain ⟨hmin, hmax⟩ := intrinsic_minimalParabolic T H N hP hTN hNH
  have hN : N.subgroupOf H = ChapterB.minimalParabolicMax S hmin :=
    ChapterB.minimalParabolicMax_unique S hmin hmax (comap_mono hTN)
  have hcore : (N.subgroupOf H).normalCore = ChapterB.minimalParabolicCore S hmin := by
    rw [hN]
    rfl
  have hQ : pCore 2 H ≤ (N.subgroupOf H).normalCore := by
    rw [hcore]
    exact ChapterB.minimalParabolicTwoCore_le_core S hmin
  have hex : ∃ R : Sylow 2 (N.subgroupOf H).normalCore,
      (R : Subgroup (N.subgroupOf H).normalCore) =
        (pCore 2 H).subgroupOf (N.subgroupOf H).normalCore := by
    rw [hcore]
    exact ChapterB.minimalParabolic_twoCore_sylow_core S hmin
  obtain ⟨R, hR⟩ := hex
  refine ⟨R, ?_, ?_⟩
  · rw [hR]
    infer_instance
  · rw [hR, map_subgroupOf_eq_of_le hQ]

end CFSG.Quasithin.Chapter15.Section04.RatioSource
