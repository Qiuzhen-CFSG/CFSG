module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Marking
/-!
# Fixed-value geometry for every marking of the natural three-space

The nonzero fixed-space hypothesis selects the point parabolic in an
arbitrarily marked incident pair. Inner-or-graph coverage gives a common
conjugating matrix. The coordinate line, incident plane, small invariant
subgroup bound and three-line orbit then transport by its natural action.
Both radicals are the intrinsic two-cores of the full parabolics.

This completes the literal matrix obligation used by the ambient
fixed-value construction; there are no extension or residual assumptions.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (1.7)(i), p.847.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open Matrix.PSL3Two ModelProof

private theorem map_inf_bot (k : SL) {A B : Subgroup VectorGroup} (h : A ⊓ B = ⊥) :
    A.map (vectorAction k).toMonoidHom ⊓ B.map (vectorAction k).toMonoidHom = ⊥ := by
  rw [← Subgroup.map_inf A B (vectorAction k).toMonoidHom (vectorAction k).injective, h, Subgroup.map_bot]

private theorem geometry_of_point_line (σ : MulAut SL) (g : SL) (i : Bool) (k : SL)
    (hp : markedParabolic σ g i = pointParabolicSL.map (MulAut.conj k).toMonoidHom)
    (hq : markedParabolic σ g (!i) = lineParabolicSL.map (MulAut.conj k).toMonoidHom) :
    ModelGeometry σ g i := by
  have hseed : modelValues σ g i = pointLine.map (vectorAction k).toMonoidHom := by
    rw [values_eq_core, hp, core_fixed_conj, MarkedProduct.pointParabolic_core, fixed_pointCore]
  have hother : modelValues σ g (!i) = incidentPlane.map (vectorAction k).toMonoidHom := by
    rw [values_eq_core, hq, core_fixed_conj, lineParabolicSL_pCoreIn_two_eq_R, fixed_lineCore]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A hc hi
    have hc' : Nat.card (A.map (vectorAction k⁻¹).toMonoidHom) ≤ 4 := by
      rw [Subgroup.card_map_of_injective (f := (vectorAction k⁻¹).toMonoidHom)
        (vectorAction k⁻¹).injective]
      exact hc
    have hs := ModelProof.small_invariant _ hc' (invariant_pullback k pointParabolicSL A
      (hp ▸ hi))
    have hm := Subgroup.map_mono (f := (vectorAction k).toMonoidHom) hs
    rw [map_action_cancel] at hm
    rwa [hseed]
  · rw [hseed, hp, fixedSpace_conj]
    exact Subgroup.map_mono line_fixed_by_point
  · rw [hseed, Subgroup.card_map_of_injective (f := (vectorAction k).toMonoidHom)
      (vectorAction k).injective, line_card]
  · rw [hseed, hother]
    exact Subgroup.map_mono line_le_plane
  · rw [hother]
    intro he
    apply plane_ne_top
    apply Subgroup.map_injective (f := (vectorAction k).toMonoidHom) (vectorAction k).injective
    rw [he, Subgroup.map_top_of_surjective (vectorAction k).toMonoidHom (vectorAction k).surjective]
  · refine ⟨MulAut.conj k lineCycle, MulAut.conj k (lineCycle ^ 2), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hq]
      exact mem_map_of_mem _ lineCycle_mem
    · rw [hq]
      exact mem_map_of_mem _ (lineParabolicSL.pow_mem lineCycle_mem 2)
    · rw [hseed, map_action_conj]
      exact map_inf_bot k line_neighbors.1
    · rw [hseed, map_action_conj]
      exact map_inf_bot k line_neighbors.2.1
    · rw [hseed, map_action_conj, map_action_conj]
      exact map_inf_bot k line_neighbors.2.2

/-- Nonzero fixed vectors select the point member of the arbitrarily marked
incident pair. Its full radical fixes that line and the neighboring full
radical fixes the incident plane, with three disjoint conjugate lines. -/
theorem modelGeometry_of_fixed (σ : MulAut SL) (g : SL) (i : Bool)
    (h : fixedSpace (markedParabolic σ g i) ≠ ⊥) : ModelGeometry σ g i := by
  obtain ⟨k, ⟨hp, hq⟩|⟨hp, hq⟩⟩ := marked_pair σ g i
  · exact geometry_of_point_line σ g i k hp hq
  · exfalso
    apply h
    rw [hp, fixedSpace_conj, line_fixed_bot, Subgroup.map_bot]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.FixedGeometry.ValueConstruction
