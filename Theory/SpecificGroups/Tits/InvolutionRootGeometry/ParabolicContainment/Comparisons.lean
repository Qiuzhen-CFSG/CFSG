module

public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.Geometry
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.MarkedParabolics

/-!
# Root-defined and Atlas parabolics on the marked Tits carrier

The existing marked embedding identifies the Atlas parabolics with the
intersections of the two full Ree parabolics and the derived subgroup.
Taking inverse images gives exactly `rootParabolic`, with the original
Parrott--Atlas marking retained. The local orders 10240 and 6144 prove
properness using the already established ambient order.

Source: Parrott (1972), pp.672,683--684; Aschbacher--Smith 16.1.4(1),
printed p.1171. These comparisons are used by the centralizer containment
proof, without introducing an abstract parabolic label.
-/

public section

open Subgroup
namespace Tits.InvolutionRootGeometry
open ExceptionalParabolics.FullRee

private theorem root_eq_comap {H : Subgroup Atlas1600Group}
    {s : ReeF4.LargeLocalSeeds.Side}
    (h : H.map atlasEmbedding = ReeF4.Parabolics.parabolic 0 s ⊓ commutator (ReeF4.Model 0)) :
    rootParabolic s = H.comap parrottFiniteImageEquiv.toMonoidHom := by
  ext x
  change embedding x ∈ ReeF4.Parabolics.parabolic 0 s ↔ parrottFiniteImageEquiv x ∈ H
  have he : atlasEmbedding (parrottFiniteImageEquiv x) = embedding x := by
    simp only [atlasEmbedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
  constructor
  · intro hx
    have hm : atlasEmbedding (parrottFiniteImageEquiv x) ∈ H.map atlasEmbedding := by
      rw [h, he]
      exact ⟨hx, embedding_range ▸ (show embedding x ∈ embedding.range from ⟨x, rfl⟩)⟩
    exact (mem_map_iff_mem atlasEmbedding_injective).mp hm
  · intro hx
    have hm := mem_map_of_mem atlasEmbedding hx
    rw [h, he] at hm
    exact hm.1

theorem rootParabolic_suzuki_eq : rootParabolic .suzuki =
    ExceptionalParabolics.first.comap parrottFiniteImageEquiv.toMonoidHom :=
  root_eq_comap (by simpa only [first_eq_parabolic] using atlas_first_map)

theorem rootParabolic_linear_eq : rootParabolic .linear =
    ExceptionalParabolics.second.comap parrottFiniteImageEquiv.toMonoidHom :=
  root_eq_comap (by simpa only [second_eq_parabolic] using atlas_second_map)

private theorem proper_comap {H : Subgroup Atlas1600Group}
    (hH : H < ⊤) : H.comap parrottFiniteImageEquiv.toMonoidHom < ⊤ := by
  simpa using parrottFiniteImageEquiv.comapSubgroup.strictMono hH

private theorem first_lt : ExceptionalParabolics.first < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  have hc := ExceptionalParabolics.first_card
  rw [h, card_top, atlas1600Group_card] at hc
  norm_num at hc

private theorem second_lt : ExceptionalParabolics.second < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  have hc := ExceptionalParabolics.second_card
  rw [h, card_top, atlas1600Group_card] at hc
  norm_num at hc

theorem rootParabolic_lt_top (s : ReeF4.LargeLocalSeeds.Side) : rootParabolic s < ⊤ := by
  cases s with
  | suzuki => rw [rootParabolic_suzuki_eq]; exact proper_comap first_lt
  | linear => rw [rootParabolic_linear_eq]; exact proper_comap second_lt

end Tits.InvolutionRootGeometry
