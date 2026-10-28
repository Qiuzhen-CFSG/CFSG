module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentStabilizer

/-!
# Generation of the cubic component stabilizer

The two original incidence stabilizers N(W) and N(V) generate exactly
the stabilizer of W's connected component. An adjacent point is obtained
by first selecting its line using N(W), then selecting the point on that
line using N(V). Induction along paths supplies the generation statement.

This is the actual subgroup to which the local amalgam in Asc9445.11
applies. The equality with G is not assumed or asserted here.
Source: Aschbacher, *Sporadic Groups* (1994),45.10–45.11, pp.247–249.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

theorem neighbor_conjugator_in_normalizers {U : Subgroup G} (hU : U ∈ c.neighbors c.W) :
    ∃ g ∈ normalizer (c.W : Set G) ⊔ normalizer (c.V : Set G), U = c.W.conjBy g := by
  obtain ⟨hUp, -, L, hL, hWL, hUL⟩ := hU
  obtain ⟨k, hk, rfl⟩ := c.linesThrough_base ▸ (show L ∈ c.linesThrough c.W from ⟨hL, hWL⟩)
  have hUk : U.conjBy k⁻¹ ≤ c.V := by
    have hh := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hUL
    change U.conjBy k⁻¹ ≤ (c.V.conjBy k).conjBy k⁻¹ at hh
    simpa only [conjBy_inv] using hh
  have hp : U.conjBy k⁻¹ ∈ c.kernelLines := c.pointsOn_base ▸
    ⟨c.point_conjugate_mem hUp k⁻¹, hUk⟩
  obtain ⟨n, hn, he⟩ := (c.mem_kernelLines_iff _).mp hp
  refine ⟨k * n, mul_mem_sup hk hn, ?_⟩
  have hh := congrArg (fun A : Subgroup G => A.conjBy k) he
  change (U.conjBy k⁻¹).conjBy k = (c.W.conjBy n).conjBy k at hh
  simpa only [conjBy_inv', conjBy_conjBy, mul_inv_cancel, conjBy_one] using hh

theorem component_conjugator_in_normalizers {U : c.points}
    (hU : c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U) :
    ∃ g ∈ normalizer (c.W : Set G) ⊔ normalizer (c.V : Set G), U.val = c.W.conjBy g := by
  have hr := (c.collinearity.reachable_iff_reflTransGen _ _).mp hU
  clear hU
  induction hr with
  | refl => exact ⟨1, one_mem _, (conjBy_one _).symm⟩
  | @tail U U' _ ha ih =>
    obtain ⟨g, hg, he⟩ := ih
    have hn := c.neighbor_conjugate ha g⁻¹
    change U'.val.conjBy g⁻¹ ∈ c.neighbors (U.val.conjBy g⁻¹) at hn
    rw [he, conjBy_inv] at hn
    obtain ⟨k, hk, he'⟩ := c.neighbor_conjugator_in_normalizers hn
    refine ⟨g * k, mul_mem hg hk, ?_⟩
    have hh := congrArg (fun A : Subgroup G => A.conjBy g) he'
    simpa only [conjBy_inv', conjBy_conjBy, mul_inv_cancel, conjBy_one] using hh

/-- The actual incidence amalgam generates exactly the source component stabilizer. -/
theorem componentStabilizer_eq_normalizers_sup : c.componentStabilizer =
    normalizer (c.W : Set G) ⊔ normalizer (c.V : Set G) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a, ha, he⟩ := c.component_conjugator_in_normalizers hg
    change c.W.conjBy g = c.W.conjBy a at he
    have hk : a⁻¹ * g ∈ normalizer (c.W : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change c.W.conjBy (a⁻¹ * g) = c.W
      rw [conjBy_mul, he, conjBy_inv]
    have hh := (normalizer (c.W : Set G) ⊔ normalizer (c.V : Set G)).mul_mem ha (mem_sup_left hk)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le c.point_normalizer_le_componentStabilizer c.kernel_normalizer_le_componentStabilizer

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
