module

public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Centralizers
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.AutomorphismSignalizers.Inner
public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.AutomorphismSignalizers.PointwiseStabilizer

/-!
# Two-signalizers of parabolic radicals in Aut(PSL₃(5))

The inner two-signalizer theorem first kills the intersection of a normalized
two-subgroup U with Inn(PSL₃(5)). Commutators of U with the radical belong to
that intersection, so U fixes the radical pointwise. The matrix calculation
in `PointwiseStabilizer` makes every such automorphism inner, and the same
intersection calculation then kills U. This includes outer automorphisms and
uses normalization of U, with no model-vanishing or recognition premise.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof of 1.3.8, printed p.513,
the assertion I(P*, 2) = 1 for a maximal parabolic radical in L₃(5).
-/

public section

open scoped MatrixGroups
open Subgroup Matrix.PSL3.RootPlaneGeometry
namespace Matrix.PSL3.RadicalParabolicTwoSignalizers
local notation "𝔽" => ZMod 5

private theorem conj_model_injective :
    Function.Injective (MulAut.conj : Model →* MulAut Model) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  have hc : x ∈ center Model := by
    rw [mem_center_iff]
    intro y
    have he := congrArg (fun α : MulAut Model => α y) hx
    change x * y * x⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  rwa [center_eq_bot] at hc

/-- A two-subgroup normalized by a parabolic radical is trivial even in the full
automorphism group. -/
theorem automorphism_normalized_twoSubgroup_eq_bot
    (point : Bool) (U : Subgroup (MulAut Model))
    (hU : IsPGroup 2 U)
    (hn : (rootPlane 𝔽 point).map (MulAut.conj : Model →* MulAut Model) ≤
      normalizer (U : Set (MulAut Model))) : U = ⊥ := by
  let S := U.comap (MulAut.conj : Model →* MulAut Model)
  have hS : IsPGroup 2 S := hU.comap_of_injective _ conj_model_injective
  have hnS : rootPlane 𝔽 point ≤ normalizer (S : Set Model) := by
    rw [le_normalizer_iff]
    intro a ha x hx
    change MulAut.conj (a * x * a⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp (hn (mem_map_of_mem _ ha)) _).mp hx
  have hSbot := normalized_twoSubgroup_eq_bot point S hS hnS
  have hfix (α : MulAut Model) (hα : α ∈ U) : ∀ a ∈ rootPlane 𝔽 point, α a = a := by
    intro a ha
    have hm : MulAut.conj (a * (α a)⁻¹) =
        MulAut.conj a * α * (MulAut.conj a)⁻¹ * α⁻¹ := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have he : a * (α a)⁻¹ ∈ S := by
      change MulAut.conj (a * (α a)⁻¹) ∈ U
      rw [hm]
      exact U.mul_mem
        ((mem_normalizer_iff.mp (hn (mem_map_of_mem _ ha)) _).mp hα)
        (U.inv_mem hα)
    have : a * (α a)⁻¹ = 1 := mem_bot.mp (hSbot ▸ he)
    exact (mul_inv_eq_one.mp this).symm
  apply eq_bot_iff.mpr
  intro α hα
  obtain ⟨g, rfl⟩ := fixes_rootPlane_is_inner point α (hfix α hα)
  have hg : g ∈ S := hα
  have hg1 : g = 1 := mem_bot.mp (hSbot ▸ hg)
  simp only [hg1, map_one, mem_bot]

end Matrix.PSL3.RadicalParabolicTwoSignalizers
