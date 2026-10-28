module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution

/-!
# Irreducible M₁₁ modules annihilated by the eleven-norm

The certified cube of the reference annihilator lies in the two-sided
order-eleven norm ideal. On an arbitrary irreducible module annihilated by
that norm, the reference annihilator therefore acts as zero. The full matrix
image of the point representation identifies the module with the actual
binary ten-dimensional point module. Neither a degree bound nor faithfulness
is needed. Vanishing of the eleven-fixed space implies norm annihilation.

This supplies the norm-zero branch of the point-restriction reduction in
`M12DegreeGap`. The nonzero-norm branch is a separate obligation.
Source context: James, *The modular characters of the Mathieu groups*,
J. Algebra 27 (1973), 57–111; Aschbacher–Smith G.7.3(2), printed p.348.
The finite certificate is proved in `M12Recognition`; no character-table
exhaustivity assertion is assumed here.
-/

public section
open scoped BigOperators MonoidAlgebra
namespace Representation.MathieuSmall.M12DegreeGap
open Sporadic.Mathieu M12Recognition
open M12Recognition.PointClassification.NormalizedInvolution
open Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem elevenNorm_eq_zero_of_fixedSpace_eq_bot
    (τ : Representation (ZMod 2) M11 V)
    (hz : fixedSpace τ (Subgroup.zpowers m11Sylow11Generator) = ⊥) :
    τ.asAlgebraHom elevenNorm = 0 := by
  have hp : (τ m11Sylow11Generator) ^ 11 = 1 := by
    have hc : m11Sylow11Generator ^ 11 = 1 := by
      simpa only [m11Sylow11Generator_order] using pow_orderOf_eq_one m11Sylow11Generator
    rw [← map_pow, hc, map_one]
  have h := mul_geom_sum (τ m11Sylow11Generator) 11
  rw [hp, sub_self, sub_mul, one_mul, sub_eq_zero] at h
  have hn : τ.asAlgebraHom elevenNorm =
      ∑ i ∈ Finset.range 11, (τ m11Sylow11Generator) ^ i := by
    simp [elevenNorm, map_pow]
  rw [hn]
  apply LinearMap.ext
  intro v
  have hv : (∑ i ∈ Finset.range 11, (τ m11Sylow11Generator) ^ i) v ∈
      fixedSpace τ (Subgroup.zpowers m11Sylow11Generator) := by
    rw [mem_fixedSpace_zpowers_iff]
    exact LinearMap.congr_fun h v
  rwa [hz, Submodule.mem_bot] at hv

theorem equiv_point_of_elevenNorm_eq_zero
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (hz : τ.asAlgebraHom elevenNorm = 0) :
    Nonempty (τ.Equiv pointRepresentation) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial τ
  let : pointRepresentation.IsIrreducible :=
    PointClassification.pointRepresentation_isIrreducible
  have hI : elevenIdeal ≤ TwoSidedIdeal.ker τ.asAlgebraHom := by
    apply TwoSidedIdeal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hz
  have hK : referenceKernel ≤ TwoSidedIdeal.ker τ.asAlgebraHom :=
    kernel_le_of_cube τ referenceKernel (fun x hx y hy z hz =>
      hI (referenceKernel_cube_le_elevenIdeal x hx y hy z hz))
  obtain ⟨e⟩ := equiv_of_kernel_le pointRepresentation τ
    pointRepresentation_asAlgebraHom_surjective hK
  exact ⟨e.symm⟩

theorem finrank_eq_ten_of_elevenNorm_eq_zero
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (hz : τ.asAlgebraHom elevenNorm = 0) : Module.finrank (ZMod 2) V = 10 := by
  obtain ⟨e⟩ := equiv_point_of_elevenNorm_eq_zero τ hz
  exact e.toLinearEquiv.finrank_eq.trans finrank_m12Heart

theorem finrank_eq_ten_of_eleven_fixedSpace_eq_bot
    (τ : Representation (ZMod 2) M11 V) [τ.IsIrreducible]
    (hz : fixedSpace τ (Subgroup.zpowers m11Sylow11Generator) = ⊥) :
    Module.finrank (ZMod 2) V = 10 :=
  finrank_eq_ten_of_elevenNorm_eq_zero τ (elevenNorm_eq_zero_of_fixedSpace_eq_bot τ hz)

end Representation.MathieuSmall.M12DegreeGap
