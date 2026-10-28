/-
Uses Gerald Höhn's retained ATLAS icosian coordinates, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Distributed under the ATLAS
Research and Attribution License 1.0; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Tetrahedral.Outer.ActionSpec
/-!
# The non-inner scalar action of the concrete Leech twist

Golden conjugation with the rotation i ↦ -i, j ↦ k, k ↦ j preserves
both the integral icosian order and its norm-one group. Integrality follows
from the retained integral twist formula by multiplication by τ−1. The
resulting involution preserves the exact two-sign reduction kernel, so it
descends to the existing scalar projective model and then to its actual A₅.
Inverse right multiplication intertwines this action with the specified
lattice twist, first in Co₀ and then through the literal Co₁ quotient map.

For non-innerness, the real coefficient of i times the second icosian
generator is (τ−1)/2, whereas its semilinear image has real coefficient
−τ/2. Ordinary quaternion conjugation preserves the real coefficient.
The exact two-sign kernel makes these unequal coefficients, even up to
sign, an obstruction to every inner automorphism of the projective group.

This discharges the scalar-action premise of the tetrahedral outer-actor
construction. The source applications are Aschbacher, *Sporadic Groups*
(1994), 48.3(3), pp.268–269, and the normalizer step of 49.5, p.284.
The cubic correction and final reference action remain in `Outer`.
-/

open Atlas.Algebra Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.Outer.ScalarAction
open Outer
open scoped Quaternion QuadraticAlgebra
set_option backward.isDefEq.respectTransparency false
noncomputable section

private def sigma : IcosianQuaternion ≃+* IcosianQuaternion where
  toFun := sigmaQuaternion
  invFun := sigmaQuaternion
  left_inv q := by ext <;> simp [sigmaQuaternion]
  right_inv q := by ext <;> simp [sigmaQuaternion]
  map_add' q r := by ext <;> simp [sigmaQuaternion] <;> ring
  map_mul' q r := by
    ext <;> simp [sigmaQuaternion, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem sigma_star (q : IcosianQuaternion) : sigma (star q) = star (sigma q) := by
  ext <;> simp [sigma, sigmaQuaternion] <;> ring

private theorem sigma_integral (q : IcosianQuaternion) (hq : IsIcosian q) : IsIcosian (sigma q) := by
  obtain ⟨a, ha⟩ := (isIcosian_iff_synthesis q).mp hq
  have ht : IsIcosian (twistQuaternion q) := by
    rw [← ha]
    exact (twist_synthesis a) ▸ (icosianIntegralSynthesis (twistCoefficients a)).property
  have hu : (goldenTau - 1 : IcosianQuaternion) ∈ icosianOrder :=
    icosianOrder.sub_mem (icosianGeneratedOrder_le icosianTau_mem_generated) icosianOrder.one_mem
  have he : sigma q = (goldenTau - 1 : IcosianQuaternion) * twistQuaternion q := by
    ext <;> simp [sigma, sigmaQuaternion, twistQuaternion, rotate,
      goldenTau, QuadraticAlgebra.omega] <;> ring
  rw [he]
  exact icosianOrder.mul_mem hu ht

private def sigmaUnit (u : icosianNormOneGroup) : icosianNormOneGroup :=
  ⟨⟨sigma u.val.val, by
    change star (sigma u.val.val) * sigma u.val.val = 1 ∧
      sigma u.val.val * star (sigma u.val.val) = 1
    have h₁ : star u.val.val * u.val.val = 1 := Unitary.coe_star_mul_self u.val
    have h₂ : u.val.val * star u.val.val = 1 := Unitary.coe_mul_star_self u.val
    rw [← sigma_star, ← map_mul, ← map_mul, h₁, h₂, map_one]
    exact ⟨rfl, rfl⟩⟩, sigma_integral _ u.property⟩

private def sigmaAut : MulAut icosianNormOneGroup where
  toFun := sigmaUnit
  invFun := sigmaUnit
  left_inv u := by
    apply icosianNormOne_value_injective
    exact sigma.left_inv u.val.val
  right_inv u := by
    apply icosianNormOne_value_injective
    exact sigma.right_inv u.val.val
  map_mul' u v := by
    apply icosianNormOne_value_injective
    exact map_mul sigma u.val.val v.val.val

private theorem sigmaAut_minusOne : sigmaAut icosianNormOneMinusOne = icosianNormOneMinusOne := by
  apply icosianNormOne_value_injective
  change sigma (-1) = -1
  simp

private theorem sigmaAut_kernel : icosianNormOneReduction.ker.map sigmaAut.toMonoidHom =
    icosianNormOneReduction.ker := by
  ext u
  rw [Subgroup.mem_map, icosianNormOneReduction_kernel_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rcases (icosianNormOneReduction_kernel_iff v).mp hv with rfl | rfl
    · exact Or.inl (map_one sigmaAut)
    · exact Or.inr sigmaAut_minusOne
  · rintro (rfl | rfl)
    · exact ⟨1, (icosianNormOneReduction_kernel_iff _).mpr (Or.inl rfl), map_one _⟩
    · exact ⟨icosianNormOneMinusOne,
        (icosianNormOneReduction_kernel_iff _).mpr (Or.inr rfl), sigmaAut_minusOne⟩

private def projectiveAut : MulAut IcosianScalarProjectiveModel :=
  QuotientGroup.congr _ _ sigmaAut sigmaAut_kernel

private def alternatingAut : MulAut (alternatingGroup (Fin 5)) :=
  (icosianScalarProjectiveAlternating.symm.trans projectiveAut).trans
    icosianScalarProjectiveAlternating

private theorem twist_mul_right (q r : IcosianQuaternion) :
    twistQuaternion (q * r) = twistQuaternion q * sigma r := by
  ext <;> simp [twistQuaternion, rotate, sigma, sigmaQuaternion,
    Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem twist_representation (u : icosianNormOneGroup) :
    twist * icosianScalarRepresentation u = icosianScalarRepresentation (sigmaAut u) * twist := by
  apply LinearEquiv.ext
  intro v
  funext i
  change twistQuaternion (v i * (u⁻¹).val.val) =
    twistQuaternion (v i) * ((sigmaAut u)⁻¹).val.val
  rw [twist_mul_right]
  exact congrArg (fun q => twistQuaternion (v i) * q)
    (congrArg (fun w : icosianNormOneGroup => w.val.val) (map_inv sigmaAut u))

private theorem twist_co0 (u : icosianNormOneGroup) :
    MulAut.conj twistCo0 (icosianScalarsToCo0 u) = icosianScalarsToCo0 (sigmaAut u) := by
  apply fullIsometryEquiv.injective
  change fullIsometryEquiv (twistCo0 * icosianScalarsToCo0 u * twistCo0⁻¹) = _
  rw [map_mul, map_mul, map_inv, twistCo0_extension,
    icosianScalarsToCo0_extension, icosianScalarsToCo0_extension]
  apply Subtype.ext
  change icosianAutomorphismComparison twist *
    icosianAutomorphismComparison (icosianScalarRepresentation u) *
    (icosianAutomorphismComparison twist)⁻¹ =
    icosianAutomorphismComparison (icosianScalarRepresentation (sigmaAut u))
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg icosianAutomorphismComparison
  exact (mul_inv_eq_iff_eq_mul).mpr (twist_representation u)

private theorem twist_projective (x : IcosianScalarProjectiveModel) :
    MulAut.conj twistCo1 (icosianScalarProjectiveToCo1 x) =
      icosianScalarProjectiveToCo1 (projectiveAut x) := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective icosianNormOneReduction.ker x
  change leechCentralProjection twistCo0 * leechCentralProjection (icosianScalarsToCo0 u) *
    (leechCentralProjection twistCo0)⁻¹ = leechCentralProjection (icosianScalarsToCo0 (sigmaAut u))
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg leechCentralProjection (twist_co0 u)

private theorem twist_alternating (a : alternatingGroup (Fin 5)) :
    MulAut.conj twistCo1 (scalarFive a) = scalarFive (alternatingAut a) := by
  change MulAut.conj twistCo1
    (icosianScalarProjectiveToCo1 (icosianScalarProjectiveAlternating.symm a)) =
    icosianScalarProjectiveToCo1 (icosianScalarProjectiveAlternating.symm
      (icosianScalarProjectiveAlternating
        (projectiveAut (icosianScalarProjectiveAlternating.symm a))))
  rw [MulEquiv.symm_apply_apply]
  exact twist_projective _

private theorem quotient_eq_sign (u v : icosianNormOneGroup)
    (h : (QuotientGroup.mk u : IcosianScalarProjectiveModel) = QuotientGroup.mk v) :
    u.val.val = v.val.val ∨ u.val.val = -v.val.val := by
  have hk := (icosianNormOneReduction_kernel_iff (u / v)).mp
    (QuotientGroup.eq_iff_div_mem.mp h)
  rcases hk with hk | hk
  · exact Or.inl (congrArg (fun w : icosianNormOneGroup => w.val.val) (div_eq_one.mp hk))
  · right
    have he := congrArg (fun w : icosianNormOneGroup => w.val.val) (eq_mul_of_div_eq hk)
    change u.val.val = (-1) * v.val.val at he
    simpa only [neg_one_mul] using he

private theorem real_mul_comm (q r : IcosianQuaternion) : (q * r).re = (r * q).re := by
  simp only [Quaternion.re_mul]
  ring

private theorem real_conj (u v : icosianNormOneGroup) :
    (u * v * u⁻¹).val.val.re = v.val.val.re := by
  calc
    _ = (u⁻¹ * (u * v)).val.val.re := real_mul_comm _ _
    _ = _ := by rw [inv_mul_cancel_left]

private theorem projective_not_inner (x : IcosianScalarProjectiveModel) :
    projectiveAut ≠ MulAut.conj x := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective icosianNormOneReduction.ker x
  intro h
  let q := icosianScalarI * icosianScalarGenerator
  have he := DFunLike.congr_fun h (QuotientGroup.mk q)
  change (QuotientGroup.mk (sigmaAut q) : IcosianScalarProjectiveModel) =
    QuotientGroup.mk (u * q * u⁻¹) at he
  have hr := congrArg QuadraticAlgebra.re (real_conj u q)
  rcases quotient_eq_sign _ _ he with he | he
  · have he' := congrArg (fun w : IcosianQuaternion => w.re.re) he
    rw [hr] at he'
    norm_num [q, sigmaAut, sigmaUnit, sigma, sigmaQuaternion,
      icosianScalarI, icosianScalarGenerator, icosianNormOneGroupOf,
      icosianI, icosianGenerator] at he'
  · have he' := congrArg (fun w : IcosianQuaternion => w.re.re) he
    simp only [Quaternion.re_neg, QuadraticAlgebra.re_neg] at he'
    rw [hr] at he'
    norm_num [q, sigmaAut, sigmaUnit, sigma, sigmaQuaternion,
      icosianScalarI, icosianScalarGenerator, icosianNormOneGroupOf,
      icosianI, icosianGenerator] at he'

private theorem alternating_not_inner (a : alternatingGroup (Fin 5)) :
    alternatingAut ≠ MulAut.conj a := by
  intro h
  apply projective_not_inner (icosianScalarProjectiveAlternating.symm a)
  apply MulEquiv.ext
  intro x
  apply icosianScalarProjectiveAlternating.injective
  have he := DFunLike.congr_fun h (icosianScalarProjectiveAlternating x)
  simpa [alternatingAut, MulAut.conj_apply, map_mul, map_inv] using he

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.Outer.ScalarAction

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
/-- The specified semilinear lattice actor acts non-innerly on the actual
scalar A₅, with no additional geometric or model hypotheses. -/
public theorem twistScalarOuterAction : TwistScalarOuterAction :=
  ⟨Outer.ScalarAction.alternatingAut, Outer.ScalarAction.twist_alternating,
    Outer.ScalarAction.alternating_not_inner⟩
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
