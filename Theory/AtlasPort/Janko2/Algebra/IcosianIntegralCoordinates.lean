/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianIntegralCoordinates.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianOrderBasis
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# IcosianIntegralCoordinates

The integral order is additively the space of four golden integers,
and hence a free abelian group of rank eight. Coefficient extraction and
synthesis give the additive and integer-linear equivalences.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianIntegralCoordinates.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0; imports and public module boundaries changed.
Definition bodies remain exposed for the coordinate calculations in consumers.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace Atlas.Algebra
open scoped Quaternion QuadraticAlgebra

def icosianIntegralCoefficients (x : icosianOrder) (i : Fin 4) : GoldenInteger :=
  Classical.choose (x.property i)

theorem icosianIntegralCoefficients_spec (x : icosianOrder) (i : Fin 4) :
    goldenIntegerToRational (icosianIntegralCoefficients x i)=icosianBasisCoefficients x.val i :=
  Classical.choose_spec (x.property i)

def icosianIntegralSynthesis (a : Fin 4 → GoldenInteger) : icosianOrder :=
  ⟨icosianBasisSynthesis (fun i => goldenIntegerToRational (a i)),
    (isIcosian_iff_synthesis _).mpr ⟨a,rfl⟩⟩

attribute [local irreducible] icosianBasisSynthesis icosianBasisCoefficients goldenIntegerToRational

def icosianIntegralEquiv : icosianOrder ≃+ (Fin 4 → GoldenInteger) where
  toFun := icosianIntegralCoefficients
  invFun := icosianIntegralSynthesis
  left_inv x := by
    apply Subtype.ext
    change icosianBasisSynthesis (fun i => goldenIntegerToRational (icosianIntegralCoefficients x i))=x.val
    have h : (fun i => goldenIntegerToRational (icosianIntegralCoefficients x i))=
        icosianBasisCoefficients x.val := funext (icosianIntegralCoefficients_spec x)
    rw [h,icosianBasisSynthesis_coefficients]
  right_inv a := by
    funext i
    apply goldenIntegerToRational_injective
    rw [icosianIntegralCoefficients_spec]
    exact congrFun (icosianBasisCoefficients_synthesis _) i
  map_add' x y := by
    funext i
    apply goldenIntegerToRational_injective
    simp only [Pi.add_apply, map_add,icosianIntegralCoefficients_spec,icosianIntegralCoefficients_spec,
      icosianIntegralCoefficients_spec]
    exact congrFun (icosianBasisCoefficients_add x.val y.val) i

def icosianIntegralLinearEquiv : icosianOrder ≃ₗ[ℤ] (Fin 4 → GoldenInteger) :=
  icosianIntegralEquiv.toIntLinearEquiv

instance icosianOrder_free : Module.Free ℤ icosianOrder :=
  Module.Free.of_equiv icosianIntegralLinearEquiv.symm

instance icosianOrder_finite : Module.Finite ℤ icosianOrder :=
  Module.Finite.equiv icosianIntegralLinearEquiv.symm

theorem icosianOrder_rank : Module.finrank ℤ icosianOrder=8 := by
  rw [icosianIntegralLinearEquiv.finrank_eq,Module.finrank_pi_fintype]
  simp [QuadraticAlgebra.finrank_eq_two]

end Atlas.Algebra
