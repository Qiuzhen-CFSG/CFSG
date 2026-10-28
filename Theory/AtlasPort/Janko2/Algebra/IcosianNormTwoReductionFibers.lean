/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianNormTwoReductionFibers.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianNormTwoMatrixFibers
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneReductionSurjective
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# IcosianNormTwoReductionFibers

Each nonzero singular matrix over F₄ has exactly eight integral
norm-two lifts. Reduction-compatible coordinates separate four matrix
parameters from the two-element norm-one reduction kernel.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianNormTwoReductionFibers.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Algebra
open scoped Matrix Quaternion QuadraticAlgebra

theorem icosianNormTwo_reduction_ne_zero (x : IcosianNormTwo) :
    icosianModuloTwo x.val ≠ 0 := by
  intro hz
  obtain ⟨y,hy⟩ := (icosianModuloTwo_eq_zero_iff_two_mul x.val).mp hz
  have hn := x.property
  have he : x.val.val = 2*y.val := congrArg Subtype.val hy
  rw [he,icosianNorm_mul,icosianNorm_two,← icosianIntegralNorm_spec] at hn
  have hr := congrArg QuadraticAlgebra.re hn
  norm_num [goldenIntegerToRational] at hr
  have hi : 4*(icosianIntegralNorm y).re = (2 : ℤ) := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    exact hr
  omega

theorem icosianNormOneReduction_fiber_card (a : IcosianSpecialLinear) :
    Nat.card {u : icosianNormOneGroup // icosianNormOneReduction u = a} = 2 := by
  change Nat.card (icosianNormOneReduction ⁻¹' {a}) = 2
  rw [Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective
    icosianNormOneReduction_surjective a),icosianNormOneReduction_kernel_card]

/-- Coordinates on the norm-one group over its actual reduction, with its
proved two-element kernel retained separately. -/
def icosianNormOneReductionCoordinates :
    icosianNormOneGroup ≃ IcosianSpecialLinear × icosianNormOneReduction.ker :=
  (Equiv.sigmaPreimageEquiv icosianNormOneReduction).symm.trans
    ((Equiv.sigmaCongrRight
      (MonoidHom.fiberEquivKerOfSurjective icosianNormOneReduction_surjective)).trans
        (Equiv.sigmaEquivProd _ _))

theorem icosianNormOneReductionCoordinates_fst (u : icosianNormOneGroup) :
    (icosianNormOneReductionCoordinates u).1 = icosianNormOneReduction u := rfl

/-- The reduction-compatible coordinates of every norm-two icosian. -/
def icosianNormTwoReductionCoordinates : IcosianNormTwo ≃
    (Fin 5 × IcosianSpecialLinear) × icosianNormOneReduction.ker :=
  icosianNormTwoEquiv.trans
    ((Equiv.prodCongr (Equiv.refl _) icosianNormOneReductionCoordinates).trans
      (Equiv.prodAssoc _ _ _).symm)

theorem icosianNormTwoReductionCoordinates_matrix (x : IcosianNormTwo) :
    icosianModuloTwo x.val =
      icosianNormTwoRepresentativeMatrix (icosianNormTwoReductionCoordinates x).1.1 *
        ((icosianNormTwoReductionCoordinates x).1.2 : IcosianMatrix) := by
  have hx := congrArg (fun y : IcosianNormTwo => icosianModuloTwo y.val)
    (icosianNormTwoEquiv.symm_apply_apply x)
  change icosianModuloTwo
    (icosianNormTwoRepresentative (icosianNormTwoEquiv x).1 *
      icosianNormOneToOrder (icosianNormTwoEquiv x).2) = icosianModuloTwo x.val at hx
  rw [map_mul,icosianNormTwoRepresentative_reduction] at hx
  exact hx.symm


def icosianNormTwoReductionFiberEquiv (m : IcosianMatrix) :
    {x : IcosianNormTwo // icosianModuloTwo x.val = m} ≃
      IcosianNormTwoMatrixParameters m × icosianNormOneReduction.ker where
  toFun x := ⟨⟨(icosianNormTwoReductionCoordinates x.val).1, by
    rw [← icosianNormTwoReductionCoordinates_matrix]
    exact x.property⟩,(icosianNormTwoReductionCoordinates x.val).2⟩
  invFun p := ⟨icosianNormTwoReductionCoordinates.symm (p.1.val,p.2), by
    rw [icosianNormTwoReductionCoordinates_matrix,
      icosianNormTwoReductionCoordinates.apply_symm_apply]
    exact p.1.property⟩
  left_inv x := by
    apply Subtype.ext
    exact icosianNormTwoReductionCoordinates.symm_apply_apply x.val
  right_inv p := by
    rcases p with ⟨⟨p,hp⟩,k⟩
    simp

theorem icosianNormTwoReduction_fiber_card (m : IcosianMatrix)
    (hm : Matrix.det m = 0) (hne : m ≠ 0) :
    Nat.card {x : IcosianNormTwo // icosianModuloTwo x.val = m} = 8 := by
  rw [Nat.card_congr (icosianNormTwoReductionFiberEquiv m),Nat.card_prod,
    icosianNormOneReduction_kernel_card,Nat.card_eq_fintype_card,
    icosianNormTwoMatrixParameters_count m hm hne]

theorem icosianNormTwoReduction_surjective_rank_one (m : IcosianMatrix)
    (hm : Matrix.det m = 0) (hne : m ≠ 0) :
    ∃ x : IcosianNormTwo, icosianModuloTwo x.val = m := by
  have hp : 0 < Nat.card {x : IcosianNormTwo // icosianModuloTwo x.val = m} := by
    rw [icosianNormTwoReduction_fiber_card m hm hne]
    decide
  obtain ⟨x⟩ := (Nat.card_pos_iff.mp hp).1
  exact ⟨x.val,x.property⟩

end Atlas.Algebra
