module
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ParabolicAction.Basic

/-!
# The central pinned SL₂ and its prime-field order-three element

The genuine pinned central SL₂ remains faithful through elementary descent.
Its element u(1)v(1) has order three, including when q = 2. The specified
natural operator in the marked (lower, upper) root-string order sends
(x,y) to (x+y,x). This module does not yet identify that operator with
conjugation on the first root layer; the root-string equation is a separate
calculation, consumed explicitly in `ParabolicAction`.

Source: the pinned rank-one construction in GLS3 §§2.4 and 2.6
(`refs/KGroup/GLS3/chapter2.tex`), for the binary endpoint of
Aschbacher–Smith F.1.12(I)(4), printed pp.263–264 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
open Matrix
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.ConcreteBruhat
namespace Triality.Standard.Parabolics.CentralRootSquare

/-- The central root strings are ordered (lower weight, upper weight).
Thus the natural matrix is conjugated by the interchange matrix. -/
def centralLinear (P : Parameters) (A : SL(2, GaloisField P.prime P.exponent)) :
    (ExtensionField P × ExtensionField P) →ₗ[ExtensionField P]
      (ExtensionField P × ExtensionField P) :=
  LinearMap.prod
  ((baseFieldEmbedding P (A 1 1)) • LinearMap.fst _ _ _ +
    (baseFieldEmbedding P (A 1 0)) • LinearMap.snd _ _ _)
  ((baseFieldEmbedding P (A 0 1)) • LinearMap.fst _ _ _ +
    (baseFieldEmbedding P (A 0 0)) • LinearMap.snd _ _ _)

theorem centralLinear_apply (P : Parameters) (A : SL(2, GaloisField P.prime P.exponent))
    (v : ExtensionField P × ExtensionField P) :
    centralLinear P A v =
      (baseFieldEmbedding P (A 1 1) * v.1 + baseFieldEmbedding P (A 1 0) * v.2,
       baseFieldEmbedding P (A 0 1) * v.1 + baseFieldEmbedding P (A 0 0) * v.2) := rfl

/-- The genuine descended central SL₂ remains faithful. -/
theorem centralActor_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (centralActor P hp) := by
  intro A B h
  apply (pinnedRankOneMaps P hp).centralFixedEmbedding_injective
  have he := ElementaryCentralKernel.toCarrier_injective P hp (congrArg Subtype.val h)
  exact congrArg (elementaryInclusion P) he

/-- The prime-field element u(1)v(1) in the actual base-field SL₂. -/
def orderThreeMatrix (P : Parameters) : SL(2, GaloisField P.prime P.exponent) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) 1 *
    SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) (by decide) 1

theorem orderThreeMatrix_val (P : Parameters) (hp : P.prime = 2) :
    (orderThreeMatrix P).val = !![0,1;1,1] := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orderThreeMatrix, SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, Matrix.single_apply,
      CharTwo.add_self_eq_zero]

theorem orderThreeMatrix_cube (P : Parameters) (hp : P.prime = 2) :
    orderThreeMatrix P ^ 3 = 1 := by
  let : CharP (GaloisField P.prime P.exponent) 2 :=
    hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, orderThreeMatrix_val P hp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

/-- Actual order-three element of the central parabolic, including q = 2. -/
def orderThreeActor (P : Parameters) (hp : P.prime = 2) : parabolic P .central :=
  centralActor P hp (orderThreeMatrix P)

theorem orderOf_orderThreeActor (P : Parameters) (hp : P.prime = 2) :
    orderOf (orderThreeActor P hp) = 3 := by
  apply orderOf_eq_prime
  · exact (map_pow (centralActor P hp) (orderThreeMatrix P) 3).symm.trans
      ((congrArg (centralActor P hp) (orderThreeMatrix_cube P hp)).trans (map_one _))
  · intro h
    have he : orderThreeMatrix P = 1 := centralActor_injective P hp (h.trans (map_one _).symm)
    have hh := congrArg (fun A : SL(2, GaloisField P.prime P.exponent) => A 0 1) he
    have hv := congrFun₂ (orderThreeMatrix_val P hp) 0 1
    change orderThreeMatrix P 0 1 = 1 at hv
    simp [hv, SpecialLinearGroup.coe_one] at hh

/-- The displayed natural operator of u(1)v(1) sends (x,y) to (x+y,x). -/
theorem centralLinear_orderThree (P : Parameters) (hp : P.prime = 2)
    (v : ExtensionField P × ExtensionField P) :
    centralLinear P (orderThreeMatrix P) v = (v.1 + v.2, v.1) := by
  rw [centralLinear_apply]
  have hv (i j : Fin 2) := congrFun₂ (orderThreeMatrix_val P hp) i j
  change ((baseFieldEmbedding P) ((orderThreeMatrix P).val 1 1) * v.1 +
    (baseFieldEmbedding P) ((orderThreeMatrix P).val 1 0) * v.2,
    (baseFieldEmbedding P) ((orderThreeMatrix P).val 0 1) * v.1 +
    (baseFieldEmbedding P) ((orderThreeMatrix P).val 0 0) * v.2) = _
  rw [hv 1 1, hv 1 0, hv 0 1, hv 0 0]
  simp

end Triality.Standard.Parabolics.CentralRootSquare
end
