module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.MarkingExistence.CalibratedCharts.CentralLifting.RootRigidity
public import Theory.AlgebraicGroup.RootSubgroups.SL2RootCurves
public import Theory.AlgebraicGroup.Instance.PSL
/-!
Lifted standard SL₂ root curves lie in the abstract derived subgroup of a
reductive source. This holds for any target group and any algebraic morphism
from the actual SL₂ variety to that target.

Choose a scalar outside `{0, 1, -1}` and lift the image of the corresponding
SL₂ diagonal point through the surjective central quotient. Direct matrix
multiplication gives nontrivial scalar conjugation of each projected root
curve. `RootRigidity` lifts this identity upstairs and writes each root
point as a commutator. Its finite-kernel theorem can therefore be applied
with the abstract derived subgroup, even when the full central kernel is
positive dimensional, as for GL₂ → PGL₂.

For the central PGL₂-cover consumer, take `p = pgl2StandardProjection`.
The upper/lower projection identities are the literal definitions of the
standard PGL₂ curves. These results discharge the root-membership premises
of the finite-kernel chart construction; they do not construct that lift.

Sources: Borel, §§13.13--13.14 and 13.18; GLS3, §§1.9--1.12.
-/

open Theory.AlgebraicGroup Matrix

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {Y Q : Variety k} [AlgebraicGroup Y] [AlgebraicGroup Q]

private noncomputable def sl2DiagonalPoint (a : k) (ha : a ≠ 0) : Variety.Point (slVariety k 2) :=
  (slPointMulEquiv (k := k) 2).symm (SpecialLinearGroup.diag2 a ha)

private theorem sl2DiagonalPoint_upper (a : k) (ha : a ≠ 0) (t : k) :
    sl2DiagonalPoint a ha * standardSL2UpperMorphism.onPoints (kPlusPoint t) * (sl2DiagonalPoint a ha)⁻¹ =
      standardSL2UpperMorphism.onPoints (kPlusPoint (a*a*t)) := by
  apply (slPointMulEquiv (k := k) 2).injective
  simp only [map_mul, map_inv, sl2DiagonalPoint, MulEquiv.apply_symm_apply]
  simp only [slPointMulEquiv_apply, standardSL2UpperMorphism_kPlusPoint,
    typeASLRootPoint, Equiv.apply_symm_apply]
  rw [SpecialLinearGroup.diag2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.diag2_coe',
      SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha,
      standardSL2UpperRootIndex, Matrix.vecMul, dotProduct,
      Matrix.single_apply, Matrix.one_apply]
  all_goals ring

private theorem sl2DiagonalPoint_lower (a : k) (ha : a ≠ 0) (t : k) :
    sl2DiagonalPoint a⁻¹ (inv_ne_zero ha) * standardSL2LowerMorphism.onPoints (kPlusPoint t) *
      (sl2DiagonalPoint a⁻¹ (inv_ne_zero ha))⁻¹ =
      standardSL2LowerMorphism.onPoints (kPlusPoint (a*a*t)) := by
  apply (slPointMulEquiv (k := k) 2).injective
  simp only [map_mul, map_inv, sl2DiagonalPoint, MulEquiv.apply_symm_apply]
  simp only [slPointMulEquiv_apply, standardSL2LowerMorphism_kPlusPoint,
    typeASLRootPoint, Equiv.apply_symm_apply]
  rw [SpecialLinearGroup.diag2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.diag2_coe',
      SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ha,
      standardSL2LowerRootIndex, Matrix.vecMul, dotProduct,
      Matrix.single_apply, Matrix.one_apply]
  all_goals ring

private theorem exists_scalar : ∃ a : k, a ≠ 0 ∧ a*a ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset k)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ⟨a, ha.1, fun h => (mul_self_eq_one_iff.mp h).elim ha.2.1 ha.2.2⟩

/-- A regular lift of the projected standard upper curve lies in the
abstract derived subgroup of the reductive source. -/
public theorem upper_mem_commutator_of_central_sl2_lift
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hqsurj : Function.Surjective q.onPoints)
    (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (p : Morphism (slVariety k 2) Q) (u : Morphism (KPlus k) Y)
    (hu : q.comp u = p.comp standardSL2UpperMorphism) (s : Variety.Point (KPlus k)) :
    u.onPoints s ∈ _root_.commutator (Variety.Point Y) := by
  obtain ⟨a, ha, ha2⟩ := exists_scalar (k := k)
  obtain ⟨y, hy⟩ := hqsurj (p.onPoints (sl2DiagonalPoint a ha))
  have hp (t : k) : q.onPoints (u.onPoints (kPlusPoint t)) =
      p.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint t)) :=
    congrArg (fun m : Morphism (KPlus k) Q => m.onPoints (kPlusPoint t)) hu
  obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
  apply root_mem_commutator_of_quotient_scaling hY q hq u y (a*a) ha2
  intro b
  calc
    _ = p.onPoints (sl2DiagonalPoint a ha * standardSL2UpperMorphism.onPoints (kPlusPoint b) *
        (sl2DiagonalPoint a ha)⁻¹) := by simp only [map_mul, map_inv, hp, hy]
    _ = p.onPoints (standardSL2UpperMorphism.onPoints (kPlusPoint (a*a*b))) := by
      rw [sl2DiagonalPoint_upper]
    _ = _ := (hp _).symm

/-- A regular lift of the projected standard lower curve lies in the
abstract derived subgroup of the reductive source. -/
public theorem lower_mem_commutator_of_central_sl2_lift
    (hY : IsReductiveAlgebraicGroup Y)
    (q : Morphism Y Q) (hqsurj : Function.Surjective q.onPoints)
    (hq : q.kernel ≤ Subgroup.center (Variety.Point Y))
    (p : Morphism (slVariety k 2) Q) (v : Morphism (KPlus k) Y)
    (hv : q.comp v = p.comp standardSL2LowerMorphism) (s : Variety.Point (KPlus k)) :
    v.onPoints s ∈ _root_.commutator (Variety.Point Y) := by
  obtain ⟨a, ha, ha2⟩ := exists_scalar (k := k)
  obtain ⟨y, hy⟩ := hqsurj (p.onPoints (sl2DiagonalPoint a⁻¹ (inv_ne_zero ha)))
  have hp (t : k) : q.onPoints (v.onPoints (kPlusPoint t)) =
      p.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint t)) :=
    congrArg (fun m : Morphism (KPlus k) Q => m.onPoints (kPlusPoint t)) hv
  obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
  apply root_mem_commutator_of_quotient_scaling hY q hq v y (a*a) ha2
  intro b
  calc
    _ = p.onPoints (sl2DiagonalPoint a⁻¹ (inv_ne_zero ha) *
        standardSL2LowerMorphism.onPoints (kPlusPoint b) *
        (sl2DiagonalPoint a⁻¹ (inv_ne_zero ha))⁻¹) := by simp only [map_mul, map_inv, hp, hy]
    _ = p.onPoints (standardSL2LowerMorphism.onPoints (kPlusPoint (a*a*b))) := by
      rw [sl2DiagonalPoint_lower a ha b]
    _ = _ := (hp _).symm

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.CalibratedCharts.CentralLifting
