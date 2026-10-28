module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.PairModel

/-!
# The two types of cubic monomials on the signed pair model

The triangle sum has coefficient four. The mixed sum has coefficient minus
four on ordered coordinate pairs, hence minus eight on an unordered pair.
The first is invariant because every natural coordinate sign occurs twice;
the second is invariant because the three axis signs multiply to one.

These are the coefficients computed in Aschbacher, *Sporadic Groups*, 29.11,
printed pp. 159–160. This module proves their invariance on the actual signed
pair representation. Identifying this explicit form with the restriction of
`griessBeta` is a separate source coefficient calculation.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin SignedModules.Natural Atlas.Codes Atlas.Fischer

/-- The two explicit source monomial sums as a scalar function. -/
def pairCubicValue (f h k : PairSpace) : ℝ :=
  4 * (∑ i : Axis, ∑ x : Omega, ∑ y : Omega, ∑ z : Omega,
    f.val i x y * h.val i y z * k.val i z x) -
  4 * (∑ σ : Equiv.Perm Axis, ∑ x : Omega, ∑ y : Omega,
    f.val (σ 0) x y * h.val (σ 1) x y * k.val (σ 2) x y)

/-- The source pair cubic: same-axis triangles and the mixed same-pair monomials. -/
def pairBeta : Griess.TrilinearForm PairSpace where
  toFun f :=
    { toFun h :=
        { toFun := pairCubicValue f h
          map_add' k l := by
            simp only [pairCubicValue, Submodule.coe_add, Pi.add_apply, mul_add,
              Finset.sum_add_distrib]
            ring
          map_smul' t k := by
            simp only [pairCubicValue, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
              mul_left_comm _ t, ← Finset.mul_sum, RingHom.id_apply]
            ring }
      map_add' h k := by
        apply LinearMap.ext
        intro l
        simp only [pairCubicValue, Submodule.coe_add, Pi.add_apply, mul_add, add_mul,
          Finset.sum_add_distrib, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
        ring
      map_smul' t h := by
        apply LinearMap.ext
        intro k
        simp only [pairCubicValue, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
          mul_left_comm _ t, mul_assoc t, ← Finset.mul_sum,
          LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
        ring }
  map_add' f h := by
    apply LinearMap.ext
    intro k
    apply LinearMap.ext
    intro l
    simp only [pairCubicValue, Submodule.coe_add, Pi.add_apply, add_mul,
      Finset.sum_add_distrib, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' t f := by
    apply LinearMap.ext
    intro h
    apply LinearMap.ext
    intro k
    simp only [pairCubicValue, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      mul_assoc t, ← Finset.mul_sum, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
    ring

theorem pairBeta_apply (f h k : PairSpace) : pairBeta f h k =
    4 * (∑ i : Axis, ∑ x : Omega, ∑ y : Omega, ∑ z : Omega,
      f.val i x y * h.val i y z * k.val i z x) -
    4 * (∑ σ : Equiv.Perm Axis, ∑ x : Omega, ∑ y : Omega,
      f.val (σ 0) x y * h.val (σ 1) x y * k.val (σ 2) x y) := rfl

private theorem triangle_signs (g : N) (i : Axis) (x y z : Omega) :
    sign (coordinateShift g i x + coordinateShift g i y) *
      sign (coordinateShift g i y + coordinateShift g i z) *
      sign (coordinateShift g i z + coordinateShift g i x) = 1 := by
  rw [← sign_add, ← sign_add]
  have h : (coordinateShift g i x + coordinateShift g i y) +
      (coordinateShift g i y + coordinateShift g i z) +
      (coordinateShift g i z + coordinateShift g i x) = 0 := by
    calc
      _ = (coordinateShift g i x + coordinateShift g i x) +
        (coordinateShift g i y + coordinateShift g i y) +
        (coordinateShift g i z + coordinateShift g i z) := by abel
      _ = 0 := by simp
  rw [h, sign_zero]

private theorem mixed_signs (g : N) (σ : Equiv.Perm Axis) (x y : Omega) :
    sign (coordinateShift g (σ 0) x + coordinateShift g (σ 0) y) *
      sign (coordinateShift g (σ 1) x + coordinateShift g (σ 1) y) *
      sign (coordinateShift g (σ 2) x + coordinateShift g (σ 2) y) = 1 := by
  have hs (z : Omega) : coordinateShift g (σ 0) z + coordinateShift g (σ 1) z +
      coordinateShift g (σ 2) z = 0 := by
    have h := (Equiv.sum_comp σ (fun i => coordinateShift g i z)).trans (coordinateShift_sum g z)
    simpa only [Fin.sum_univ_three] using h
  rw [← sign_add, ← sign_add]
  have h : (coordinateShift g (σ 0) x + coordinateShift g (σ 0) y) +
      (coordinateShift g (σ 1) x + coordinateShift g (σ 1) y) +
      (coordinateShift g (σ 2) x + coordinateShift g (σ 2) y) = 0 := by
    calc
      _ = (coordinateShift g (σ 0) x + coordinateShift g (σ 1) x + coordinateShift g (σ 2) x) +
        (coordinateShift g (σ 0) y + coordinateShift g (σ 1) y + coordinateShift g (σ 2) y) := by abel
      _ = 0 := by rw [hs x, hs y, add_zero]
  rw [h, sign_zero]

/-- Invariance uses the actual common coordinate permutation and balanced signs;
no invariant cubic is assumed. -/
theorem pairBeta_invariant (g : N) (f h k : PairSpace) :
    pairBeta (pairRepresentation g f) (pairRepresentation g h) (pairRepresentation g k) =
      pairBeta f h k := by
  rw [pairBeta_apply, pairBeta_apply]
  congr 1
  · congr 1
    rw [← Equiv.sum_comp (axisPermutation g)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp (coordinatePermutation g)]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Equiv.sum_comp (coordinatePermutation g)]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Equiv.sum_comp (coordinatePermutation g)]
    apply Finset.sum_congr rfl
    intro z _
    rw [pairRepresentation_apply_forward, pairRepresentation_apply_forward,
      pairRepresentation_apply_forward]
    calc
      _ = (sign (coordinateShift g i x + coordinateShift g i y) *
        sign (coordinateShift g i y + coordinateShift g i z) *
        sign (coordinateShift g i z + coordinateShift g i x)) *
        (f.val i x y * h.val i y z * k.val i z x) := by ring
      _ = _ := by rw [triangle_signs, one_mul]
  · congr 1
    rw [← Equiv.sum_comp (Equiv.mulLeft (axisPermutation g))]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Equiv.sum_comp (coordinatePermutation g)]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Equiv.sum_comp (coordinatePermutation g)]
    apply Finset.sum_congr rfl
    intro y _
    change (pairRepresentation g f).val (axisPermutation g (σ 0))
        (coordinatePermutation g x) (coordinatePermutation g y) *
      (pairRepresentation g h).val (axisPermutation g (σ 1))
        (coordinatePermutation g x) (coordinatePermutation g y) *
      (pairRepresentation g k).val (axisPermutation g (σ 2))
        (coordinatePermutation g x) (coordinatePermutation g y) = _
    rw [pairRepresentation_apply_forward, pairRepresentation_apply_forward,
      pairRepresentation_apply_forward]
    calc
      _ = (sign (coordinateShift g (σ 0) x + coordinateShift g (σ 0) y) *
        sign (coordinateShift g (σ 1) x + coordinateShift g (σ 1) y) *
        sign (coordinateShift g (σ 2) x + coordinateShift g (σ 2) y)) *
        (f.val (σ 0) x y * h.val (σ 1) x y * k.val (σ 2) x y) := by ring
      _ = _ := by rw [mixed_signs, one_mul]

end Sporadic.Monster.Construction.NMonomial.EAction
