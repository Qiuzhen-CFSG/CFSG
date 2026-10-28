module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitCentralizer
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinAction

/-!
# Finite kernel of the split Clifford Spin action

For an explicitly split finite-dimensional quadratic form over a field, the
kernel of Clifford conjugation on the underlying quadratic space is finite.
No restriction on the characteristic is needed, so the result applies in
particular to split even-dimensional forms in characteristic two.

The scalar-centralizer step is supplied by the lower split Clifford module.
The remaining argument identifies the kernel with scalar square roots of one,
embedding it into an at-most-two element set.  This is the finite-kernel input
for the even orthogonal Spin isogeny construction.
-/

universe u

open CliffordAlgebra

namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k]
variable [AddCommGroup V] [Module k V]
variable {Q : QuadraticForm k V}
variable [FiniteDimensional k V]

private theorem cliffordSpinAction_ker_eq_algebraMap
    (s : SplitQuadraticForm Q)
    (z : (cliffordSpinAction Q s.actionForm).ker) :
    ∃ a : k, (z.1 : CliffordAlgebra Q) =
      algebraMap k (CliffordAlgebra Q) a := by
  apply CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_ι s
    (z.1 : CliffordAlgebra Q) (spinGroup.mem_even z.1.property)
  intro v
  have hspec := cliffordSpinAction_spec Q s.actionForm z.1 v
  rw [z.2] at hspec
  have hconj : CliffordAlgebra.ι Q v =
      (z.1 : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        ↑((spinGroup.toUnits z.1)⁻¹) := by
    simpa using hspec
  have hmul := congrArg
    (fun y : CliffordAlgebra Q => y * (spinGroup.toUnits z.1 : CliffordAlgebra Q))
    hconj
  have hmul' : CliffordAlgebra.ι Q v *
        (spinGroup.toUnits z.1 : CliffordAlgebra Q) =
      (z.1 : CliffordAlgebra Q) *
        (CliffordAlgebra.ι Q v *
          ((↑((spinGroup.toUnits z.1)⁻¹) : CliffordAlgebra Q) *
            (spinGroup.toUnits z.1 : CliffordAlgebra Q))) := by
    simpa only [mul_assoc] using hmul
  rw [Units.inv_mul, mul_one] at hmul'
  exact hmul'.symm

private noncomputable def spinActionKernelScalar
    (s : SplitQuadraticForm Q)
    (z : (cliffordSpinAction Q s.actionForm).ker) : k :=
  Classical.choose (cliffordSpinAction_ker_eq_algebraMap s z)

private theorem spinActionKernelScalar_spec
    (s : SplitQuadraticForm Q)
    (z : (cliffordSpinAction Q s.actionForm).ker) :
    (z.1 : CliffordAlgebra Q) =
      algebraMap k (CliffordAlgebra Q) (spinActionKernelScalar s z) :=
  Classical.choose_spec (cliffordSpinAction_ker_eq_algebraMap s z)

private theorem spinActionKernelScalar_sq
    (s : SplitQuadraticForm Q)
    (z : (cliffordSpinAction Q s.actionForm).ker) :
    spinActionKernelScalar s z * spinActionKernelScalar s z = 1 := by
  let e := CliffordAlgebra.changeFormEquiv s.bilinear_toQuadraticMap
  let _ : Nontrivial (CliffordAlgebra Q) := e.symm.injective.nontrivial
  apply (FaithfulSMul.algebraMap_injective k (CliffordAlgebra Q))
  have hnorm := spinGroup.star_mul_self_of_mem z.1.property
  rw [spinActionKernelScalar_spec s z] at hnorm
  simpa [CliffordAlgebra.star_algebraMap] using hnorm

private theorem spinActionKernelScalar_injective
    (s : SplitQuadraticForm Q) :
    Function.Injective (spinActionKernelScalar s) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  rw [spinActionKernelScalar_spec s z, spinActionKernelScalar_spec s w, hzw]

/-- The kernel of the Clifford conjugation action attached to an explicitly
split finite-dimensional quadratic form is finite in every characteristic. -/
public theorem cliffordSpinAction_ker_finite
    (s : SplitQuadraticForm Q) :
    Set.Finite
      ((cliffordSpinAction Q s.actionForm).ker : Set (spinGroup Q)) := by
  have hroots : ({a : k | a * a = 1} : Set k).Finite := by
    apply ((Set.finite_singleton (-1 : k)).insert (1 : k)).subset
    intro a ha
    have hfactor : (a - 1) * (a + 1) = 0 := by
      calc
        (a - 1) * (a + 1) = a * a - 1 := by ring
        _ = 0 := by rw [ha]; ring
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      exact sub_eq_zero.mp h
    · right
      exact eq_neg_of_add_eq_zero_left h
  rw [← Set.finite_coe_iff]
  let _ : Finite {a : k // a * a = 1} := Set.finite_coe_iff.mpr hroots
  let kernelScalar :
      (cliffordSpinAction Q s.actionForm).ker →
        {a : k // a * a = 1} :=
    fun z => ⟨spinActionKernelScalar s z, spinActionKernelScalar_sq s z⟩
  exact Finite.of_injective kernelScalar (by
    intro z w hzw
    apply spinActionKernelScalar_injective s
    exact congrArg Subtype.val hzw)

end Theory.AlgebraicGroup
