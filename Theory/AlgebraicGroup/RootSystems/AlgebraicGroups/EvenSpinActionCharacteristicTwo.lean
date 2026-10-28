module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinActionKernel
public import Mathlib.Algebra.CharP.Two

/-!
# Faithfulness of the split Spin action in characteristic two

An element in the kernel of the natural Clifford action commutes with every
embedded vector. The split Clifford centralizer theorem makes it a scalar,
and the Spin norm makes its square one. In characteristic two the only such
scalar is one, so the natural action is injective on field points.

This is a statement about points. It supplies no regular inverse to the
Spin-to-Omega isogeny. That distinction is essential for the simply connected
D4 construction in characteristic two (GLS3, §§1.10 and 1.12).
-/

universe u
namespace Theory.AlgebraicGroup

variable {k V : Type u} [Field k] [CharP k 2]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

/-- The natural action of split Spin is faithful on points in characteristic
two, without any assertion that its inverse on its image is regular. -/
public theorem cliffordSpinActionOfSplit_injective_charTwo
    (s : SplitQuadraticForm Q) :
    Function.Injective (cliffordSpinActionOfSplit Q s) := by
  apply (cliffordSpinActionOfSplit Q s).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  have haction : cliffordSpinActionOfSplit Q s x = 1 := hx
  obtain ⟨a, ha⟩ := CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_ι s
    (x : CliffordAlgebra Q) (spinGroup.mem_even x.property) (by
      intro v
      have hspec := cliffordSpinActionOfSplit_spec Q s x v
      rw [haction] at hspec
      have hconj : CliffordAlgebra.ι Q v =
          (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
            (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) := by
        simpa using hspec
      have hmul := congrArg
        (fun y : CliffordAlgebra Q => y * (spinGroup.toUnits x : CliffordAlgebra Q))
        hconj
      have hmul' : CliffordAlgebra.ι Q v *
          (spinGroup.toUnits x : CliffordAlgebra Q) =
        (x : CliffordAlgebra Q) *
          (CliffordAlgebra.ι Q v *
            ((↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) *
              (spinGroup.toUnits x : CliffordAlgebra Q))) := by
        simpa only [mul_assoc] using hmul
      rw [Units.inv_mul, mul_one] at hmul'
      exact hmul'.symm)
  let : Nontrivial (CliffordAlgebra Q) :=
    s.cliffordToExterior.symm.injective.nontrivial
  have hnorm := spinGroup.star_mul_self_of_mem x.property
  rw [ha] at hnorm
  have haa : a * a = 1 := by
    apply (FaithfulSMul.algebraMap_injective k (CliffordAlgebra Q))
    simpa [CliffordAlgebra.star_algebraMap] using hnorm
  have ha1 : a = 1 := CharTwo.sq_injective (by simpa [pow_two] using haa)
  change x = 1
  apply Subtype.ext
  simpa [ha1] using ha

end Theory.AlgebraicGroup
