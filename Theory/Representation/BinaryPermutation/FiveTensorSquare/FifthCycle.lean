module
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Model
public import Mathlib.LinearAlgebra.TensorProduct.Basis
/-!
# Fixed-free five-cycles on the deleted tensor square

An invariant vector of a five-cycle is constant, hence zero in the odd
augmentation core. Tensor coordinate contractions transfer this to each
factor action on the square. These are the actual odd-order elements used
to split central covers in the deleted branch of Aschbacher–Smith D.3.7,
printed pp.197–199.
-/
public section
open scoped TensorProduct
namespace BinaryPermutation.FiveTensorSquare
private def cycle : Sym := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
private theorem cycle_even : cycle ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel
/-- The even five-cycle used to split a central deleted-square cover. -/
def fifthCycle : Alt := ⟨cycle,cycle_even⟩
theorem fifthCycle_pow_five : fifthCycle ^ 5 = 1 := by
  apply Subtype.ext
  change cycle ^ 5 = 1
  decide +kernel
private theorem fifthCycle_core_fixed (v : C) (hv : δ fifthCycle v = v) : v = 0 := by
  have h : ∀ v : Full (Fin 5), (∑ i, v i) = 0 →
      representation (Fin 5) cycle v = v → v = 0 := by decide +kernel
  exact Subtype.ext (h v v.property (congrArg Subtype.val hv))

/-- The five-cycle is fixed-free on the first deleted tensor factor. -/
theorem fifthCycle_left_fixed (v : V)
    (hv : deletedAction (fifthCycle,1) v = v) : v = 0 := by
  let b := Module.finBasis (ZMod 2) C
  let e := TensorProduct.equivFinsuppOfBasisRight (M := C) b
  have he (x : V) (i) : e (deletedAction (fifthCycle,1) x) i = δ fifthCycle (e x i) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u w =>
      change e (δ fifthCycle u ⊗ₜ[ZMod 2] δ 1 w) i = _
      simp [e]
    | add x y hx hy => simpa only [map_add,Finsupp.add_apply] using congrArg₂ (· + ·) hx hy
  apply e.injective
  apply Finsupp.ext
  intro i
  have hfix : δ fifthCycle (e v i) = e v i := by rw [←he,hv]
  simpa only [map_zero,Finsupp.zero_apply] using fifthCycle_core_fixed _ hfix

/-- The five-cycle is fixed-free on the second deleted tensor factor. -/
theorem fifthCycle_right_fixed (v : V)
    (hv : deletedAction (1,fifthCycle) v = v) : v = 0 := by
  let e := TensorProduct.comm (ZMod 2) C C
  have he (x : V) : e (deletedAction (1,fifthCycle) x) =
      deletedAction (fifthCycle,1) (e x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u w => rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  apply e.injective
  rw [map_zero]
  apply fifthCycle_left_fixed
  rw [←he,hv]
end BinaryPermutation.FiveTensorSquare
