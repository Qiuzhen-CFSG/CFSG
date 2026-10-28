module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.QuotientCount.Action
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Injectivity

/-!
# Binary coordinates on the actual local normal closure

The certified eleven commuting involutions span the specified normal closure:
the conjugation tables make their span normal, and the first vector is its
normal generator. The matrix injectivity certificate makes the binary-product
parametrization bijective. In particular this normal closure acts trivially by
conjugation on itself.

The words and their right-conjugation tables are the ATLAS `J4G1-max1W1`
certificate described in `KernelCount.Relations`. No order or quotient
identification is used here.
-/

set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency true

@[expose] public section
namespace Janko4.Cardinality.QuotientCount
open KernelCount

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

namespace Image

theorem closure_basis_eq_localKernel :
    Subgroup.closure (Set.range (basis hA hB)) = localKernel hA hB := by
  apply closure_conjugates_eq_normalClosure _ _ _ (localXY_generate hA hB)
  · intro i
    change (localX hA hB)⁻¹ * basis hA hB i * localX hA hB ∈ _
    rw [basis_conj_x]
    exact binaryProduct_mem _ _ _ (fun j =>
      Subgroup.subset_closure (Set.mem_range_self j))
  · intro i
    change (localY hA hB)⁻¹ * basis hA hB i * localY hA hB ∈ _
    rw [basis_conj_y]
    exact binaryProduct_mem _ _ _ (fun j =>
      Subgroup.subset_closure (Set.mem_range_self j))

-- Keep comparison of inherited group operations from unfolding the matrix model.
attribute [local irreducible] basis modelGroup matrixA matrixB localKernel
  max1Subgroup localX localY localKernelSeed

theorem mem_localKernel_iff_binaryProduct (g : max1Subgroup hA hB) :
    g ∈ localKernel hA hB ↔ ∃ v, binaryProduct (basis hA hB) v = g := by
  rw [← closure_basis_eq_localKernel hA hB]
  exact mem_closure_iff_binaryProduct (G := max1Subgroup hA hB) (n := 11)
    (basis hA hB) (fun i => basis_square hA hB i) (fun i j => basis_commute hA hB i j) g

/-- Evaluation of the eleven binary coordinates in the actual normal closure. -/
def coordinates (v : Fin 11 → Bool) : localKernel hA hB :=
  ⟨binaryProduct (basis hA hB) v,
    binaryProduct_mem _ _ _ (basis_mem_localKernel hA hB)⟩

@[simp] theorem coordinates_val (v : Fin 11 → Bool) :
    (coordinates hA hB v : max1Subgroup hA hB) = binaryProduct (basis hA hB) v := rfl

theorem coordinates_injective : Function.Injective (coordinates hA hB) := by
  intro v w h
  apply binaryProduct_injective hA hB (representation_basis hA hB) matrixProduct_injective
  simpa only [coordinates_val] using
    congrArg (fun n : localKernel hA hB => (n : max1Subgroup hA hB)) h

theorem coordinates_surjective : Function.Surjective (coordinates hA hB) := by
  intro g
  obtain ⟨v, hv⟩ := (mem_localKernel_iff_binaryProduct hA hB g).mp g.property
  exact ⟨v, Subtype.ext hv⟩

noncomputable def coordinatesEquiv : (Fin 11 → Bool) ≃ localKernel hA hB :=
  Equiv.ofBijective (coordinates hA hB)
    ⟨coordinates_injective hA hB, coordinates_surjective hA hB⟩

@[simp] theorem coordinatesEquiv_apply (v : Fin 11 → Bool) :
    coordinatesEquiv hA hB v = coordinates hA hB v := rfl

theorem coordinates_mul (v w : Fin 11 → Bool) :
    coordinates hA hB v * coordinates hA hB w =
      coordinates hA hB (fun i => v i ^^ w i) := by
  apply Subtype.ext
  change binaryProduct (basis hA hB) v * binaryProduct (basis hA hB) w = _
  rw [coordinates_val]
  exact binaryProduct_mul (G := max1Subgroup hA hB) (n := 11)
    (basis hA hB) (fun i => basis_square hA hB i) (fun i j => basis_commute hA hB i j) v w

theorem localKernel_commute (n : max1Subgroup hA hB) (hn : n ∈ localKernel hA hB)
    (m : max1Subgroup hA hB) (hm : m ∈ localKernel hA hB) : n * m = m * n := by
  obtain ⟨v, rfl⟩ := (mem_localKernel_iff_binaryProduct hA hB n).mp hn
  obtain ⟨w, rfl⟩ := (mem_localKernel_iff_binaryProduct hA hB m).mp hm
  rw [binaryProduct_mul (G := max1Subgroup hA hB) (n := 11) (basis hA hB) (fun i => basis_square hA hB i)
    (fun i j => basis_commute hA hB i j),
    binaryProduct_mul (G := max1Subgroup hA hB) (n := 11) (basis hA hB) (fun i => basis_square hA hB i)
    (fun i j => basis_commute hA hB i j)]
  congr 1
  funext i
  exact Bool.xor_comm _ _

/-- The right-conjugation table extends multiplicatively to every coordinate. -/
theorem right_conj_coordinates_x (v : Fin 11 → Bool) :
    (localX hA hB)⁻¹ * (coordinates hA hB v : max1Subgroup hA hB) * localX hA hB =
      binaryProduct (fun i => binaryProduct (basis hA hB)
        (fun j => (xMasks i).testBit j.val)) v := by
  have h := map_binaryProduct (MulAut.conj (localX hA hB)⁻¹).toMonoidHom
    (basis hA hB) v
  change (localX hA hB)⁻¹ * binaryProduct (basis hA hB) v * ((localX hA hB)⁻¹)⁻¹ =
    binaryProduct (fun i => (localX hA hB)⁻¹ * basis hA hB i * ((localX hA hB)⁻¹)⁻¹) v at h
  simpa only [inv_inv, basis_conj_x, coordinates_val] using h

theorem right_conj_coordinates_y (v : Fin 11 → Bool) :
    (localY hA hB)⁻¹ * (coordinates hA hB v : max1Subgroup hA hB) * localY hA hB =
      binaryProduct (fun i => binaryProduct (basis hA hB)
        (fun j => (yMasks i).testBit j.val)) v := by
  have h := map_binaryProduct (MulAut.conj (localY hA hB)⁻¹).toMonoidHom
    (basis hA hB) v
  change (localY hA hB)⁻¹ * binaryProduct (basis hA hB) v * ((localY hA hB)⁻¹)⁻¹ =
    binaryProduct (fun i => (localY hA hB)⁻¹ * basis hA hB i * ((localY hA hB)⁻¹)⁻¹) v at h
  simpa only [inv_inv, basis_conj_y, coordinates_val] using h

end Image

/-- The actual binary normal closure acts trivially on itself. -/
theorem localKernel_le_action_ker_certified :
    localKernel hA hB ≤ (action hA hB).ker :=
  localKernel_le_action_ker hA hB (Image.localKernel_commute hA hB)

end Janko4.Cardinality.QuotientCount
