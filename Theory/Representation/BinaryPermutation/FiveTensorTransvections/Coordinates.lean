module

public import Theory.Representation.BinaryPermutation.FiveTensorQuadratic

/-!
# Coordinate test for the binary S₅ × S₃ tensor action

Use the core vectors eᵢ+e₄ and eⱼ+e₂ in the two permutation cores.
A kernel-checked finite calculation shows that if any two of their tensor
 displacements are zero or equal, both permutations are the identity.
Over F₂ this is exactly the obstruction to a common displacement line.

Source: Aschbacher–Smith 13.8.20, printed p.954, the S₅ × S₃ tensor branch.
-/

@[expose] public section
namespace BinaryPermutation.FiveTensorTransvections.Coordinates
def coreVector (n : ℕ) (i : Fin n) : BinaryPermutation.core (Fin (n+1)) :=
  ⟨Pi.single i.castSucc 1 + Pi.single (Fin.last n) 1, by
    simp [BinaryPermutation.mem_core, Finset.sum_add_distrib, show (1 : ZMod 2) + 1 = 0 from rfl]⟩
def delta (g : Equiv.Perm (Fin 5)) (h : Equiv.Perm (Fin 3))
    (ij : Fin 4 × Fin 2) : Fin 5 × Fin 3 → ZMod 2 := fun xy =>
  (coreVector 4 ij.1).val (g.symm xy.1) * (coreVector 2 ij.2).val (h.symm xy.2) -
    (coreVector 4 ij.1).val xy.1 * (coreVector 2 ij.2).val xy.2
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem displacement_test : ∀ (g : Equiv.Perm (Fin 5)) (h : Equiv.Perm (Fin 3)),
    (∀ i j, delta g h i = 0 ∨ delta g h j = 0 ∨ delta g h i = delta g h j) →
    g = 1 ∧ h = 1 := by
  decide +kernel

end BinaryPermutation.FiveTensorTransvections.Coordinates
end
