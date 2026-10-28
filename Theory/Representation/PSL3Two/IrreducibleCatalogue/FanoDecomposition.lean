module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Inverse
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition.Transitive

/-!
# The binary Fano flag decomposition

The actual flag permutation module of SL₃(2) is equivariantly isomorphic to
`ZMod 2 × (Core × (LineCore × Steinberg))`, with the trivial, point-core,
line-core and trace-zero adjoint actions respectively. The map sends a flag
basis vector to `(1, eₓ + Ω, e_λ + Ω, (v ↦ λ(v)x))`. A kernel-checked left
inverse and equal dimensions certify its bijectivity.

The imported core sequences are the genuine evaluation/weighted-sum exact
sequences W* → U₂ → W and W → line-core → W*. The flag action is transitive,
and the marked stabilizer is an actual Sylow two-subgroup; `cosetEquiv` is the
equivariant identification with its cosets. No irreducible catalogue, absolute
irreducibility, radical or nonsplitting assertion is assumed or proved here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the core
models in H.5.3(1–2) and the decomposition H.6.2(1), printed pp.385–387.
-/

@[expose] public section
open Representation
namespace BinaryLinearThree.FanoDecomposition

/-- The concrete four-summand decomposition of the actual flag representation. -/
noncomputable def flagDecomposition : Representation.Equiv flagRepresentation targetRepresentation :=
  flagMap.ofBijective flagMap_bijective

@[simp] theorem flagDecomposition_apply (a : BinaryPermutation.Full Flag) :
    flagDecomposition a = flagMap a := rfl

/-- The decomposition has the specified literal value on every flag basis vector. -/
theorem flagDecomposition_basis (f : Flag) : flagDecomposition (Pi.single f 1) =
    (1, (pointSpike f.val.1, (lineSpike f.val.2, flagRankOne f))) := flagMap_basis f

/-- The checked reconstruction formula is also a right inverse. -/
theorem flagInverse_rightInverse : Function.RightInverse flagInverse flagMap := by
  intro v
  obtain ⟨a, rfl⟩ := flagMap_bijective.surjective v
  rw [flagInverse_leftInverse]

/-- The inverse of the representation equivalence is the explicit coefficient formula. -/
@[simp] theorem flagDecomposition_symm_apply (v : Target) :
    flagDecomposition.symm v = flagInverse v := by
  apply flagMap_injective
  change flagDecomposition (flagDecomposition.symm v) = flagMap (flagInverse v)
  rw [Representation.Equiv.apply_symm_apply, flagInverse_rightInverse]

end BinaryLinearThree.FanoDecomposition
