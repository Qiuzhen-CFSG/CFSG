module

public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Assembly
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.FanoDecomposition

/-!
# The irreducible binary representations of SL₃(2)

Every finite-dimensional irreducible binary representation of the actual
`BinaryLinearThree.Group` is equivalent to the trivial, natural, dual-natural,
or eight-dimensional adjoint representation. The imported density certificates
also prove absolute irreducibility of the three nontrivial models.

A nonzero vector fixed by a Sylow two-subgroup realizes an irreducible module
as a quotient of the flag permutation module. Its concrete decomposition into
the trivial module, the point and line cores, and the adjoint module, together
with both core exact sequences, gives the four alternatives.

Source: Aschbacher–Smith, H.6.1, using the constructions of H.5.3 and H.6.2,
printed pp.385–387 of the combined manuscript of 1 March 2004.
-/

public section

open Representation

namespace BinaryLinearThree.IrreducibleCatalogue

open FanoDecomposition

universe u

variable {M : Type u} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

set_option backward.isDefEq.respectTransparency false in
/-- H.6.1 on the concrete SL₃(2) carrier, with actual representation
equivalences and no assumed catalogue or decomposition witnesses. -/
theorem classify (ρ : Representation (ZMod 2) Group M) [IsIrreducible ρ] :
    Nonempty (ρ.Equiv (Representation.trivial (ZMod 2) Group (ZMod 2))) ∨
      Nonempty (ρ.Equiv W) ∨ Nonempty (ρ.Equiv W.dual) ∨ Nonempty (ρ.Equiv S) := by
  exact classify_from_flag_decomposition flagPerm markedFlag (flagSylow : Subgroup Group)
    flagSylow.isPGroup' (fun _ => Iff.rfl) markedFlag_reachable lineCoreRepresentation
    pointEvaluation pointWeightedSum pointWeightedSum_surjective point_exact
    lineEvaluation lineWeightedSum lineWeightedSum_surjective line_exact
    flagDecomposition ρ

set_option backward.isDefEq.respectTransparency false in
/-- The nontrivial-action form of H.6.1 consumed by the Chapter 13
linear-three chief-factor decomposition. -/
theorem classify_nontrivial (ρ : Representation (ZMod 2) Group M) [IsIrreducible ρ]
    (hρ : ∃ g : Group, ∃ v : M, ρ g v ≠ v) :
    Nonempty (ρ.Equiv W) ∨ Nonempty (ρ.Equiv W.dual) ∨ Nonempty (ρ.Equiv S) := by
  rcases classify ρ with htriv | h
  · obtain ⟨e⟩ := htriv
    obtain ⟨g, v, hv⟩ := hρ
    apply False.elim
    apply hv
    apply e.toLinearEquiv.injective
    simpa using congrArg (fun f => f v) (e.toIntertwiningMap.isIntertwining' g)
  · exact h

end BinaryLinearThree.IrreducibleCatalogue
