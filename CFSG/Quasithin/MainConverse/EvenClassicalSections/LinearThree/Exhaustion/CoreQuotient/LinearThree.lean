module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.Structure
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.PSL3.OuterSolvable

/-!
# The linear-three core: reduction to concrete matrix automorphisms

An `IsPSL` witness supplies an actual equivalence to the central quotient
of SL₃ over a finite field. Simplicity and nonsolvability transfer through
that equivalence, so the model calculation needs no independent simplicity
or order certification. The positive exponent includes `m = 1`, which is
the separately listed binary-three core.

The final outer-solvability theorem still awaits arbitrary-automorphism
coverage and the standard outer-image calculation. The theorem below is
explicitly conditional on these independent inputs and is not presented as
the completed source result.

Source: GLS3, Theorem 2.5.12, §2.7, and the final extension-control argument
in Theorem 6.5.3 (`refs/KGroup/GLS3/chapter2.tex` and `chapter6.tex`).
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable

/-- Transfer the two concrete automorphism inputs to every recognized binary
PSL₃ core. The extra inputs remain obligations of this module's assembly owner. -/
public theorem linearThree_outer_isSolvable_of_standard_inputs
    (hcoverage : ∀ (F : Type) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)],
      ¬ Group.IsSolvable PSL(3,F) → ∀ m : ℕ, 0 < m → Nat.card F = 2 ^ m →
        standard F = ⊤)
    (hstandard : ∀ (F : Type) [Field F] [Finite F],
      Group.IsSolvable (standardOuter F))
    (S : Type) [Group S] [IsSimpleGroup S]
    (hns : ¬ Group.IsSolvable S) (m : ℕ) (hm : 0 < m)
    (hS : ClassicalGroup.IsPSL S 3 (2 ^ m)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let : IsSimpleGroup PSL(3,F) := e.symm.isSimpleGroup
  have hnsF : ¬ Group.IsSolvable PSL(3,F) := by
    intro h
    let := h
    exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  let : Group.IsSolvable (MulAut.Outer PSL(3,F)) :=
    outer_isSolvable_of_standard_inputs F
      (hcoverage F hnsF m hm hcard) (hstandard F)
  exact MulAut.isSolvable_outer_of_mulEquiv e

end CFSG.Quasithin.MainConverse.LinearThreeSections
