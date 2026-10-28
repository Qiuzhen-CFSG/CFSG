module

public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.BinaryModel

/-!
# The six balanced cross-commutator matrices

There are only 256 possible matrices with four entries in the four-element
center. The kernel checks their quadratic fibers on sixteen quotient vectors
and the polar pairing with the first anisotropic plane. The two conditions
leave precisely the six invertible binary matrices multiplied by z*u.
This calculation uses the explicit collection cocycle, not group tables or
subgroup enumeration.

Source motivation: the multiplication recognition in Aschbacher,
*Sporadic Groups* (1994), proof of 46.14, printed pp.257–258.
-/

public section
namespace Theory.GroupTheory.AnisotropicRecognition

/-- Balanced nonzero square fibers and the first-plane centralizer condition
leave exactly these six cross-commutator matrices. -/
theorem sixCases_of_balanced :
    ∀ M : Cross, FirstNondegenerate M → Balanced M → SixCases M := by
  decide +kernel

end Theory.GroupTheory.AnisotropicRecognition
