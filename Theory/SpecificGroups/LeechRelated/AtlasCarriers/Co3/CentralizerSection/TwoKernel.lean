module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.Co3Kernel
public import Theory.SpecificGroups.SymplecticSix.EvenProjective
public import Mathlib.GroupTheory.PGroup

/-!
# The two-group kernel of the literal Co₃ projective quotient

The checked two-graph calculation in `UniversalDoubleCover.Co3Kernel` identifies
the kernel of the actual action on 36 fixed points with the marked involution.
The binary symplectic group has trivial center, so passing to the projective
quotient adds no kernel. Consequently the exact `quotientMap` used by the
centralizer section has a two-group kernel. No complement to the double cover
is used.

This supplies the coprime-kernel rank lifting input for the Co₃ exclusion in
Aschbacher--Smith A.2.19 and I.1.3, printed pp.40--41 and 407. The local model
is the nonsplit `2Sp₆(2)` of GLS3 Table 5.3j.
-/

public section
namespace Sporadic.LeechRelated.Co3.CentralizerSection
open Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover

/-- Projectivization does not enlarge the already calculated matrix kernel. -/
theorem quotientMap_ker_eq_matrixProjection_ker :
    quotientMap.ker = Co3Witness.matrixProjection.ker := by
  ext g
  change (QuotientGroup.mk' (Subgroup.center LinearData.Sp))
    (Co3Witness.matrixProjection g) = 1 ↔ Co3Witness.matrixProjection g = 1
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Theory.SpecificGroups.SymplecticSix.EvenProjective.center_eq_bot]
  rfl

/-- The kernel normal in the displayed numerator is exactly its central involution. -/
theorem quotientMap_ker_eq_zpowers :
    quotientMap.ker = Subgroup.zpowers Co3Witness.z :=
  quotientMap_ker_eq_matrixProjection_ker.trans Co3Witness.matrixProjection_ker_eq_zpowers

/-- The actual quotient used by the Co₃ section has a two-group kernel. -/
theorem quotientMap_kernel_isPGroup : IsPGroup 2 quotientMap.ker := by
  rw [quotientMap_ker_eq_matrixProjection_ker, isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change g.val ^ 2 = 1
  rcases Co3Witness.matrixProjection_kernel_cases g.val g.property with h | h
  · rw [h, one_pow]
  · rw [h, Co3Witness.z_sq]

end Sporadic.LeechRelated.Co3.CentralizerSection
