module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
import all Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Equations for projective field transport

This is the proof interface for the coefficientwise transport constructed in
`Support`. The internal import deliberately accesses that definition to prove
its quotient equation; clients need only the public equation below.

The construction in `Support` is the licensed ATLAS field transport. No new
choice of a projective action is made here.
-/

namespace Atlas
open scoped MatrixGroups

@[simp] public theorem fieldEquivPSL_mk {F K : Type*} [Field F] [Field K]
    (n : ℕ) (e : F ≃+* K) (g : SL(n,F)) :
    fieldEquivPSL n e (QuotientGroup.mk' _ g) =
      QuotientGroup.mk' _ (fieldEquivSL n e g) := by
  rfl

end Atlas
