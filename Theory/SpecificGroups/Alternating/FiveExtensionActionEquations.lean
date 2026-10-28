module
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
import all Theory.SpecificGroups.Alternating.FiveExtensionAction

/-!
# The conjugation equation for the five-point automorphism marking

The existing equivalence S₅ ≃ Aut(A₅) is defined by conjugation. This
companion publishes its application equation without exposing its body or
changing the original module. The internal import is used only for this
specification. The terminal local product uses it to retain the prescribed
A₅ quotient map when extending the action to its normalizer.
Source: GLS3, 5.2.1; Aschbacher--Smith, completion of 12.3.1, p.812.
-/

namespace Theory.SpecificGroups.Alternating.FiveExtensionAction
public theorem symmetricAutEquiv_apply (s : Equiv.Perm (Fin 5)) :
    symmetricAutEquiv s = MulAut.conjNormal s := by rfl
end Theory.SpecificGroups.Alternating.FiveExtensionAction
