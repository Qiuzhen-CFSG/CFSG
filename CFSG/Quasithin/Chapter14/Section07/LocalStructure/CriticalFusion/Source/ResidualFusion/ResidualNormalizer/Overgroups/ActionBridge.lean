module

public import Theory.SpecificGroups.Alternating.FiveExtensionAction
import all Theory.SpecificGroups.Alternating.FiveExtensionAction

/-!
# Equation interface for the five-point automorphism marking

The shared implementation keeps the body of `symmetricAutEquiv` private and
exports no evaluation equation. This internal proof extension uses `import all`
only to publish that equation; its statement uses public names. It lets the
14.7.67 consumer compare its original quotient marking with the actual
conjugation action without changing the shared module or its definition.

Source: the construction in `FiveExtensionAction`, and Aschbacher--Smith,
Lemma 14.7.67(4), printed p.1070.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.Overgroups

/-- The underlying permutation of the image is literal conjugation. -/
theorem symmetricAutEquiv_apply (s : Equiv.Perm (Fin 5))
    (a : alternatingGroup (Fin 5)) :
    (Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv s a :
      Equiv.Perm (Fin 5)) = s * (a : Equiv.Perm (Fin 5)) * s⁻¹ := by rfl

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.Overgroups
