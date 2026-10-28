module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.Reduction

/-!
# Assembly for components of proper alternating Sylow overgroups

Split the natural action into primitive and nonprimitive cases. In the
primitive case the proved reduction supplies a double transposition and
excludes three-cycles. The two remaining recognition inputs are explicit;
this conditional assembly does not yet prove the intrinsic classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85), final paragraph.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- Assemble the two permutation branches without changing the component
carriers, the genuine model equivalences, or the exceptional degree. -/
theorem alternating_proper_sylow_component_models_of_recognition (m : ℕ) (hm : 6 ≤ m)
    (hprimitive : AlternatingPrimitiveComponentRecognition m)
    (hnonprimitive : AlternatingNonprimitiveComponentRecognition m) :
    AlternatingProperSylowComponentModels m := by
  intro S X hS hX D hD
  by_cases hp : MulAction.IsPreprimitive X (Fin m)
  · exact alternating_primitive_component_models_of_recognition hm hprimitive S X hS hX hp D hD
  · exact hnonprimitive S X hS hX hp D hD

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
