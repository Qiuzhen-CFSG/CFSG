module

public import Theory.Representation.Mathieu.SmallModules.M23Recognition
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.Source

/-!
# Native M23 completeness for the Chapter K source contract

The native recognition theorem supplies both alternatives in
`M23SmallRecognition`, including the group marking, linear equivalence and
pointwise equivariance to the literal Golay restrictions. This discharges
the small-module premise of `source_m23_of_degree_and_small_recognition`;
the degree reduction remains with the source assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), K.4 opening,
printed p.457 (PDF p.468), and H.13.1--2, printed p.395.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
universe v

/-- The published native M23 small-recognition contract, in every carrier universe. -/
theorem m23SmallRecognition : M23SmallRecognition.{v} := by
  intro V _ _ _ ρ hf hi hd
  let : ρ.IsIrreducible := hi
  exact Representation.MathieuSmall.M23Recognition.of_degree_eleven ρ hf hd

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
