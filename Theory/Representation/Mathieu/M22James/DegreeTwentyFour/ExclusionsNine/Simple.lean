module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Reduction
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple.WordReduction
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple.Extension
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsNine.Simple.Recognition

/-!
# Assembly of the simple-point degree-eighteen obstruction

An irreducible binary point restriction of dimension eighteen satisfying the
central quadratic relation is equivalent to one of the two concrete mixed
tensor models. The recognition proof derives the Schur field, constructs the
tensor-coordinate equivalence and descends it to the binary field. Centrality
then forces the transported full-group action to be F₄-linear, and the literal
subgroup words give the matrix equations excluded for both models.

This discharges the simple-point extension premise of the central degree-nine
exclusion. No absolute irreducibility or degree catalogue is assumed.

Source: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
pp.15–16, M₂₂ branch; Aschbacher–Smith H.12.1, printed pp.393–394, for the
actual SL₃(4) point subgroup. This is the simple-point obstruction used in that
degree exclusion, not the full sporadic-module classification.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine
universe u

/-- The simple-point exclusion follows from actual binary model recognition. -/
theorem simplePointExtensionExclusion_of_recognition
    (h : Simple.SimplePointRecognition.{u}) : SimplePointExtensionExclusion.{u} := by
  intro V _ _ _ ρ hq hi hd
  obtain ⟨b, ⟨e⟩⟩ := h V (pointAction ρ) hq hi hd
  exact Simple.no_mixed_extension ρ b e

/-- No binary action of the actual triple Mathieu cover has an irreducible
point restriction of dimension eighteen satisfying the central quadratic
relation. The binary recognition premise is fully discharged. -/
theorem simplePointExtensionExclusion : SimplePointExtensionExclusion.{u} :=
  simplePointExtensionExclusion_of_recognition Simple.simplePointRecognition

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsNine
