module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Relations
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Reference
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Certificate.Homogeneous
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Certificate.NaturalDual
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.ExtensionExclusion.Certificate.DualNatural

/-!
# Finite exclusion for the Mathieu point-restriction catalogue

Only the nonzero diagonal natural-by-dual parameters admit the necessary
extension equations. The 31 other entries have a column forced to zero by
checked linear combinations of the 432 scalar intertwining equations; this
contradicts the equation X² = 1. The three certificate modules check every
operator against the literal catalogue matrices and check every row combination
in Lean's kernel. The finite enumeration here concerns only the 34 catalogue
entries, never the 2^144 possible matrices.

This is the finite linear-algebra step used in James (1973), Lemma 8.3,
cited in Aschbacher–Smith H.12.1(1), printed pp.393–394. The parent
`ExtensionExclusion` module owns its assembly with the full-group representation.
The diagnostic's ATLAS attribution and coordinate conventions are preserved in
`ExtensionExclusion/source/README.md`; reproducible certificates are described in
`Certificate/source/README.md`.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion
open PointModel Representation.SL3FourLocalCatalogue Certificate
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

private instance : DecidableEq CatalogueEntry :=
  inferInstanceAs (DecidableEq (Σ a b, ExtensionClass.Parameter a b))

set_option maxRecDepth 4000 in
private lemma catalogue_partition : ∀ i : CatalogueEntry,
    (∃ p : Reference.F, p ≠ 0 ∧ i = referenceEntry p) ∨
    (∃ j, i = Homogeneous.entries j) ∨
    (∃ j, i = NaturalDual.entries j) ∨
    (∃ j, i = DualNatural.entries j) := by
  decide +kernel

/-- The actual extension equations exclude every catalogue entry except the
nonzero diagonal natural-by-dual parameters. -/
theorem extensionEquations_referenceEntry (i : CatalogueEntry) (X : Matrix12)
    (h : ExtensionEquations i X) :
    ∃ p : Reference.F, p ≠ 0 ∧ i = referenceEntry p := by
  rcases catalogue_partition i with hs | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact hs
  · exact (Homogeneous.excludes j X h).elim
  · exact (NaturalDual.excludes j X h).elim
  · exact (DualNatural.excludes j X h).elim

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointRestriction.ExtensionExclusion
