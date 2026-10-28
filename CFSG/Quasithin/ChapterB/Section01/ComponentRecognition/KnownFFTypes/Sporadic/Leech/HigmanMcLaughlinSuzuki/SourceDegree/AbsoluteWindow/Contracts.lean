module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FiveCenter

/-!+# The remaining HS representation calculations after five-center restriction

The proved extraspecial restriction gives dimension f + 20a with a positive.
Fixed-point-freeness of the actual five-center would force degree twenty or
forty in the source window; a separate absolute degree-forty exclusion under
that fixed-space hypothesis would finish it. These two predicates state the
missing calculations. Neither is
asserted here, and neither may be replaced by a character-table assumption.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph, author-preprint p.16, citing the low-dimensional representation
and Brauer-character calculations; Aschbacher--Smith K.4, printed p.457.
The parent `AbsoluteWindow` module owns their assembly.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow

universe v

/-- The actual five-center has no fixed vectors on a faithful absolutely
irreducible representation in the source degree window. This is a remaining
representation calculation, not a consequence asserted by this definition. -/
def FiveCenterFixedFreeInWindow : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible → Module.finrank K W ≤ 50 →
      Representation.invariants (τ.comp fiveCenter.subtype) = ⊥

/-- Once the actual five-center is fixed-point-free, absolute degree forty is
excluded. This keeps the preceding calculation as an explicit hypothesis, so
its producer and this exclusion can be proved independently. -/
def FixedFreeAbsoluteDegreeFortyExcluded : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible →
      Representation.invariants (τ.comp fiveCenter.subtype) = ⊥ →
        Module.finrank K W ≠ 40

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow
