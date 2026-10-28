module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.Source
public import Theory.Representation.AbsolutelyIrreducible
public import Mathlib.LinearAlgebra.Trace

/-!
# The two concrete HS character calculations needed for binary degree recognition

The source degree argument needs an absolute degree window and, separately,
the degree-twenty trace field. These predicates specify those calculations on
the actual HS carrier; neither predicate is asserted here. Simplicity is
inherited from the source central quotient. The first calculation determines
the dimension over the commuting field; the second descends it to F₂.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Proposition 5.1,
HS paragraph, author preprint p.16; Aschbacher--Smith K.4, printed p.457.
The actual source application is in the sibling `SourceDegree` module.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
universe v

/-- The absolute degree input, on the actual HS carrier over finite fields of
characteristic two. This is a specification, not a character-table theorem. -/
def AbsoluteDegreeWindow : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible →
      Module.finrank K W ≤ 50 → Module.finrank K W = 20

/-- The additional characteristic-two trace calculation needed for binary
descent. It concerns all actual degree-twenty absolutely irreducible actions,
not merely one chosen matrix realization. -/
def DegreeTwentyTraceField : Prop :=
  IsSimpleGroup KnownSimple.SporadicName.hs.Carrier →
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W),
    Function.Injective τ → τ.IsAbsolutelyIrreducible →
      Module.finrank K W = 20 →
        ∀ g, LinearMap.trace K W (τ g) ^ 2 = LinearMap.trace K W (τ g)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
