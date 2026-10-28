module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Frames
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Scalar

/-!
# Conditional assembly of the Leech short-root extension

The source local A₅ must supply an element of C(I) acting as C(1) in the
chosen long frame, conjugate to the literal scalar involution. A separate
Leech conjugacy calculation must identify that scalar with `markedInvolution`.
The proved torus extension then constructs every short-root parameter,
including the exact marking demanded by `ShortFrame`.

These two geometric premises are not proved here. In particular this module
does not yet assert `nonempty_shortFrame` for an arbitrary `LongFrame`.
The conditional consumer below retains final assembly of the local extension
without requiring an inhabitant of `LongFrame` or `CentralizerFaithful`.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four definitions on p.269. The square-of-lift statement of
Lemma 46.9, p.254, does not on its own prove the marking premise.
-/

public section

open Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators

/-- The literal consumer of the local A₅ and scalar-marking branches.
All extra geometric premises remain explicit until their constructions exist. -/
theorem nonempty_shortFrame_of_scalar_seed (L : LongFrame)
    (hseed : ∃ g ∈ centralizerI,
      L.Intertwines g (rootC 1) ∧ IsConj g scalarInvolution)
    (hmarked : IsConj scalarInvolution markedInvolution) : Nonempty (ShortFrame L) := by
  obtain ⟨g, hg, ha, hc⟩ := hseed
  exact ⟨shortFrameOfOne L g hg ha (hc.trans hmarked)⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
