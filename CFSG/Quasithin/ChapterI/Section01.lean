module

public import Theory.Representation.FirstCohomology

/-!
# I.1: Elementary results on cohomology

This module exports the elementary first-cohomology and dual-cover construction
used in Remark I.1.5 of Aschbacher--Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), printed pp.407--408.

The map sending a vector to its displacement cocycle has kernel equal to the
fixed space. Passing to cohomology adds the original submodule to that kernel.
This gives the rigidity consequence below whenever the first cohomology vanishes.
The Schur-multiplier and named-module calculations in I.1.2--I.1.6 are separate
mathematical inputs; this module does not assume or assert those tables.
-/

namespace CFSG.Quasithin.ChapterI

open Representation Representation.OneCohomology

/-- The vanishing consequence of I.1.5: a dual covering of a module with zero
first cohomology is the original module. This applies, in particular, over F₂. -/
public theorem dualCover_eq_of_firstCohomology_eq_zero
    {k G W : Type*} [CommRing k] [Group G] [AddCommGroup W] [Module k W]
    {ρ : Representation k G W} (V : Subrepresentation ρ)
    (h : IsDualCover V) [Subsingleton (H1 V.toRepresentation)] :
    V.toSubmodule = ⊤ :=
  dualCover_eq_top_of_H1_subsingleton V h.1 h.2

end CFSG.Quasithin.ChapterI
