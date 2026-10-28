module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.PairContracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.MiddlePair.Certificate

/-!
# The exact middle-adjacent dimension bound for binary SL₅

Twenty-five permutation translates of a nonzero local highest vector with
support `{1,2}` are independent, as certified in `MiddlePair.Certificate`.
This discharges `MiddlePairBound`, the middle-pair input to
`Graph.adjacent_dimension_bound_of_pair_estimates`. The certificate itself
needs neither faithfulness nor irreducibility.

Source application: Guralnick–Malle, *Classification of 2F-modules, II*,
Lemma 4.2/Table 6, pp.22–23, and Proposition 4.8(3B), pp.27–28;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section

open Representation

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]

/-- A faithful irreducible binary SL₅ representation satisfies the exact
middle-adjacent support estimate required by the adjacent-dimension assembly. -/
theorem middle_pair_bound
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (_hfaithful : Function.Injective σ) (_hirreducible : Representation.IsIrreducible σ) :
    MiddlePairBound σ := by
  intro v hv h
  exact MiddlePair.finrank_ge_twentyFive h hv

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension
