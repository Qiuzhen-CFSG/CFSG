module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.PairContracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.EndPairs.Case01
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.EndPairs.Reversal

/-!
# Dimension twenty-five for both end-adjacent supports

A nonzero local highest vector with support `{0,1}` supplies twenty-five
independent translates, certified by root differences and the active rank-one
relations. The actual inverse-transpose automorphism, conjugated by coordinate
reversal, transports support `{2,3}` to `{0,1}` on the same vector space.

This discharges `EndPairBound`, the end-pair premise of
`Graph.adjacent_dimension_bound_of_pair_estimates`. The calculation itself
works without faithfulness or irreducibility; the public contract retains the
hypotheses of its source consumer.

Source application: Guralnick–Malle, Classification of 2F-modules II,
Lemma 4.2/Table 6, pp.22–23, and Proposition 4.8(3B), pp.27–28;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
open Representation
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]

/-- Either exact end-adjacent support forces dimension at least twenty-five. -/
theorem end_pair_bound (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (_hf : Function.Injective σ) (_hi : IsIrreducible σ) : EndPairBound σ := by
  intro J v hv h hJ
  rcases hJ with rfl | rfl
  · exact EndPairs.Case01.finrank_ge_twentyFive h hv
  · exact EndPairs.Case01.finrank_ge_twentyFive (EndPairs.reverse_local_highest h) hv

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension
