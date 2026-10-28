module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.DimensionContracts

/-!
# The remaining exact adjacent-pair dimension estimates

The three-active-root certificates handle every support of cardinality at least
three. The remaining adjacent supports are precisely `{0,1}`, `{1,2}` and
`{2,3}`. These contracts retain the original binary local highest-vector data;
they do not assume a graph operator or identify any highest-weight module.

The final adjacent dimension estimate is assembled in `AdjacentDimension`.
Its application is Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.8(3B), and Aschbacher–Smith K.3.2, printed pp.454–455.
-/

@[expose] public section

open Representation

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The two adjacent pairs at the ends of the diagram. -/
def EndPairBound (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    (J = {0, 1} ∨ J = {2, 3}) → 25 ≤ Module.finrank (ZMod 2) V

/-- The adjacent pair in the middle of the diagram. -/
def MiddlePairBound (σ : Representation (ZMod 2) SL5TenDimensional.Group V) : Prop :=
  ∀ (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ {1, 2} v →
    25 ≤ Module.finrank (ZMod 2) V

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.AdjacentDimension
