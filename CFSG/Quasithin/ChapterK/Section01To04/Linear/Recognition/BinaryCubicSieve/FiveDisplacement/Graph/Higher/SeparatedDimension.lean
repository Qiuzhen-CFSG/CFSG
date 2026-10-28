module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.DimensionContracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.SeparatedDimension.Case02
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.SeparatedDimension.Case13

/-!
# Dimension bounds for the separated binary SL₅ supports

For either literal support `{0,2}` or `{1,3}`, twenty-five permutation translates
of a nonzero local highest vector are independent. The two certificates use
triangular composites of root-difference operators and the original local
highest-vector relations. In particular, they require no extension of scalars,
absolute irreducibility or identification with an algebraic highest weight.

This discharges `SeparatedDimensionBound`, the separated-support premise of
`Graph.higher_displacement_of_dimension_estimates`. The certificate itself is
stronger than that consumer requires: faithfulness and irreducibility are not
needed for the local dimension estimate.

Source application: Guralnick–Malle, *Classification of 2F-modules II*,
Lemma 4.2/Table 6 and Proposition 4.8(3B), author manuscript pp.22–23, 27–28;
Aschbacher–Smith K.3.2, printed pp.454–455. This direct binary calculation
supplies the sufficient dimension bound used by the graph-displacement proof.
-/

public section

open Representation

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Both separated local supports have dimension at least twenty-five. -/
theorem separated_dimension_bound
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (_hf : Function.Injective σ) (_hi : IsIrreducible σ) : SeparatedDimensionBound σ := by
  intro J v hv hJ hsep
  rcases hsep with rfl | rfl
  · exact SeparatedDimension.Case02.twentyFive_le hJ hv
  · exact SeparatedDimension.Case13.twentyFive_le hJ hv

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph
