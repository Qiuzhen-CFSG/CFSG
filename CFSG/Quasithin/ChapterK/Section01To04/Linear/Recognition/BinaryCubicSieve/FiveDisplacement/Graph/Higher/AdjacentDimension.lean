module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.PairContracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.EndPairs
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.MiddlePair
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.Three012
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.Three013
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.Three023
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Higher.AdjacentDimension.Three123

/-!
# Adjacent-support dimension bound for binary SL₅

Every support containing at least three roots gives twenty-five independent
permutation translates. This follows from four explicit coefficient-extraction
certificates; no faithfulness or irreducibility is needed for this branch.

The exact two-root supports `{0,1}`, `{1,2}` and `{2,3}` are covered by the
end-pair and middle-pair certificates. The finite support split below combines
these with the three-root cases to prove `AdjacentDimensionBound`, including
every support with additional active roots. No graph-operator,
absolute-irreducibility or highest-weight comparison hypothesis is added.

Source application: Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.8(3B), author manuscript pp.27–28; Aschbacher–Smith K.3.2,
printed pp.454–455. This discharges the adjacent dimension premise of
`higher_displacement_of_dimension_estimates`; the separated-support estimate
and final graph-displacement assembly belong to their respective consumers.
-/

public section

open Representation Representation.SL5TenDimensional.Classification

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Module.Finite (ZMod 2) V]

private theorem three_root_subset (J : Finset (Fin 4)) (hJ : 3 ≤ J.card) :
    {0, 1, 2} ⊆ J ∨ {0, 1, 3} ⊆ J ∨ {0, 2, 3} ⊆ J ∨ {1, 2, 3} ⊆ J := by
  revert J
  decide +kernel

/-- Three or more active roots already force twenty-five dimensions. -/
theorem finrank_ge_twentyFive_of_three_active
    {σ : Representation (ZMod 2) SL5TenDimensional.Group V}
    {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector σ J v) (hv : v ≠ 0) (hJ : 3 ≤ J.card) :
    25 ≤ Module.finrank (ZMod 2) V := by
  rcases three_root_subset J hJ with hsub | hsub | hsub | hsub
  · exact AdjacentDimension.Three012.finrank_ge_twentyFive h
      (hsub (by simp)) (hsub (by simp)) (hsub (by simp)) hv
  · exact AdjacentDimension.Three013.finrank_ge_twentyFive h
      (hsub (by simp)) (hsub (by simp)) (hsub (by simp)) hv
  · exact AdjacentDimension.Three023.finrank_ge_twentyFive h
      (hsub (by simp)) (hsub (by simp)) (hsub (by simp)) hv
  · exact AdjacentDimension.Three123.finrank_ge_twentyFive h
      (hsub (by simp)) (hsub (by simp)) (hsub (by simp)) hv

private theorem adjacent_support_cases (J : Finset (Fin 4))
    (i j : Fin 4) (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 = j.val) :
    3 ≤ J.card ∨ J = {0, 1} ∨ J = {1, 2} ∨ J = {2, 3} := by
  revert J i j
  decide +kernel

/-- The exact adjacent-pair estimates finish the adjacent-support contract. -/
theorem adjacent_dimension_bound_of_pair_estimates
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (he : AdjacentDimension.EndPairBound σ)
    (hm : AdjacentDimension.MiddlePairBound σ) : AdjacentDimensionBound σ := by
  intro J v hv h i hi j hj hij
  rcases adjacent_support_cases J i j hi hj hij with hcard | rfl | rfl | rfl
  · exact finrank_ge_twentyFive_of_three_active h hv hcard
  · exact he _ v hv h (Or.inl rfl)
  · exact hm v hv h
  · exact he _ v hv h (Or.inr rfl)

/-- Every nonzero local highest vector with adjacent active roots in a faithful
irreducible binary SL₅ representation forces dimension at least twenty-five.
The support may contain additional active roots. -/
theorem adjacent_dimension_bound
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V)
    (hf : Function.Injective σ) (hi : IsIrreducible σ) : AdjacentDimensionBound σ := by
  exact adjacent_dimension_bound_of_pair_estimates σ
    (AdjacentDimension.end_pair_bound σ hf hi)
    (AdjacentDimension.middle_pair_bound σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph
