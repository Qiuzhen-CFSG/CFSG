module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.Products
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.MaxJClassification

/-!
# The two dihedral action cases and the compatible Thompson product

`exists_decomposition` constructs every field of `Decomposition` from the
prepared local data and the explicit `RankGeometry` premise. Characteristic
rotations and the maximizing choice of `w ∈ {u,t*u}` give the two source action
alternatives and a dihedral factor with ambient center `⟨z⟩`.

The marked six-letter action proves the joint disjointness needed for the
three-factor product. Direct classification of the maximum elementary subgroups
of T₀ identifies J(T), without identifying the full first omega subgroup of T₀
with J(T). The resulting equivalence sends `(a,b,c)` to the ambient product
`a*b*c`. All existing product helpers are re-exported from `Products`.

The source-theorem assembly still constructs `Prepared` and `RankGeometry`;
this module discharges the conditional dihedral calculation completely.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 16.3.12,
printed pp.1181–1182 / PDF pp.1198–1199.
-/
