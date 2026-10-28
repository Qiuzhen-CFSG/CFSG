/-
Copyright (c) 2026 Gerald Höhn.
The re-exported constructions are adapted from ATLAS, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.ConwayCo12
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Simplicity
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway3Geometry
public import Theory.AtlasPort.OtherSporadic.McLaughlinModel

/-!
# The Conway and McLaughlin groups on the Leech lattice

This interface exports the four concrete carriers in the namespaces
`Atlas.Sporadic.Conway1`, `Conway2`, `Conway3`, and `McLaughlin`:

* Co1 is `LeechCentralQuotient`, the full Leech isometry group modulo its
  central signs, of order 4157776806543360000.
* Co2 is the full stabilizer of the specified norm-four vector, of order
  42305421312000.
* Co3 is the full stabilizer of the specified norm-six vector, of order
  495766656000.
* McL is `McLModel`, the pointwise stabilizer of the specified 2-2-3 triangle
  inside Co3, of order 898128000.

Each namespace exports `Model`, `finite`, `card`, `isSimpleGroup`, and
`exists_mul_ne_mul`. Group and finiteness instances are inherited from the
actual quotient and subgroups; the instances below register the proved
simplicity results. The quotient projection, vector-stabilizer embeddings
and McL embedding into Co3 are re-exported with their kernel or injectivity
proofs.

The order proofs use the concrete lattice orbits and stabilizers. Simplicity
of Co1 and Co2 follows from primitive actions and normal generation by Golay
signs. Co3 uses its primitive decomposition action and a simple Mathieu23
triangle stabilizer. McL uses its primitive triangle action, simple Mathieu22
stabilizer and the second action on the 275 graph vertices.

Source: Gerald Höhn, ATLAS, `Atlas/Sporadic/Conway1.lean`, `Conway2.lean`,
`Conway2Simplicity.lean`, `Conway2Commutators.lean`, `Conway3.lean`,
`Conway3Simplicity.lean`, `Conway3Geometry.lean`, `McLaughlin.lean`,
`McLaughlinSimplicity.lean`, and `McLaughlinGraph.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`. The imported ports preserve
their mathematical namespaces and adapt module boundaries to Lean 4.33.0.

These lattice constructions are separate from the ATLAS matrix and
permutation carriers in `Theory.SpecificGroups.LeechRelated.AtlasCarriers`.
Transport to those carriers requires a comparison isomorphism.
-/

public section

namespace Atlas.Sporadic

instance Conway1.instIsSimpleGroupModel : IsSimpleGroup Conway1.Model :=
  Conway1.isSimpleGroup

instance Conway2.instIsSimpleGroupModel : IsSimpleGroup Conway2.Model :=
  Conway2.isSimpleGroup

instance Conway3.instIsSimpleGroupModel : IsSimpleGroup Conway3.Model :=
  Conway3.isSimpleGroup

instance McLaughlin.instIsSimpleGroupModel : IsSimpleGroup McLaughlin.Model :=
  McLaughlin.isSimpleGroup

end Atlas.Sporadic
