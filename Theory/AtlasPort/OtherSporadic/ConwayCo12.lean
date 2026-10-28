/-
Copyright (c) 2026 Gerald Höhn.
The re-exported constructions are adapted from ATLAS, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway1
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2Simplicity
public import Theory.AtlasPort.OtherSporadic.Sporadic.Conway2Commutators

/-!
The actual Conway groups Co1 and Co2, with their orders and simplicity proofs.

`Atlas.Sporadic.Conway1.Model` is the central quotient of the Leech isometry
group. `Atlas.Sporadic.Conway2.Model` is the full stabilizer of the specified
norm-four Leech vector. Both inherit their group and finiteness instances;
their source namespaces export `card`, `isSimpleGroup`, and `exists_mul_ne_mul`.

The simplicity proofs use faithful primitive actions on crosses and orthogonal
minimum lines, together with normal generation by concrete Golay signs.
All construction, geometry, and generation interfaces are re-exported.

Source: Gerald Höhn, `Atlas/Sporadic/Conway1.lean`, `Conway2Simplicity.lean`,
and `Conway2Commutators.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
-/
