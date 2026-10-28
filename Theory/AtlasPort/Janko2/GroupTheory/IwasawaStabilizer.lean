/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors.
Adapted from ATLAS, Atlas/GroupTheory/IwasawaStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.GroupTheory.G2IwasawaStabilizer

/-!
# Iwasawa's point-stabilizer criterion

A faithful primitive perfect group is simple if the conjugates of an abelian
normal subgroup of a point stabilizer generate it. A nontrivial normal subgroup
acts transitively; the resulting factorization puts the commutator subgroup
inside it, and perfectness finishes the proof.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/IwasawaStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
The existing CFSG Lean 4.33 port supplies the same public `Atlas.GroupTheory`
declarations. This module re-exports that proof for the icosian construction
without duplicating declarations or changing their hypotheses.
-/
