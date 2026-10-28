/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinPreimageData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinCrossData

/-!
# Eisenstein Preimage Data

Explicit integral vectors provide preimages for the retained Leech generating vectors. Kernel-checked residue and sum calculations certify their membership in the congruence lattice.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinPreimageData.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- Integral preimages of the retained Leech generating vectors under the marked comparison. -/
def eisensteinLeechPreimage : Fin 38 → EisensteinCoordinates :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨-1, -2⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨-2, -1⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨-2, -1⟩, ⟨2, 1⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-3, -2⟩],
    ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-3, -2⟩],
    ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-2, -2⟩],
    ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨-2, 0⟩],
    ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-3, -1⟩],
    ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨3, 1⟩, ⟨-1, -1⟩],
    ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-3, -2⟩],
    ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-2, 0⟩],
    ![⟨-2, -1⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩],
    ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-3, -1⟩],
    ![⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, -2⟩, ⟨4, 2⟩],
    ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩, ⟨0, 0⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨3, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩],
    ![⟨-2, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩],
    ![⟨-2, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩],
    ![⟨-2, -1⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-2, -1⟩, ⟨2, 1⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-3, -2⟩, ⟨1, 0⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨2, 1⟩, ⟨-2, -1⟩, ⟨2, 1⟩],
    ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨2, 1⟩, ⟨-2, -1⟩, ⟨2, 1⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-3, -1⟩, ⟨1, 1⟩],
    ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -2⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩],
    ![⟨-2, -1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

def eisensteinLeechPreimageLift (j : Fin 38) : ℤ :=
  ((eisensteinLeechPreimage j 0).re + (eisensteinLeechPreimage j 0).im) % 3

def eisensteinLeechPreimageWitness (j : Fin 38) : EisensteinCoordinates := fun i =>
  let r := (eisensteinLeechPreimage j i).re - eisensteinLeechPreimageLift j
  let s := (eisensteinLeechPreimage j i).im
  ⟨(-r + 2*s)/3, (-2*r+s)/3⟩

def eisensteinLeechPreimageSumWitness (j : Fin 38) : Eisenstein :=
  let z := (∑ i, eisensteinLeechPreimage j i) + 3 * (eisensteinLeechPreimageLift j : Eisenstein)
  ⟨(-z.re + 2*z.im)/9, (-2*z.re+z.im)/9⟩

theorem eisensteinLeechPreimage_congruence_check : ∀ j : Fin 38,
    (∀ i, eisensteinLeechPreimage j i = (eisensteinLeechPreimageLift j : Eisenstein) +
      eisensteinTheta * eisensteinLeechPreimageWitness j i) ∧
    eisensteinWordResidue (eisensteinLeechPreimageWitness j) =
      ternaryEncoder (ternaryDecoder (eisensteinWordResidue (eisensteinLeechPreimageWitness j))) ∧
    (∑ i, eisensteinLeechPreimage j i) + 3 * (eisensteinLeechPreimageLift j : Eisenstein) =
      (3 * eisensteinTheta) * eisensteinLeechPreimageSumWitness j := by
  decide +kernel

theorem eisensteinLeechPreimage_mem (j : Fin 38) :
    eisensteinLeechPreimage j ∈ eisensteinLeechModule := by
  obtain ⟨hc, ht, hs⟩ := eisensteinLeechPreimage_congruence_check j
  refine ⟨(eisensteinLeechPreimageLift j : Eisenstein), eisensteinLeechPreimageWitness j, hc, ?_,
    ⟨eisensteinLeechPreimageSumWitness j, hs⟩⟩
  rw [ht]
  exact ⟨_, rfl⟩

end Atlas.Lattices
