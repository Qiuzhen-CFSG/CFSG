/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinCrossData.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinRational

/-!
# Eisenstein Cross Data

Explicit integral coordinates specify a marked real cross. Kernel-checked finite calculations certify the defining congruences and its diagonal Gram matrix.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinCrossData.lean`, revision
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

/-- A marked real cross in the Eisenstein congruence lattice. The marking
uses the retained binary-Golay coordinate order 8a+4b+c. -/
def eisensteinCrossVector : Fin 24 → EisensteinCoordinates :=
  ![![⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, -2⟩, ⟨4, 2⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 2⟩, ⟨2, -2⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -4⟩, ⟨2, 4⟩],
    ![⟨1, 2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, -2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-3, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩, ⟨-3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-3, 0⟩, ⟨3, 0⟩, ⟨-3, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -4⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨-2, 2⟩, ⟨4, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨4, 2⟩, ⟨-4, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨0, -2⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -2⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩],
    ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨2, 4⟩, ⟨2, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩],
    ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-4, -2⟩, ⟨2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 2⟩, ⟨1, 2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 2⟩, ⟨2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩],
    ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 2⟩],
    ![⟨-3, 0⟩, ⟨-3, 0⟩, ⟨3, 0⟩, ⟨3, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩],
    ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩]]

def eisensteinCrossLift (j : Fin 24) : ℤ :=
  ((eisensteinCrossVector j 0).re + (eisensteinCrossVector j 0).im) % 3

def eisensteinCrossWitness (j : Fin 24) : EisensteinCoordinates := fun i =>
  let r := (eisensteinCrossVector j i).re - eisensteinCrossLift j
  let s := (eisensteinCrossVector j i).im
  ⟨(-r + 2*s)/3, (-2*r+s)/3⟩

def eisensteinCrossSumWitness (j : Fin 24) : Eisenstein :=
  let z := (∑ i, eisensteinCrossVector j i) + 3 * (eisensteinCrossLift j : Eisenstein)
  ⟨(-z.re + 2*z.im)/9, (-2*z.re+z.im)/9⟩

theorem eisensteinCross_congruence_check : ∀ j : Fin 24,
    (∀ i, eisensteinCrossVector j i = (eisensteinCrossLift j : Eisenstein) +
      eisensteinTheta * eisensteinCrossWitness j i) ∧
    eisensteinWordResidue (eisensteinCrossWitness j) =
      ternaryEncoder (ternaryDecoder (eisensteinWordResidue (eisensteinCrossWitness j))) ∧
    (∑ i, eisensteinCrossVector j i) + 3 * (eisensteinCrossLift j : Eisenstein) =
      (3 * eisensteinTheta) * eisensteinCrossSumWitness j := by
  decide +kernel

theorem eisensteinCross_mem (j : Fin 24) :
    eisensteinCrossVector j ∈ eisensteinLeechModule := by
  obtain ⟨hc, ht, hs⟩ := eisensteinCross_congruence_check j
  refine ⟨(eisensteinCrossLift j : Eisenstein), eisensteinCrossWitness j, hc, ?_,
    ⟨eisensteinCrossSumWitness j, hs⟩⟩
  rw [ht]
  exact ⟨_, rfl⟩

/-- Twice the unscaled real pairing, retained over integers for the local Gram check. -/
def eisensteinIntegerPair (z w : EisensteinCoordinates) : ℤ :=
  ∑ i, (2*(z i).re*(w i).re - (z i).re*(w i).im -
    (z i).im*(w i).re + 2*(z i).im*(w i).im)

theorem eisensteinCross_gram_check : ∀ i j : Fin 24,
    eisensteinIntegerPair (eisensteinCrossVector i) (eisensteinCrossVector j) =
      if i = j then 72 else 0 := by
  decide +kernel

end Atlas.Lattices
