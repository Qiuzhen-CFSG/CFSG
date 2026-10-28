/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Fischer/CountingColumnRule.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Int.Basic

/-!
# CountingColumnArithmetic

Finite column intersection rules and signed histogram moments. The optional weight
checks four intersection sizes and records the resulting signed power. This
arithmetic layer is independent of the later interpretation by actual octads.

Source: Gerald Höhn, ATLAS, `Atlas/Fischer/CountingColumnRule.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adaptation: Lean 4.33.0 module boundaries and narrow arithmetic imports.
Definitions remain exposed for the downstream finite calculations.
-/

@[expose] public section

namespace Atlas.Fischer
open scoped BigOperators

abbrev CountingColumnVector := Fin 6 → ℕ

/-- The two allowed intersection sizes, with their actual delta values. -/
def countingColumnDelta (n : ℕ) : Option ℕ :=
  if n=0 then some 1 else if n=4 then some 0 else none

/-- The column sizes of G diamond H, with complement taken after symmetric difference. -/
def countingDiamondColumns (d : ℕ) (g b h : CountingColumnVector) : CountingColumnVector :=
  fun i => if d=0 then g i+b i-2*h i else 4-(g i+b i-2*h i)

/-- Literal source column-count-rule followed by signed-octad-summand.
The interpretation for actual octads is proved separately from this finite arithmetic. -/
def countingColumnWeight (epsilon : ℕ) (D E F : Finset (Fin 6))
    (g b h : CountingColumnVector) : Option ℤ := do
  let d0 ← countingColumnDelta (∑ i, h i)
  let d1 ← countingColumnDelta (∑ i ∈ D, g i)
  let d2 ← countingColumnDelta (∑ i ∈ E, b i)
  let j := countingDiamondColumns d0 g b h
  let d3 ← countingColumnDelta (∑ i ∈ F, j i)
  let d4 := (epsilon+d0+d1+d2+d3)%2
  let s := (∑ i ∈ E, g i)/2+(∑ i ∈ D ∩ E, b i)+(∑ i ∈ D, h i)
  return (-1 : ℤ)^(s+d0+d4)*(-3 : ℤ)^((d0+d1+d2+d3+d4-epsilon)/2)

/-- The six possible signed nonzero weights, in increasing order. -/
def countingSignedWeight (i : Fin 6) : ℤ := ![-9,-3,-1,1,3,9] i

abbrev CountingSignedHistogram := Fin 6 → ℕ

def countingWeightHistogram (w : Option ℤ) : CountingSignedHistogram :=
  fun i => if w=some (countingSignedWeight i) then 1 else 0

/-- The derivative at one of the source Laurent polynomial, retaining every sign. -/
def countingHistogramMoment (v : CountingSignedHistogram) : ℤ :=
  ∑ i, countingSignedWeight i*(v i : ℤ)

end Atlas.Fischer
