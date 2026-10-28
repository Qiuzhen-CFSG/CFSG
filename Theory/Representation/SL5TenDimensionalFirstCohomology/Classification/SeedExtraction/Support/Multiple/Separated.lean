module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Operators
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case02
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case03
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case13
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case012
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case013
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case023
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case123
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated.Case0123
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Separated active roots force dimension at least eleven

For each support containing two separated roots, eleven permutation translates
of the highest vector admit triangular coefficient extractors. Each extractor
is a product of at most two transvection differences. It kills all preceding
translates and sends its own translate to a nonzero permutation translate.
The eight finite certificates allow additional active roots and use neither
irreducibility nor torus weight separation.

`Separated.Extraction` proves the extraction and independence criteria. The
`Separated.Case*` modules verify the concrete matrix identities and apply these
criteria. Here we exhaust the possible supports and conclude the dimension
bound, hence exclude dimension ten.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

private theorem separated_support_cases (J : Finset (Fin 4)) (i j : Fin 4)
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 < j.val) :
    J = {0, 2} ∨ J = {0, 3} ∨ J = {1, 3} ∨ J = {0, 1, 2} ∨
      J = {0, 1, 3} ∨ J = {0, 2, 3} ∨ J = {1, 2, 3} ∨ J = {0, 1, 2, 3} := by
  revert J i j
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Separated active roots yield eleven independent translates, without irreducibility. -/
theorem LocalHighestVector.eleven_le_finrank_of_separated [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) {i j : Fin 4}
    (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 < j.val) :
    11 ≤ Module.finrank (ZMod 2) V := by
  rcases separated_support_cases J i j hi hj hij with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Separated.Case02.eleven_le h hv
  · exact Separated.Case03.eleven_le h hv
  · exact Separated.Case13.eleven_le h hv
  · exact Separated.Case012.eleven_le h hv
  · exact Separated.Case013.eleven_le h hv
  · exact Separated.Case023.eleven_le h hv
  · exact Separated.Case123.eleven_le h hv
  · exact Separated.Case0123.eleven_le h hv

/-- A ten-dimensional binary SL₅ module cannot have separated active highest-vector roots. -/
theorem LocalHighestVector.false_of_finrank_ten_of_separated
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) (hdim : Module.finrank (ZMod 2) V = 10)
    {i j : Fin 4} (hi : i ∈ J) (hj : j ∈ J) (hij : i.val + 1 < j.val) : False := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := V) (by omega)
  have hh := h.eleven_le_finrank_of_separated hv hi hj hij
  omega

end Representation.SL5TenDimensional.Classification
