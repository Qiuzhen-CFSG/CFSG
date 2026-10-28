module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.LocalData
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Operators
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Adjacent
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support.Multiple.Separated
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Multiple-root support: local estimates and assembly

`Multiple.Operators` proves the coefficient-extraction identities and initial
independence estimates for active simple roots. The adjacent and separated
certificates strengthen these estimates to exclude dimension ten. Choosing and
ordering two distinct support elements shows that the two cases cover every
support of size at least two.

The source application is Aschbacher--Smith, *The Classification of Quasithin
Groups*, I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Assemble the multiple-support contradiction from the adjacent and separated pair exclusions. -/
theorem LocalHighestVector.false_of_finrank_ten_of_pair_exclusions
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    (hdim : Module.finrank (ZMod 2) V = 10) (hcard : 2 ≤ J.card)
    (hadjacent : ∀ {K : Finset (Fin 4)} {w : V}, LocalHighestVector ρ K w → w ≠ 0 →
      Module.finrank (ZMod 2) V = 10 →
      ∀ i ∈ K, ∀ j ∈ K, i.val + 1 = j.val → False)
    (hseparated : ∀ {K : Finset (Fin 4)} {w : V}, LocalHighestVector ρ K w → w ≠ 0 →
      Module.finrank (ZMod 2) V = 10 →
      ∀ i ∈ K, ∀ j ∈ K, i.val + 1 < j.val → False) : False := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
  have hp (a b : Fin 4) (ha : a ∈ J) (hb : b ∈ J) (hab : a < b) : False := by
    by_cases hn : a.val + 1 = b.val
    · exact hadjacent h hv hdim a ha b hb hn
    · exact hseparated h hv hdim a ha b hb (by omega)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hp i j hi hj hij
  · exact hp j i hj hi hji

/-- Multiple active roots force at least eleven independent vectors. -/
theorem LocalHighestVector.eleven_le_finrank_of_multiple
    [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) Group V} {J : Finset (Fin 4)} {v : V}
    (h : LocalHighestVector ρ J v) (hv : v ≠ 0) (hcard : 2 ≤ J.card) :
    11 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
  have hp (a b : Fin 4) (ha : a ∈ J) (hb : b ∈ J) (hab : a < b) :
      11 ≤ Module.finrank (ZMod 2) V := by
    by_cases hn : a.val + 1 = b.val
    · have hh := h.twelve_le_finrank_of_adjacent hv ha hb hn
      omega
    · exact h.eleven_le_finrank_of_separated hv ha hb (by omega)
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hp i j hi hj hij
  · exact hp j i hj hi hji

/-- A ten-dimensional binary SL₅ module cannot have multiple active roots. -/
theorem LocalHighestVector.false_of_finrank_ten_of_multiple
    {ρ : Representation (ZMod 2) Group V} [IsIrreducible ρ]
    {J : Finset (Fin 4)} {v : V} (h : LocalHighestVector ρ J v) (hv : v ≠ 0)
    (hdim : Module.finrank (ZMod 2) V = 10) (hcard : 2 ≤ J.card) : False := by
  let := Module.finite_of_finrank_pos (R := ZMod 2) (M := V) (by omega)
  have hh := h.eleven_le_finrank_of_multiple hv hcard
  omega

end Representation.SL5TenDimensional.Classification
