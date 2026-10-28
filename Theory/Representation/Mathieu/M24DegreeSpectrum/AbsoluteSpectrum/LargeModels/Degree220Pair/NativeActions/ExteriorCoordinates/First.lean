module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Evaluation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.First.Packed
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.First.Columns

/-!
# The first native fifth compound matrix

The packed input columns have their exact native-entry specification in
`First.Columns`. The sound five-by-five circuit evaluates all 462 minor
columns simultaneously. The kernel checks the resulting rows in groups of
fourteen; together they cover all 462 rows. Applying the Boolean determinant
soundness theorem gives the literal matrix equality in column convention.

No representation, irreducibility, presentation, or spectrum premise is used.
Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
`NativeActions/source/README.md` fixes the native matrices and subset order.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
namespace First

/-- All 462 minors with the fixed row subset, packed into one natural number. -/
def packedRowA (i : Fin 462) : ℕ :=
  packedFive (fun k l => columnA (fiveTuple i k) l)

/-- The packed circuit computes the same minor as the proved Boolean evaluator. -/
lemma packedRowA_bit (i j : Fin 462) :
    (packedRowA i).testBit j.val = compoundBit false i j := by
  rw [packedRowA, packedFive_bit]
  unfold compoundBit
  congr 1
  funext k l
  exact columnA_bits (fiveTuple i k) l j

-- The representative fourteen-row kernel check used 4.31 seconds.
-- Keep the reduction caches of the following certificates from overlapping.
set_option Elab.async false

private theorem rows_00 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (0 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (0 + i.val)).val]! := by
  decide +kernel

private theorem rows_01 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (14 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (14 + i.val)).val]! := by
  decide +kernel

private theorem rows_02 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (28 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (28 + i.val)).val]! := by
  decide +kernel

private theorem rows_03 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (42 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (42 + i.val)).val]! := by
  decide +kernel

private theorem rows_04 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (56 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (56 + i.val)).val]! := by
  decide +kernel

private theorem rows_05 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (70 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (70 + i.val)).val]! := by
  decide +kernel

private theorem rows_06 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (84 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (84 + i.val)).val]! := by
  decide +kernel

private theorem rows_07 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (98 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (98 + i.val)).val]! := by
  decide +kernel

private theorem rows_08 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (112 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (112 + i.val)).val]! := by
  decide +kernel

private theorem rows_09 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (126 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (126 + i.val)).val]! := by
  decide +kernel

private theorem rows_10 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (140 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (140 + i.val)).val]! := by
  decide +kernel

private theorem rows_11 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (154 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (154 + i.val)).val]! := by
  decide +kernel

private theorem rows_12 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (168 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (168 + i.val)).val]! := by
  decide +kernel

private theorem rows_13 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (182 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (182 + i.val)).val]! := by
  decide +kernel

private theorem rows_14 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (196 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (196 + i.val)).val]! := by
  decide +kernel

private theorem rows_15 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (210 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (210 + i.val)).val]! := by
  decide +kernel

private theorem rows_16 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (224 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (224 + i.val)).val]! := by
  decide +kernel

private theorem rows_17 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (238 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (238 + i.val)).val]! := by
  decide +kernel

private theorem rows_18 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (252 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (252 + i.val)).val]! := by
  decide +kernel

private theorem rows_19 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (266 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (266 + i.val)).val]! := by
  decide +kernel

private theorem rows_20 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (280 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (280 + i.val)).val]! := by
  decide +kernel

private theorem rows_21 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (294 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (294 + i.val)).val]! := by
  decide +kernel

private theorem rows_22 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (308 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (308 + i.val)).val]! := by
  decide +kernel

private theorem rows_23 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (322 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (322 + i.val)).val]! := by
  decide +kernel

private theorem rows_24 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (336 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (336 + i.val)).val]! := by
  decide +kernel

private theorem rows_25 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (350 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (350 + i.val)).val]! := by
  decide +kernel

private theorem rows_26 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (364 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (364 + i.val)).val]! := by
  decide +kernel

private theorem rows_27 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (378 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (378 + i.val)).val]! := by
  decide +kernel

private theorem rows_28 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (392 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (392 + i.val)).val]! := by
  decide +kernel

private theorem rows_29 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (406 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (406 + i.val)).val]! := by
  decide +kernel

private theorem rows_30 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (420 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (420 + i.val)).val]! := by
  decide +kernel

private theorem rows_31 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (434 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (434 + i.val)).val]! := by
  decide +kernel

private theorem rows_32 : ∀ i : Fin 14,
    packedRowA (Fin.ofNat 462 (448 + i.val)) =
      exteriorRowsA[(Fin.ofNat 462 (448 + i.val)).val]! := by
  decide +kernel

/-- The thirty-three checked groups exhaust the literal exterior row indices. -/
theorem packedRowA_eq (i : Fin 462) : packedRowA i = exteriorRowsA[i.val]! := by
  have h : ∀ (b : Fin 33) (k : Fin 14),
      packedRowA (Fin.ofNat 462 (14 * b.val + k.val)) =
        exteriorRowsA[(Fin.ofNat 462 (14 * b.val + k.val)).val]! := by
    intro b
    fin_cases b
    · exact rows_00
    · exact rows_01
    · exact rows_02
    · exact rows_03
    · exact rows_04
    · exact rows_05
    · exact rows_06
    · exact rows_07
    · exact rows_08
    · exact rows_09
    · exact rows_10
    · exact rows_11
    · exact rows_12
    · exact rows_13
    · exact rows_14
    · exact rows_15
    · exact rows_16
    · exact rows_17
    · exact rows_18
    · exact rows_19
    · exact rows_20
    · exact rows_21
    · exact rows_22
    · exact rows_23
    · exact rows_24
    · exact rows_25
    · exact rows_26
    · exact rows_27
    · exact rows_28
    · exact rows_29
    · exact rows_30
    · exact rows_31
    · exact rows_32
  have hi : Fin.ofNat 462 (14 * (i.val / 14) + i.val % 14) = i := by
    apply Fin.ext
    change (14 * (i.val / 14) + i.val % 14) % 462 = i.val
    omega
  have hh := h ⟨i.val / 14, by omega⟩ ⟨i.val % 14, Nat.mod_lt _ (by decide)⟩
  simpa only [hi] using hh

end First

/-- The literal fifth compound matrix of the first native generator. -/
theorem compoundMatrix_first : compoundMatrix (codeMatrix false) = exteriorMatrix false := by
  apply compoundMatrix_eq_of_bits false
  intro i j
  rw [← First.packedRowA_bit, First.packedRowA_eq]
  rfl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
