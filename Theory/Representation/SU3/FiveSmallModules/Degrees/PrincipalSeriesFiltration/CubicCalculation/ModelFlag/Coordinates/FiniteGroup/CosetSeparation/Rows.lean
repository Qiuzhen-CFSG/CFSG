module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.FiniteGroup.Data
/-!
# Projective separation of the 126 recorded last rows

For a row with nonzero first coordinate, normalize that coordinate to one and
encode the two F₅ coordinates of the second entry and the imaginary coordinate
of the third entry. The remaining recorded row gets code 125. A checked inverse
table recovers the original index from each of the 126 codes. Normalization is
invariant under nonzero scalar multiplication, so the recorded projective rows
are distinct.

Only the 126 inverse-table identities are computed, using kernel reduction.
The table refers to the unchanged matrices in `FiniteGroup.Data`; it does not
supply replacement representatives. The late-row benchmark took 0.29 seconds
of kernel checking; the full inverse-table check took 31.4 seconds, with about
2.1 GB peak memory including imports, before production assembly.

Source data: `Coordinates/source/upper_group_data.json`. Mathematical use:
Guralnick–Malle, Proposition 4.3, p.10, and Aschbacher–Smith K.2, p.453.
-/

public section

open BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Embedding
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup

private def rowCode (v : Fin 3 → Field) : Fin 126 :=
  if v 0 = 0 then 125 else
    Fin.ofNat 126 (5 * (5 * (v 1 / v 0).re.val + (v 1 / v 0).im.val) + (v 2 / v 0).im.val)

private def rowDecode : Fin 126 → Fin 126 :=
  ![2, 81, 27, 112, 48, 50, 6, 63, 36, 78, 67, 51, 15, 119,
    76, 83, 124, 8, 117, 74, 53, 18, 110, 13, 95, 20, 69, 116,
    38, 39, 99, 25, 56, 37, 62, 77, 55, 65, 123, 58, 5, 89,
    26, 52, 109, 32, 103, 11, 29, 113, 44, 10, 75, 85, 70, 66,
    79, 40, 21, 97, 92, 90, 91, 34, 31, 125, 71, 118, 107, 17,
    87, 7, 93, 120, 22, 19, 14, 54, 46, 59, 80, 57, 41, 42,
    86, 45, 100, 28, 72, 73, 115, 121, 96, 24, 9, 64, 102, 4,
    35, 111, 122, 12, 104, 82, 1, 68, 101, 30, 16, 105, 108, 94,
    47, 3, 60, 88, 43, 49, 61, 84, 114, 33, 23, 98, 106, 0]

private theorem decode_code (i : Fin 126) : rowDecode (rowCode (rawRepresentative i 2)) = i := by
  revert i
  decide +kernel

private theorem rowCode_scale (c : Field) (hc : c ≠ 0) (v : Fin 3 → Field) :
    rowCode (fun k => c * v k) = rowCode v := by
  simp only [rowCode, mul_eq_zero, hc, false_or, mul_div_mul_left _ _ hc]

/-- Nonzero scalar multiples among the recorded last rows have the same index. -/
theorem rawRepresentative_last_row_separates (i j : Fin 126) (c : Field) (hc : c ≠ 0)
    (h : ∀ k, rawRepresentative i 2 k = c * rawRepresentative j 2 k) : i = j := by
  calc
    i = rowDecode (rowCode (rawRepresentative i 2)) := (decode_code i).symm
    _ = rowDecode (rowCode (fun k => c * rawRepresentative j 2 k)) :=
      congrArg (fun v => rowDecode (rowCode v)) (funext h)
    _ = rowDecode (rowCode (rawRepresentative j 2)) :=
      congrArg rowDecode (rowCode_scale c hc _)
    _ = j := decode_code j

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
