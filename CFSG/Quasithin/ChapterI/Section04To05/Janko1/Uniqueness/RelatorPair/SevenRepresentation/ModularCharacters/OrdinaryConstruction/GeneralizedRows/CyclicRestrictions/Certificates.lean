module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.CyclicRestrictions.FourierData

/-!
# Checked integer Fourier identities

Each certificate asserts equality of integer coefficient lists, including the
cyclotomic multiple. Kernel reduction checks all fifteen rows on every power
of each of the fifteen class representatives. See `FourierData.lean` for the
GPL-3.0-or-later attribution of the derived numerical material.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.CyclicRestrictions
open CyclicCharacterPolynomial

private theorem certificate_0 (i : Fin 15) (k : Fin 1) : certificate 0 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_1 (i : Fin 15) (k : Fin 2) : certificate 1 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_2 (i : Fin 15) (k : Fin 3) : certificate 2 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_3 (i : Fin 15) (k : Fin 5) : certificate 3 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_4 (i : Fin 15) (k : Fin 5) : certificate 4 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_5 (i : Fin 15) (k : Fin 6) : certificate 5 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_6 (i : Fin 15) (k : Fin 7) : certificate 6 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_7 (i : Fin 15) (k : Fin 10) : certificate 7 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_8 (i : Fin 15) (k : Fin 10) : certificate 8 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_9 (i : Fin 15) (k : Fin 11) : certificate 9 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_10 (i : Fin 15) (k : Fin 15) : certificate 10 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_11 (i : Fin 15) (k : Fin 15) : certificate 11 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_12 (i : Fin 15) (k : Fin 19) : certificate 12 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_13 (i : Fin 15) (k : Fin 19) : certificate 13 i k := by
  unfold certificate
  revert i k
  decide +kernel

private theorem certificate_14 (i : Fin 15) (k : Fin 19) : certificate 14 i k := by
  unfold certificate
  revert i k
  decide +kernel

public theorem certificates (j i : Fin 15) (k : Fin (classOrder j)) : certificate j i k := by
  fin_cases j
  · exact certificate_0 i k
  · exact certificate_1 i k
  · exact certificate_2 i k
  · exact certificate_3 i k
  · exact certificate_4 i k
  · exact certificate_5 i k
  · exact certificate_6 i k
  · exact certificate_7 i k
  · exact certificate_8 i k
  · exact certificate_9 i k
  · exact certificate_10 i k
  · exact certificate_11 i k
  · exact certificate_12 i k
  · exact certificate_13 i k
  · exact certificate_14 i k


end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.CyclicRestrictions
