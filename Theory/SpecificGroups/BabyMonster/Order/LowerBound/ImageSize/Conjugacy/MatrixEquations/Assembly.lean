module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.Data
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.Conjugacy.MatrixEquations.Packed

/-!
# Assembly of the concrete conjugacy matrix equations

The literal matrices in `Conjugacy.Data` use exactly the blocked-row decoding
of `Packed`. Thus three families of natural-number row equalities suffice:
one inverse product and two intertwining equations. The other inverse product
follows from finiteness of the matrix monoid. These are certificate interfaces;
the numerical row equalities must be supplied by separate kernel proofs.

See `Conjugacy/source/README.md` for the construction and provenance of the
literal matrices and the right-conjugation convention.
-/

namespace BabyMonster.OrderLowerBound.ConjugacyCertificate

/-- The single packed inverse check implies both inverse identities. -/
public theorem inverse_of_rows
    (h : ∀ i : Fin 4370,
      product (row conjugacyQBlocks i.val) conjugacyQInvBlocks 4370 = 2 ^ i.val) :
    conjugacyQ * conjugacyQInv = 1 ∧ conjugacyQInv * conjugacyQ = 1 := by
  have he : conjugacyQ * conjugacyQInv = 1 := decode_mul_one 4370 _ _ h
  exact ⟨he, matrix_reverse_inverse 4370 _ _ he⟩

/-- A packed row certificate for the first intertwining equation. -/
public theorem intertwineA_of_rows
    (h : ∀ i : Fin 4370,
      product (row atlasABlocks i.val) conjugacyQBlocks 4370 =
      product (row conjugacyQBlocks i.val) conjugacyRecoveredABlocks 4370) :
    atlasA * conjugacyQ = conjugacyQ * conjugacyA :=
  decode_mul_eq 4370 _ _ _ _ h

/-- A packed row certificate for the second intertwining equation. -/
public theorem intertwineB_of_rows
    (h : ∀ i : Fin 4370,
      product (row atlasBBlocks i.val) conjugacyQBlocks 4370 =
      product (row conjugacyQBlocks i.val) conjugacyRecoveredBBlocks 4370) :
    atlasB * conjugacyQ = conjugacyQ * conjugacyB :=
  decode_mul_eq 4370 _ _ _ _ h

end BabyMonster.OrderLowerBound.ConjugacyCertificate
