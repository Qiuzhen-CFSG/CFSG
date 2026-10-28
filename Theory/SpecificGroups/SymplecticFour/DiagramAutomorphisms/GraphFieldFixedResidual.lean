module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.Basic
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual.Nonbinary

/-!
# Graph-field fixed residuals: field transport and conditional assembly

The explicit graph-field action and its restriction to the derived carrier
are defined in `Basic`. The nonbinary residual and Sylow-index consequences
of an actual Suzuki equivalence are proved in `Nonbinary`.

Here a fixed-group equivalence over the standard binary Galois field is
transported to any finite characteristic-two field of the same order. Its
matrix compatibility is retained in the fixed coordinate convention. The
standard-field equivalence remains an explicit input: neither this module
nor its imports currently construct it. The binary derived fixed residual
also remains a separate calculation, so this is not yet source 16.1.4(7).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 16.1.4(7) and 16.1.8, printed pp.1171–1173.
-/

@[expose] public noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A coefficient-field identification with the field of the Suzuki generators. -/
def coefficientFieldEquiv (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1)) :
    F ≃+* BinaryGaloisField (2 * m + 1) := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (BinaryGaloisField (2 * m + 1))
  apply FiniteField.ringEquivOfCardEq
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF]
  exact (GaloisField.card 2 (2 * m + 1) (by omega)).symm

/-- Transport a genuine standard-field fixed-group equivalence to the given field. -/
def fixedEquivOfBinaryModel (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1))
    (e : (graphFieldAut (F := BinaryGaloisField (2 * m + 1)) m).fixedSubgroup ≃*
      SuzukiMatrixGroup m) :
    (graphFieldAut (F := F) m).fixedSubgroup ≃* SuzukiMatrixGroup m :=
  (fixedFieldEquiv m (coefficientFieldEquiv m hF)).trans e

/-- The transported equivalence preserves the specified matrix embedding. -/
theorem fixedEquivOfBinaryModel_matrix (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1))
    (e : (graphFieldAut (F := BinaryGaloisField (2 * m + 1)) m).fixedSubgroup ≃*
      SuzukiMatrixGroup m)
    (he : ∀ g, ((e g : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) =
        matrixCoordinates (RingEquiv.refl _) (g : Sp _))
    (g : (graphFieldAut (F := F) m).fixedSubgroup) :
    ((fixedEquivOfBinaryModel m hF e g : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) =
        matrixCoordinates (coefficientFieldEquiv m hF) (g : Sp F) := by
  change ((e (fixedFieldEquiv m (coefficientFieldEquiv m hF) g) :
    GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
      Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) = _
  rw [he, fixedFieldEquiv_coe]
  rfl

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
