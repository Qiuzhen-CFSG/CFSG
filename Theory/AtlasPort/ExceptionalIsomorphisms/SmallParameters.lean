module

public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360

/-!
# Exceptional comparisons at the small field parameters

This interface collects PSL₂(4) ≃ A₅, PSL₂(7) ≃ PSL₃(2), and PSL₂(9) ≃ A₆.
The first uses the existing CFSG proof via the faithful five-point projective
action. The latter two reuse the ported ATLAS eight-point and ten-point action
comparisons. Field transport makes the order-seven comparison independent of
the field implementation, as already done for orders four and nine.

Source interfaces: Gerald Höhn and the ATLAS contributors,
`Atlas/Comparisons/Exceptional/Order60Four.lean`, `Order168.lean`, and
`Order360.lean`, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Changes: reuse the existing CFSG order-four construction in place of the
icosian construction, and add uniform field transport at order seven.
ATLAS Research and Attribution License 1.0 applies to adapted material;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
noncomputable section

namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups

local instance smallParametersPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The existing faithful projective action gives the comparison over any
four-element field, without an additional characteristic assumption. -/
def psl2Card4EquivAlt5 {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4) :
    PSL(2, F) ≃* alternatingGroup (Fin 5) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some

/-- The canonical field realizes the order-four comparison. -/
def psl2FourEquivAlt5 : PSL(2, GaloisField 2 2) ≃* alternatingGroup (Fin 5) :=
  psl2Card4EquivAlt5 (by rw [GaloisField.card 2 2 (by decide)]; norm_num)

/-- A seven-element field is isomorphic to the actual prime field. -/
def cardSevenFieldEquiv {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7) :
    F ≃+* ZMod 7 := by
  letI := Fintype.ofFinite F
  exact (ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm

/-- Transport of the checked eight-point action comparison to any
seven-element field. -/
def psl2Card7EquivPsl3Two {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 7) :
    PSL(2, F) ≃* PSL(3, ZMod 2) :=
  (Atlas.fieldEquivPSL (F := F) (K := ZMod 7) 2 (cardSevenFieldEquiv hF)).trans
    psl2SevenEquivPsl3Two

end Atlas.Comparisons.Exceptional
