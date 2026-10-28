module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ResidueDiagonal
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.Operators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.FixedRows
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.RootEntries.Transport

/-!
# Assembly of diagonal root entries from residue constancy and pairing

There are three balanced central residues. The first E6 simple root supplies
a normalized residue-zero entry; the seventh ambient simple root and its
opposite anchor residues minus one and plus one. If entries are constant on
each residue class and the two anchor scalars multiply to one, they define
one field unit with the required values on all root coordinates.

Both extra premises remain genuine representation obligations. In E8,
constancy includes agreement between repeated E6 constituents. The pairing
must come from the actual evaluated-word action. Neither premise is proved
by this conditional assembly, and no cubic constraint is assumed.

Sources: GLS3 §§1.12.5–6 and 2.6.2, for Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- Assemble the E7 root entries from residue constancy and one actual opposite pair.
The two extra premises are separate representation obligations. -/
theorem e7Six_root_entries_of_constancy_and_pairing (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F)
    (hc : ∀ z, Commute (e7Six F w) (e7Six F z)) (hd : (e7Six F w).val.val.IsDiag)
    (hconstant : ∀ r t : typeE7Roots,
      balancedResidue (centralExponent e7Node (Sum.inr r)) =
        balancedResidue (centralExponent e7Node (Sum.inr t)) →
      (e7Six F w).val.val (Sum.inr r) (Sum.inr r) =
        (e7Six F w).val.val (Sum.inr t) (Sum.inr t))
    (hpair : let r : typeE7Roots := typeE7RootPairing_baseEquiv 6
      (e7Six F w).val.val
          (Sum.inr (typeE7RootPairing.reflectionPerm r r))
          (Sum.inr (typeE7RootPairing.reflectionPerm r r)) *
        (e7Six F w).val.val (Sum.inr r) (Sum.inr r) = 1) :
    ∃ u : Fˣ, ∀ r : typeE7Roots,
      (e7Six F w).val.val (Sum.inr r) (Sum.inr r) =
        ((u ^ balancedResidue (centralExponent e7Node (Sum.inr r)) : Fˣ) : F) := by
  apply exists_unit_of_residue_constancy
    (fun r => (e7Six F w).val.val (Sum.inr r) (Sum.inr r))
    (fun r => balancedResidue (centralExponent e7Node (Sum.inr r)))
    (e7Node 0) (typeE7RootPairing_baseEquiv 6)
    (typeE7RootPairing.reflectionPerm (typeE7RootPairing_baseEquiv 6)
      (typeE7RootPairing_baseEquiv 6))
    (fun r => by unfold balancedResidue; omega)
    e7_centralResidue_first e7_centralResidue_extra
    (by rw [centralResidue_opposite, e7_centralResidue_extra]; norm_num)
    (e7Six_diagonal_simple_root_eq_one F hodd w hc hd 0) hpair hconstant

/-- The same assembly forces agreement of all E8 copies when constancy is supplied.
No cubic constraint is used. -/
theorem e8Six_root_entries_of_constancy_and_pairing (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F)
    (hc : ∀ z, Commute (e8Six F w) (e8Six F z)) (hd : (e8Six F w).val.val.IsDiag)
    (hconstant : ∀ r t : typeE8Roots,
      balancedResidue (centralExponent e8Node (Sum.inr r)) =
        balancedResidue (centralExponent e8Node (Sum.inr t)) →
      (e8Six F w).val.val (Sum.inr r) (Sum.inr r) =
        (e8Six F w).val.val (Sum.inr t) (Sum.inr t))
    (hpair : let r : typeE8Roots := typeE8RootPairing_baseEquiv 6
      (e8Six F w).val.val
          (Sum.inr (typeE8RootPairing.reflectionPerm r r))
          (Sum.inr (typeE8RootPairing.reflectionPerm r r)) *
        (e8Six F w).val.val (Sum.inr r) (Sum.inr r) = 1) :
    ∃ u : Fˣ, ∀ r : typeE8Roots,
      (e8Six F w).val.val (Sum.inr r) (Sum.inr r) =
        ((u ^ balancedResidue (centralExponent e8Node (Sum.inr r)) : Fˣ) : F) := by
  apply exists_unit_of_residue_constancy
    (fun r => (e8Six F w).val.val (Sum.inr r) (Sum.inr r))
    (fun r => balancedResidue (centralExponent e8Node (Sum.inr r)))
    (e8Node 0) (typeE8RootPairing_baseEquiv 6)
    (typeE8RootPairing.reflectionPerm (typeE8RootPairing_baseEquiv 6)
      (typeE8RootPairing_baseEquiv 6))
    (fun r => by unfold balancedResidue; omega)
    e8_centralResidue_first e8_centralResidue_extra
    (by rw [centralResidue_opposite, e8_centralResidue_extra]; norm_num)
    (e8Six_diagonal_simple_root_eq_one F hodd w hc hd 0) hpair hconstant


end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
