module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.RootEntries.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.RootEntries.Constancy.Symmetries
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.TorusPlacement.ScalarShape.RootEntries.Constancy.FixedRoots

/-!
# Residue constancy from root orbits

Selected E6 reflections preserve the diagonal entries of a central word.
Root symmetries fixing the selected simple roots preserve the entire actual
word matrix, including its repeated E8 constituents. Orthogonal root rows
are fixed, and the E6 root orbit is normalized by its first simple root.

The two assembly theorems below consume only geometric coverage: the
nonzero residue fibers must be connected by the stated root operations,
and each residue-zero root must be in the E6 orbit or orthogonal to E6.
They do not prove that exhaustive root coverage. The unconditional E7 and
E8 residue-constancy theorems remain to be assembled after those inputs
are constructed. No inverse-pair identity or cubic constraint is used.

Sources: GLS3 §§1.12.5–6 and 2.6.2, for the higher subsystem inclusions
used in Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section

noncomputable section
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
attribute [local instance] Classical.decEq
local instance constancyAssemblyE7Fintype : Fintype typeE7Roots := Fintype.ofFinite _
local instance constancyAssemblyE8Fintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- Root geometry supplies the residue-constancy premise for the actual E7 word. -/
theorem e7Six_diagonal_residue_constancy_of_root_orbits (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F)
    (hc : ∀ z, Commute (e7Six F w) (e7Six F z)) (hd : (e7Six F w).val.val.IsDiag)
    (hzero : ∀ r : typeE7Roots,
      balancedResidue (centralExponent e7Node (Sum.inr r)) = 0 →
        SubsystemRootOrbit e7Node (e7Node 0) r ∨
          ∀ i, typeE7RootPairing.pairing r (e7Node i) = 0)
    (hnonzero : ∀ r t : typeE7Roots,
      balancedResidue (centralExponent e7Node (Sum.inr r)) ≠ 0 →
      balancedResidue (centralExponent e7Node (Sum.inr r)) =
        balancedResidue (centralExponent e7Node (Sum.inr t)) →
      SubsystemRootOrbit e7Node r t)
    (r t : typeE7Roots)
    (hrt : balancedResidue (centralExponent e7Node (Sum.inr r)) =
      balancedResidue (centralExponent e7Node (Sum.inr t))) :
    (e7Six F w).val.val (Sum.inr r) (Sum.inr r) =
      (e7Six F w).val.val (Sum.inr t) (Sum.inr t) := by
  have hz (r : typeE7Roots)
      (hr : balancedResidue (centralExponent e7Node (Sum.inr r)) = 0) :
      (e7Six F w).val.val (Sum.inr r) (Sum.inr r) = 1 := by
    rcases hzero r hr with h | h
    · exact (e7Six_diagonal_root_subsystemOrbit F w hc hd _ _ h).trans
        (e7Six_diagonal_simple_root_eq_one F hodd w hc hd 0)
    · simpa using e7Six_orthogonal_root_row F hodd w r h (Sum.inr r)
  by_cases hr : balancedResidue (centralExponent e7Node (Sum.inr r)) = 0
  · exact (hz r hr).trans (hz t (hrt.symm.trans hr)).symm
  · exact (e7Six_diagonal_root_subsystemOrbit F w hc hd r t (hnonzero r t hr hrt)).symm

/-- Root geometry supplies the residue-constancy premise for the actual E8 word. -/
theorem e8Six_diagonal_residue_constancy_of_root_orbits (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F)
    (hc : ∀ z, Commute (e8Six F w) (e8Six F z)) (hd : (e8Six F w).val.val.IsDiag)
    (hzero : ∀ r : typeE8Roots,
      balancedResidue (centralExponent e8Node (Sum.inr r)) = 0 →
        SubsystemRootOrbit e8Node (e8Node 0) r ∨
          ∀ i, typeE8RootPairing.pairing r (e8Node i) = 0)
    (hnonzero : ∀ r t : typeE8Roots,
      balancedResidue (centralExponent e8Node (Sum.inr r)) ≠ 0 →
      balancedResidue (centralExponent e8Node (Sum.inr r)) =
        balancedResidue (centralExponent e8Node (Sum.inr t)) →
      SubsystemRootOrbit e8Node r t)
    (r t : typeE8Roots)
    (hrt : balancedResidue (centralExponent e8Node (Sum.inr r)) =
      balancedResidue (centralExponent e8Node (Sum.inr t))) :
    (e8Six F w).val.val (Sum.inr r) (Sum.inr r) =
      (e8Six F w).val.val (Sum.inr t) (Sum.inr t) := by
  have hz (r : typeE8Roots)
      (hr : balancedResidue (centralExponent e8Node (Sum.inr r)) = 0) :
      (e8Six F w).val.val (Sum.inr r) (Sum.inr r) = 1 := by
    rcases hzero r hr with h | h
    · exact (e8Six_diagonal_root_subsystemOrbit F w hc hd _ _ h).trans
        (e8Six_diagonal_simple_root_eq_one F hodd w hc hd 0)
    · simpa using e8Six_orthogonal_root_row F hodd w r h (Sum.inr r)
  by_cases hr : balancedResidue (centralExponent e8Node (Sum.inr r)) = 0
  · exact (hz r hr).trans (hz t (hrt.symm.trans hr)).symm
  · exact (e8Six_diagonal_root_subsystemOrbit F w hc hd r t (hnonzero r t hr hrt)).symm

/-- The two complementary A2 root rows are fixed by every evaluated E6 word. -/
theorem e8Six_complement_root_row (F : Type*) [Field F]
    (hodd : Odd (ringChar F)) (w : SixNodeWord F) (k : Fin 2)
    (c : typeE8RootPairing_base.support ⊕ typeE8Roots) :
    (e8Six F w).val.val (Sum.inr (e8ComplementRoot k)) c =
      (1 : Matrix (typeE8RootPairing_base.support ⊕ typeE8Roots)
        (typeE8RootPairing_base.support ⊕ typeE8Roots) F)
        (Sum.inr (e8ComplementRoot k)) c :=
  e8Six_orthogonal_root_row F hodd w _ (e8ComplementRoot_orthogonal k) c

end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.TorusPlacement.ScalarShape
