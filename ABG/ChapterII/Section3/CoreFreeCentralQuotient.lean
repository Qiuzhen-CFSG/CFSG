module
public import Theory.GroupTheory.CentralTwoQuotientOddCore

/-!
# Odd-core descent through a central 2-subgroup

Compatibility interface for ABG II.3. The reusable proof now lives in
Theory.GroupTheory.CentralTwoQuotientOddCore.
-/

namespace ABG

/-- A central 2-quotient of a finite group with trivial odd core has trivial odd core. -/
public theorem oddCore_quotient_eq_bot_of_central_two_subgroup
    {G : Type*} [Group G] [Finite G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hZtwo : IsPGroup 2 Z)
    (hcore : pPrimeCore 2 G = ⊥) : pPrimeCore 2 (G ⧸ Z) = ⊥ :=
  Subgroup.pPrimeCore_quotient_eq_bot_of_central_two_subgroup Z hZ hZtwo hcore

end ABG
