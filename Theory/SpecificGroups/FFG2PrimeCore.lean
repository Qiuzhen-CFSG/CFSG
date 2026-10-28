module

public import Theory.SpecificGroups.FFClassicalPrimeCore
public import Theory.AtlasPort.G2
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Three-prime cores of the octonion FF models

For full G₂ over an even field, the source's quasisimplicity excludes the
binary endpoint: its actual derived subgroup has index two. Simplicity
and the order formula then eliminate the three-prime core. For G₂(2)',
the order 6048 is already established by the identification with the
long-root normal closure. Its center remains the explicit missing model
fact; the final classification assembly must discharge that premise.

Source application: Aschbacher–Smith, combined 1 March 2004 manuscript,
B.5.6(1), printed p.105. All octonion constructions and order results are
from the attributed ATLAS ports imported above.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups
theorem g2_threePrimeCore (F : Type*) [Field F] [Finite F] [IsQuasisimple (Atlas.G2.Model F)]
    (n : ℕ) (hc : Nat.card F = 2 ^ n) : pPrimeCore 3 (Atlas.G2.Model F) = ⊥ := by
  have hlarge : 2 < Nat.card F := by
    have hpos := Finite.one_lt_card (α := F)
    by_contra h
    have htwo : Nat.card F = 2 := by omega
    let e := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv htwo)
    let := IsQuasisimple.of_mulEquiv e
    have he := Group.IsPerfect.commutator_eq_top (G := Atlas.G2.Model (ZMod 2))
    have hcard := congrArg (fun S : Subgroup (Atlas.G2.Model (ZMod 2)) => Nat.card S) he
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure] at hcard
    rw [Atlas.G2.BinaryException.card_H, Nat.card_congr Subgroup.topEquiv.toEquiv,
      Atlas.G2.card_Model] at hcard
    norm_num only [Nat.card_zmod, Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceEqDiff] at hcard
  let := Atlas.G2.isSimple hlarge
  apply pPrimeCore_eq_bot_of_simple
  rw [Atlas.G2.card_Model, hc]
  exact dvd_mul_of_dvd_right (three_dvd_even_square_sub_one n) _

/-- The actual derived binary octonion group has order divisible by three. -/
theorem three_dvd_card_g2_derived_two :
    3 ∣ Nat.card (commutator (Atlas.G2.Model (ZMod 2))) := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
    Atlas.G2.BinaryException.card_H]
  decide

/-- The precise outstanding center calculation needed for the derived
binary model. Quasisimplicity is supplied by the source classification. -/
theorem g2_derived_two_threePrimeCore_of_center
    [IsQuasisimple (commutator (Atlas.G2.Model (ZMod 2)))]
    (hZ : IsPGroup 3 (center (commutator (Atlas.G2.Model (ZMod 2))))) :
    pPrimeCore 3 (commutator (Atlas.G2.Model (ZMod 2))) = ⊥ :=
  IsQuasisimple.pPrimeCore_eq_bot hZ three_dvd_card_g2_derived_two

end Theory.SpecificGroups
