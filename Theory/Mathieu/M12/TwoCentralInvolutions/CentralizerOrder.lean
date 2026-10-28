module

public import Theory.Mathieu.M12.TwoCentralInvolutions
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore.Order
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The order of a two-central involution centralizer in M₁₂

Sylow conjugacy identifies the two-central involution with the marked
SmallParabolicPair element z. Its full centralizer is the first parabolic,
whose checked order is 192. This is class 2B, not the class 2A whose
centralizer order is divisible by five.

Source: GLS3 Table 5.3b; Aschbacher–Smith 14.7.68(2), printed p.1071.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.Mathieu

/-- The literal centralizer of every two-central M₁₂ involution has order 192. -/
theorem M12Involutions.card_centralizer_of_twoCentral (x : M12)
    (hx : orderOf x = 2) (hc : TwoCentral x) :
    Nat.card (centralizer ({x} : Set M12)) = 192 := by
  rw [← card_centralizer_eq_of_isConj _ _ (M12Involutions.isConj_z_of_twoCentral x hx hc)]
  exact M12SmallPair.card_firstParabolic

end Sporadic.Mathieu
