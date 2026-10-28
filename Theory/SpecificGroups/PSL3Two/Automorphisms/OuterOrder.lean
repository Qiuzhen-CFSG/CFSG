module

public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Mathlib.GroupTheory.PGroup

/-!
# The order of Out(SL₃(2))

The checked automorphism-group order 336, centerlessness, and the group order
168 give index two for the actual inner automorphism subgroup. This supplies
the two-group outer action used in the Clifford calculation of
Aschbacher–Smith 13.8.21(1), printed p.956.
-/

public section

namespace Matrix.PSL3Two.Automorphisms
/-- The actual outer automorphism group of SL₃(2) has order two. -/
theorem card_outer_sl : Nat.card (MulAut.Outer SL) = 2 := by
  have hAut : Nat.card (MulAut SL) = 336 := by
    rw [Nat.card_congr (MulAut.congr Matrix.PSL3Two.equiv).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  have hi : Function.Injective (MulAut.conj : SL →* MulAut SL) :=
    MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot
  have hInner : Nat.card (MulAut.innerSubgroup SL) = 168 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact Matrix.PSL3Two.card_SL
  have h := (MulAut.innerSubgroup SL).card_mul_index
  rw [hAut, hInner] at h
  change (MulAut.innerSubgroup SL).index = 2
  omega

/-- The outer action of the binary three-dimensional special linear group
is a two-group. -/
theorem outer_sl_isTwoGroup : IsPGroup 2 (MulAut.Outer SL) :=
  IsPGroup.of_card (n := 1) card_outer_sl

end Matrix.PSL3Two.Automorphisms
