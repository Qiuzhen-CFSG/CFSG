module

public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Innerness at the second automorphism group of the Tits group

Parrott's group is simple and has certified order 17971200. A commutative
simple group has prime order, so its center must be trivial. The elementary
automorphism-tower argument therefore proves that every automorphism of
`Aut(ParrottGroup)` is inner.

This supplies the automorphism-theoretic part of the binary Ree reduction in
Aschbacher–Smith F.1.12, printed pp.263–264 of `refs/quasithin.pdf`.
The identification of the exceptional-twist fixed group `ReeF4.Model 0` with
`Aut(ParrottGroup)` is a separate, necessary model comparison. In particular
this result makes no claim that the outer group of the Tits simple group
has odd order.
-/

public section

namespace Tits

/-- The certified simple Tits group has trivial center. -/
theorem parrottGroup_center_eq_bot : Subgroup.center ParrottGroup = ⊥ := by
  rcases (inferInstance : (Subgroup.center ParrottGroup).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have : IsMulCommutative ParrottGroup := Subgroup.center_eq_top_iff.mp h
    have hp : (Nat.card ParrottGroup).Prime :=
      Group.is_simple_iff_prime_card.mp inferInstance
    rw [parrottGroup_card] at hp
    have htwo : 2 = 1 ∨ 2 = 17971200 := (Nat.dvd_prime hp).mp ⟨8985600, rfl⟩
    norm_num at htwo

/-- Every automorphism of the full automorphism group of the Tits simple
group is inner. -/
theorem aut_parrottGroup_inner (α : MulAut (MulAut ParrottGroup)) :
    ∃ g : MulAut ParrottGroup, MulAut.conj g = α :=
  MulAut.automorphismTower_inner_of_isSimpleGroup parrottGroup_center_eq_bot α

end Tits
