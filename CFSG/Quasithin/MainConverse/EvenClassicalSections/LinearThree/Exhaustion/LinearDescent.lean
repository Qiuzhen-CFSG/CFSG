module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Reduction
public import Theory.SpecificGroups.PSL3.EvenFieldOrderComparison

/-!
# Strict linear parameter descent

An injection of an actual PSL₃(2^m) model into a proper subgroup of PSL₃(2^f)
forces m < f. Otherwise the order comparison makes the inclusion of that
proper subgroup surjective. The source's stronger divisibility restrictions
are unnecessary for this implication.

Source: GLS3, Theorem 6.5.3(f), `refs/KGroup/GLS3/chapter6.tex`.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open Matrix Matrix.PSL3.LinearThree CFSG.KnownSimple
open scoped MatrixGroups

/-- An actual smaller linear model in a proper subgroup has a strictly smaller exponent. -/
public theorem linear_parameter_lt_of_injective {f m : ℕ} (hf : 0 < f)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (U : Subgroup PSL(3,F)) (hU : U ≠ ⊤)
    {L : Type} [Group L] (hL : ClassicalGroup.IsPSL L 3 (2 ^ m))
    (i : L →* U) (hi : Function.Injective i) : m < f := by
  by_contra hm
  have hfm : f ≤ m := by omega
  obtain ⟨E, _, _, hE, ⟨e⟩⟩ := hL
  have hcard := card_even_mono hf hfm F E hF hE
  have hLE : Nat.card L = Nat.card PSL(3,E) := Nat.card_congr e.toEquiv
  have hLU := Nat.card_le_card_of_injective i hi
  have hsurj : Function.Surjective U.subtype :=
    (U.subtype_injective.bijective_of_nat_card_le (by omega)).2
  apply hU
  apply top_unique
  intro g _
  obtain ⟨u,rfl⟩ := hsurj g
  exact u.property

end CFSG.Quasithin.MainConverse.LinearThreeSections
