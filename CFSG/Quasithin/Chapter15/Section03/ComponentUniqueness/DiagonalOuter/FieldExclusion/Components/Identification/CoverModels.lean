module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Setup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.CoverModels.Models

/-!
# Odd centers and the two exceptional field covers

Apply the universal A.3.6 theorem to the actual two-core quotient of the
selected component. Quasisimplicity eliminates both noncomponent cases.
The odd center embeds in the quotient center, so divisibility by three
forces order three. Perfect central-cover transport preserves the simple
central quotient, and the orders of the three given models select SL₃(4)
and SL₃(7) from the full A.3.6 cover list.

The input is the published local `Input H K v`; the three-model central
quotient premise is supplied by the independent model sieve. The only
earlier source theorem parameter is the exact universal A.3.6 statement.
No quotient by a prime-to-three core occurs in this argument.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of
15.3.38, printed p.1137; A.3.6, pp.43--45; A.3.18, pp.51--52.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
open Chapter1.Section02 CoverModels
universe u
variable {G : Type u} [Group G] [Finite G] {H K : Subgroup G} {v : G}

/-- The odd-center and actual-cover alternative on p.1137, conditional only
on the three given central-quotient models and the universal earlier A.3.6. -/
theorem Input.oddCenter_coprime_or_exceptional (d : Input H K v)
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK CFSG.KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (hmodel : FieldComponentQuotient K) :
    Nat.Coprime 3 (Nat.card (oddCenterIn K)) ∨
      (ExceptionalFieldCover K ∧ Nat.card (oddCenterIn K) = 3) := by
  let := d.quasisimple
  rcases oddCenter_alternatives d hA36 with h | ⟨hz, hm⟩
  · exact Or.inl h
  right
  refine ⟨?_, hz⟩
  have hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
    rcases twoCore_alternatives d hA36 with h | h
    · have hd := card_dvd_of_injective (oddCenterMap (X := K)) oddCenterMap_injective
      rw [← card_oddCenterIn K, hz, h] at hd
      norm_num at hd
    · exact h.1
  have hc := field_quotient_card K hmodel
  have he := Nat.card_congr (twoCoreCover (X := K)).quotientCenterEquiv.toEquiv
  rw [he] at hc
  have horder := card_eq_card_quotient_mul_card_subgroup (center (K ⧸ pCore 2 K))
  rw [hcenter] at horder
  exact select_threeCover hm hcenter (by omega)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
