module

public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# Two-reduced quasisimple covers of the hexacode group

A quasisimple group with trivial two-core mapping onto the triple cover
of A₆ has the same central quotient. Its center is odd, so the Schur
multiplier bound leaves orders one and three. The first order would make
the group smaller than its image; the second gives equal orders and hence
injectivity of the original epimorphism. The actual map is retained.

Source: GLS3, Theorem 5.2.3(c); Aschbacher–Smith A.3.5 and the intrinsic
quotient step of 13.6.22, printed pp.43 and 932.
-/

public section
open Subgroup Theory.GroupTheory Atlas.Codes
namespace Representation.Hexacode

private theorem center_odd {H : Type*} [Group H] [Finite H]
    (hcore : pCore 2 H = ⊥) : Odd (Nat.card (center H)) := by
  by_contra hodd
  have hd : 2 ∣ Nat.card (center H) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center H) 2 hd
  let Z := (zpowers z).map (center H).subtype
  have hZc : Z ≤ center H := map_subtype_le _
  let : Z.Normal := ⟨fun x hx g => by
    rw [mem_center_iff.mp (hZc hx) g, mul_inv_cancel_right]
    exact hx⟩
  have hZp : IsPGroup 2 Z := by
    apply IsPGroup.of_card (n := 1)
    simp only [Z, card_map_of_injective (center H).subtype_injective,
      Nat.card_zpowers, hz, pow_one]
  have hle : Z ≤ pCore 2 H := le_sSup ⟨inferInstance, hZp⟩
  have hz1 : (z : H) = 1 := (hcore ▸ hle) (mem_map_of_mem _ (mem_zpowers z))
  have he : z = 1 := Subtype.ext hz1
  simp [he] at hz

/-- A two-reduced quasisimple epimorphism onto the concrete triple cover
is injective; the conclusion concerns the given map itself. -/
theorem injective_of_surjective_of_twoCore_eq_bot
    {H : Type*} [Group H] [Finite H] [IsQuasisimple H]
    (hcore : pCore 2 H = ⊥)
    (f : H →* HexEvenAutomorphisms) (hf : Function.Surjective f) :
    Function.Injective f := by
  let : IsQuasisimple HexEvenAutomorphisms := even_isQuasisimple
  let : Nontrivial HexEvenAutomorphisms := (Finite.one_lt_card_iff_nontrivial).mp
    (by rw [hexEven_card]; decide)
  let e := (IsQuasisimple.centralQuotientEquiv f hf).trans even_quotient_center_equiv
  have hquot : Nat.card (H ⧸ center H) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have horder := (center H).card_eq_card_quotient_mul_card_subgroup
  rw [hquot] at horder
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
      e (center_odd hcore) with hone | ⟨_, hthree⟩
  · have hle := Nat.card_le_card_of_surjective f hf
    rw [hexEven_card, horder, hone] at hle
    norm_num at hle
  · apply (Nat.bijective_iff_surjective_and_card f).mpr ⟨hf, ?_⟩ |>.1
    rw [horder, hthree, hexEven_card]

end Representation.Hexacode
