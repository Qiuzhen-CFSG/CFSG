module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.FieldAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.Inputs

/-!
# Field-factor calculation on the original Hall subgroup

The odd Hall assumption gives odd order for the literal subgroup `B`, and
hence for every subgroup of its original image in `G`. The field-factor
calculation is applied to this same image, using its supplied abelianness.
Its two relative normalizer inclusions and surjective torus marking remain
local geometric obligations of the moving-Hall assembly owner.

Source: Aschbacher–Smith, proof of 10.2.3(4), printed pp.745–746. These lemmas do not
assert `NaturalHallPlacementAt`: the original component and normalization
arguments are still needed to obtain that source conclusion.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L H : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {B : Subgroup H}

/-- The odd Hall hypothesis refers to the original `B`, via its actual
subgroup-of inclusion into `H ∩ M`. -/
theorem Context.hall_odd (c : Context D H B) : Odd (Nat.card B) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  apply c.hall.p_in_pi_of_p_dvd_card ⟨2,Nat.prime_two⟩ _ rfl
  rw [Nat.card_congr (subgroupOfEquivOfLe c.hall_le).toEquiv]
  exact even_iff_two_dvd.mp he

/-- Odd order descends to any original ambient subgroup of the Hall image. -/
theorem Context.odd_card_of_le_hall_image (c : Context D H B)
    (P : Subgroup G) (hP : P ≤ B.map H.subtype) : Odd (Nat.card P) := by
  have hodd : Odd (Nat.card (B.map H.subtype)) := by
    rw [card_map_of_injective H.subtype_injective]
    exact c.hall_odd
  exact Odd.of_dvd_nat hodd (card_dvd_of_le hP)

/-- A field factor compatible with conjugation by an element of the original
Hall image is trivial once the original torus normalizer claims are proved. -/
theorem source_original_field_factor_eq_one (c : Context D H B)
    {F : Type*} [Field F] [CharP F 2]
    (C : Subgroup G) (hBC : B.map H.subtype ≤ normalizer (C : Set G))
    (hCB : C ≤ normalizer (B.map H.subtype : Set G))
    (q : C →* Fˣ) (hq : Function.Surjective q)
    (b : B.map H.subtype) (σ : F ≃+* F)
    (he : ∀ d : C, q (C.normalizerMonoidHom (inclusion hBC b) d) =
      Units.map σ.toMonoidHom (q d)) : σ = 1 := by
  let := c.abelian
  exact field_factor_eq_one C (B.map H.subtype) hBC hCB q hq b σ he

end CFSG.Quasithin.Chapter10.MovingHall
