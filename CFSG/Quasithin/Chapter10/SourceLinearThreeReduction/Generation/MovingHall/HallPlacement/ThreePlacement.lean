module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.InvariantTorus
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.FieldComplement
public import Theory.SpecificGroups.FFLinearPrimeCore

/-!
# A three-group Hall lies in the original Borel

Source 10.1.3 makes the index of the literal component orbit in M prime to
three, since binary SL₂ contains a cubic. The image of a three-group Hall
in that quotient is trivial. The actual H-star overlap then normalizes the
original orbit Sylow, placing the Hall in its two-residual Borel.

This uses the general-field component-index theorem; it does not apply an
A₅-only placement result to the original larger field.
Source: Aschbacher–Smith 10.1.3 and 10.2.3, printed pp.742,745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Source 10.1.3 excludes three above the original component orbit.
Consequently a three-group Hall lies in that orbit and hence its original Borel. -/
theorem hall_le_borel_of_three
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (hB : IsPGroup 3 B) :
    B.map H.subtype ≤ sourceOrbitBorel T L := by
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two F
  have hi := CentralHall.Nonlinear.HallGeometry.hall_component_orbit_index_coprime
    D ctx.nonnormal e 3 (by decide) hd
  let R := (localOrbit T L).subgroupOf D.maximalLocal
  let : R.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let f : B →* D.maximalLocal := (H.subtype.comp B.subtype).codRestrict
    D.maximalLocal (fun b => ctx.hall_le b.property)
  let q := QuotientGroup.mk' R
  let j := q.comp f
  have hj : IsPGroup 3 j.range := hB.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hc : Nat.card j.range = 1 := hj.card_eq_or_dvd.resolve_right (fun hh =>
    (Nat.prime_three.coprime_iff_not_dvd.mp hi) (hh.trans j.range.card_subgroup_dvd_card))
  have hr : j.range = ⊥ := j.range.eq_bot_of_card_eq hc
  apply hall_le_borel_of_le_orbit D ctx e
  rintro x ⟨b,hb,rfl⟩
  have hm : j ⟨b,hb⟩ ∈ j.range := ⟨⟨b,hb⟩,rfl⟩
  have hz : j ⟨b,hb⟩ = 1 := mem_bot.mp (hr ▸ hm)
  have hmem : f ⟨b,hb⟩ ∈ R := (QuotientGroup.eq_one_iff _).mp hz
  exact hmem

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
