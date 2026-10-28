module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Placement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Overgroups

/-!
# The original central Hall image in the SL₃(2) branch

The faithful odd Hall actor lies in the literal orbit L₀. Source uniqueness
makes H intersect L₀T a proper Sylow overgroup. The exchanged linear-three
pair calculation bounds this intersection by primes two and three; oddness
then makes the image of the original quotient action a three-group.

This proves `LinearThreeImageAt` without extra premises. The argument in
fact does not require the centralization of Ω₁Z(T), as in case(ii) of the
source proof. The supplied subgroup permutation is retained in Context;
proper Sylow-overgroup control applies to the full intersection H∩L₀T.
Source: Aschbacher--Smith,10.1.3 and10.2.3(ii), printed pp.742 and745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.LinearThree
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The SL₃(2) branch of10.2.3 on the original action, without callbacks. -/
theorem source_image_isThreeGroup {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL) :
    IsPGroup 3 (action D B c.hall_le).range := by
  have hBP : B.map H.subtype ≤ H ⊓ localJoin T L :=
    le_inf (map_subtype_le B) ((hall_le_orbit D c e).trans le_sup_left)
  have h6 := (source_proper_overgroup_six D e c.nonnormal (H ⊓ localJoin T L)
    (le_inf c.hstar.1.1.2 le_sup_right) (source_hstar_inf_localJoin_lt D c.hstar)).to_le hBP
  have hB6 : IsPGroup 6 B := h6.of_equiv (B.equivMapOfInjective H.subtype H.subtype_injective).symm
  let f := action D B c.hall_le
  have hf6 : IsPGroup 6 f.range :=
    hB6.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfodd : Odd (Nat.card f.range) := (hall_odd D c).of_dvd_nat
    (Subgroup.card_range_dvd f)
  obtain ⟨n,hn⟩ := hf6.exists_card_dvd_pow
  have hn' : Nat.card f.range ∣ 2 ^ n * 3 ^ n := by
    simpa only [←mul_pow,show 2 * 3 = 6 by decide] using hn
  exact IsPGroup.of_card_dvd_pow
    ((hfodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hn')

end CFSG.Quasithin.Chapter10.CentralHall.LinearThree

namespace CFSG.Quasithin.Chapter10.CentralHall
variable {G : Type*} [Group G] [Finite G]

/-- The complete source contract for the actual binary linear-three quotient. -/
theorem source_linearThreeImageAt (T : Sylow 2 G) : LinearThreeImageAt T := by
  intro L D H B c he
  exact LinearThree.source_image_isThreeGroup D c he.some

end CFSG.Quasithin.Chapter10.CentralHall
