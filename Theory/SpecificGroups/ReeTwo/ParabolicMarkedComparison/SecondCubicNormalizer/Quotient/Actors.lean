module

public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicNormalizer.Quotient.Normal
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Two distinct involutions in the native cubic normalizer quotient

The central twist is outside the order-24 inner core because otherwise the
proved centralizer factorization would put all 48 centralizing automorphisms
inside that core. The reflection inverts the nontrivial cubic and is outside
the centralizer. Their quotient classes are therefore distinct nonidentity
involutions. The quotient of order four is the Klein four-group.

Source: the native binary Ree endpoint in Aschbacher–Smith F.1.12/J.4.5.
-/

@[expose] public section
open Subgroup
namespace ReeTwo.SylowModel.CubicAction
noncomputable section

abbrev cubicCentralizer : Subgroup (MulAut A) := centralizer ({cubic} : Set (MulAut A))

theorem cubicInnerCore_le_centralizer : cubicInnerCore ≤ cubicCentralizer := by
  apply sup_le
  · intro α hα
    exact mem_centralizer_singleton_iff.mpr (fixedInner_commutes_cubic α hα).eq
  · apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr rfl

theorem cubicCentralizer_card : Nat.card cubicCentralizer = 48 := by
  let e : cubicCentralizer ≃ {α : MulAut A // Commute α cubic} :=
    Equiv.subtypeEquivRight (fun α => mem_centralizer_singleton_iff)
  rw [Nat.card_congr e,cubic_centralizer_card]

theorem twist_not_mem_innerCore : twist ∉ cubicInnerCore := by
  intro ht
  have hCK : cubicCentralizer ≤ cubicInnerCore := by
    intro α hα
    obtain ⟨a,ha,j,k,rfl⟩ := centralizer_factorization α (mem_centralizer_singleton_iff.mp hα)
    exact cubicInnerCore.mul_mem (cubicInnerCore.mul_mem
      ((show fixedInner ≤ cubicInnerCore from le_sup_left)
        (mem_map_of_mem MulAut.conj (show a ∈ fixedCore from ha)))
      ((show zpowers cubic ≤ cubicInnerCore from le_sup_right)
        ((zpowers cubic).pow_mem (mem_zpowers cubic) j.val)))
      (cubicInnerCore.pow_mem ht k.val)
  have hcard := card_le_of_le hCK
  rw [cubicCentralizer_card,cubicInnerCore_card] at hcard
  omega

theorem inverter_square_eq_one : inverter ^ 2 = 1 := by
  change action _ ^ 2 = 1
  rw [← map_pow,Tits.AmalgamRigidity.FullRee.SecondExtension.weyl_relations.square,map_one]

theorem inverter_not_mem_centralizer : inverter ∉ cubicCentralizer := by
  intro hi
  have hc := mem_centralizer_singleton_iff.mp hi
  have he : cubic = cubic⁻¹ := by
    rw [← inverter_inverts,hc,mul_inv_cancel_right]
  have h2 : cubic ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [he]
    exact inv_mul_cancel _
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [cubic_order] at hd
  norm_num at hd

-- The twist centralizes the cubic and hence normalizes its cyclic subgroup.
theorem twist_mem_normalizer : twist ∈ cubicNormalizer := by
  apply centralizer_le_normalizer (zpowers cubic : Set (MulAut A))
  rw [zpowers_eq_closure,centralizer_closure]
  exact mem_centralizer_singleton_iff.mpr twist_commutes_cubic.eq

theorem inverter_mem_normalizer : inverter ∈ cubicNormalizer := by
  rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
  change zpowers (inverter*cubic*inverter⁻¹) = zpowers cubic
  rw [inverter_inverts,zpowers_inv]

def twistInNormalizer : cubicNormalizer := ⟨twist,twist_mem_normalizer⟩
def inverterInNormalizer : cubicNormalizer := ⟨inverter,inverter_mem_normalizer⟩
def twistClass : CubicNormalizerQuotient := QuotientGroup.mk' innerCoreInNormalizer twistInNormalizer
def inverterClass : CubicNormalizerQuotient := QuotientGroup.mk' innerCoreInNormalizer inverterInNormalizer

theorem twistClass_square : twistClass ^ 2 = 1 := by
  rw [twistClass,← map_pow]
  have he : twistInNormalizer ^ 2 = 1 := Subtype.ext twist_square_eq_one
  rw [he,map_one]

theorem inverterClass_square : inverterClass ^ 2 = 1 := by
  rw [inverterClass,← map_pow]
  have he : inverterInNormalizer ^ 2 = 1 := Subtype.ext inverter_square_eq_one
  rw [he,map_one]

theorem twistClass_ne_one : twistClass ≠ 1 := by
  intro h
  exact twist_not_mem_innerCore ((QuotientGroup.eq_one_iff twistInNormalizer).mp h)

theorem inverterClass_ne_one : inverterClass ≠ 1 := by
  intro h
  exact inverter_not_mem_centralizer (cubicInnerCore_le_centralizer
    ((QuotientGroup.eq_one_iff inverterInNormalizer).mp h))

theorem twistClass_ne_inverterClass : twistClass ≠ inverterClass := by
  intro h
  have he : QuotientGroup.mk' innerCoreInNormalizer (inverterInNormalizer * twistInNormalizer⁻¹) = 1 := by
    rw [map_mul,map_inv]
    change inverterClass * twistClass⁻¹ = 1
    rw [h,mul_inv_cancel]
  have hk : inverterInNormalizer * twistInNormalizer⁻¹ ∈ innerCoreInNormalizer :=
    (QuotientGroup.eq_one_iff _).mp he
  have hm : inverter * twist⁻¹ ∈ cubicCentralizer := cubicInnerCore_le_centralizer hk
  have ht : twist ∈ cubicCentralizer := mem_centralizer_singleton_iff.mpr twist_commutes_cubic.eq
  exact inverter_not_mem_centralizer (by simpa using cubicCentralizer.mul_mem hm ht)

instance cubicNormalizerQuotient_isKleinFour : IsKleinFour CubicNormalizerQuotient := by
  let : IsMulCommutative CubicNormalizerQuotient :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) cubicNormalizerQuotient_card
  let L := closure ({twistClass,inverterClass} : Set CubicNormalizerQuotient)
  let hL : IsKleinFour L := isKleinFour_closure_pair twistClass inverterClass
    (by simpa only [pow_two] using twistClass_square)
    (by simpa only [pow_two] using inverterClass_square)
    twistClass_ne_one inverterClass_ne_one twistClass_ne_inverterClass (IsMulCommutative.is_comm.comm ..)
  have htop : L = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [card_top,cubicNormalizerQuotient_card,IsKleinFour.card_four])
  let e : L ≃* CubicNormalizerQuotient := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact ⟨cubicNormalizerQuotient_card,
    (Monoid.exponent_eq_of_mulEquiv e).symm.trans IsKleinFour.exponent_two⟩

def cubicNormalizerQuotientEquiv : CubicNormalizerQuotient ≃* Multiplicative (ZMod 2 × ZMod 2) :=
  IsKleinFour.nonempty_mulEquiv.some
end
end ReeTwo.SylowModel.CubicAction
