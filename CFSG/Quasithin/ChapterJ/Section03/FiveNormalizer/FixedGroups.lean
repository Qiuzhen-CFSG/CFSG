module

public import Theory.GroupTheory.AbelianSylowNormalSubgroupFusion
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.FiveGroup
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Center
public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube

/-!
# The fixed subgroups and Burnside fusion in J.3.6

The actual odd core of C_G(B₅), of order125, is Sylow by J.3.1. Its three
fixed factors show that an abelian core is elementary. The quaternion
supplement then makes that core self-centralizing. The source inverter
has a fixed subgroup of order5, conjugate to B₅ but distinct from it.
Burnside fusion therefore excludes the abelian branch once N_G(P) fixes B₅;
the prime-cube theorem gives the required extraspecial group.

The exact earlier quaternion/inverter witnesses and core order remain inputs.
The subsequent normalizer action calculation owns the displayed normalizer
comparison. No arbitrary-source recognition conclusion is assumed.
Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

omit [Finite G] in
theorem exists_sylow_five_of_order
    (hG : Nat.card G = 2^14 * 3^3 * 5^3 * 7 * 13 * 29)
    (P : Subgroup G) (hP : Nat.card P = 125) :
    ∃ S : Sylow 5 G, (S : Subgroup G) = P := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have he := P.card_mul_index
  rw [hP,hG] at he
  have hi : P.index = 1167409152 := by omega
  exact ⟨(IsPGroup.of_card (p:=5) (n:=3) hP).toSylow (by rw [hi]; decide),rfl⟩

theorem five_subgroup_conjugate_into_base (B5 : Sylow 5 d.toTypeRuSetup.H)
    (A : Subgroup G) (hAH : A ≤ d.toTypeRuSetup.H) (hA : Nat.card A = 5) :
    ∃ g : d.toTypeRuSetup.H, A.conjBy (g : G) = B5Image B5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp : IsPGroup 5 A := IsPGroup.of_card (n:=1) hA
  obtain ⟨R,hR⟩ := (hp.comap_subtype (K:=d.toTypeRuSetup.H)).exists_le_sylow
  have hRc : Nat.card R = 5 := by
    rw [R.card_eq_multiplicity,d.ru2.card_H d.card_Z]
    decide +kernel
  have hAR : A.subgroupOf d.toTypeRuSetup.H = (R : Subgroup d.toTypeRuSetup.H) :=
    eq_of_le_of_card_ge hR (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv,hA,hRc])
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq d.toTypeRuSetup.H R B5
  have he := congrArg (fun S : Sylow 5 d.toTypeRuSetup.H => (S : Subgroup d.toTypeRuSetup.H)) hg
  change (R : Subgroup d.toTypeRuSetup.H).map (MulAut.conj g).toMonoidHom = _ at he
  rw [← hAR] at he
  have hm := congrArg (Subgroup.map d.toTypeRuSetup.H.subtype) he
  have hc : d.toTypeRuSetup.H.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp d.toTypeRuSetup.H.subtype := by ext; rfl
  rw [map_map,hc,← map_map,map_subgroupOf_eq_of_le hAH] at hm
  exact ⟨g,hm⟩

private theorem quaternion_square_or_self (x z : QuaternionGroup 2)
    (hz : z^2=1 ∧ z≠1) (hx : x≠1) : x=z ∨ x^2=z := by
  have hm : ∀ a b : QuaternionGroup 2, b^2=1 ∧ b≠1 → a≠1 → a=b ∨ a^2=b := by
    decide +kernel
  exact hm x z hz hx

theorem fiveOddPart_self_centralizing_of_commutative (c : Choices d)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (q : FiveQuaternionData B5)
    (hP : Nat.card (fiveOddPart B5) = 125)
    [IsMulCommutative (fiveOddPart B5)] :
    centralizer (fiveOddPart B5 : Set G) = fiveOddPart B5 := by
  have hPC : fiveOddPart B5 ≤ centralizer (fiveOddPart B5 : Set G) := by
    intro x hx a ha
    exact (fiveOddPart B5).le_centralizer hx a ha
  have hzQ : c.z ∈ CQ B5 := by
    have he : c.z ∈ CQ B5 ⊓ d.toTypeRuSetup.U := q.inf_U.symm ▸ c.z_mem_Z
    exact he.1
  have hznon : c.z ∉ centralizer (fiveOddPart B5 : Set G) := by
    intro hz
    have hh : fiveOddPart B5 ≤ centralizer ({c.z} : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (hz x hx)
    have he := c.fiveOddPart_inf_centralizer_z d.card_Z B5 q
    rw [inf_eq_left.mpr hh] at he
    have hc := congrArg (fun A : Subgroup G => Nat.card A) he
    rw [hP,B5Image_card d.card_Z B5] at hc
    contradiction
  have hCQ {t : G} (ht : t∈CQ B5) (htC : t∈centralizer (fiveOddPart B5 : Set G)) : t=1 := by
    by_contra hn
    obtain ⟨e⟩ := q.quaternion
    have hz2 := c.z_involution_of_card d.card_Z
    have hzq : (⟨c.z,hzQ⟩ : CQ B5)^2=1 := Subtype.ext hz2.2
    have he := quaternion_square_or_self (e ⟨t,ht⟩) (e ⟨c.z,hzQ⟩)
      ⟨by rw [← map_pow,hzq,map_one],
       by intro hh; exact hz2.1 (congrArg Subtype.val (e.injective (hh.trans (map_one e).symm)))⟩
      (by intro hh; exact hn (congrArg Subtype.val (e.injective (hh.trans (map_one e).symm))))
    rcases he with he | he
    · have hh : t=c.z := congrArg Subtype.val (e.injective he)
      exact hznon (hh ▸ htC)
    · have htq : (⟨t,ht⟩ : CQ B5)^2=⟨c.z,hzQ⟩ :=
        e.injective ((map_pow e _ 2).trans he)
      have hh : t^2=c.z := congrArg Subtype.val htq
      exact hznon (hh ▸ (centralizer (fiveOddPart B5 : Set G)).pow_mem htC 2)
  apply le_antisymm ?_ hPC
  intro x hx
  have hB : x∈G5 B5 := centralizer_le (B5Image_le_fiveOddPart d.card_Z B5) hx
  have hn : CQ B5 ≤ normalizer (fiveOddPart B5 : Set G) :=
    inf_le_right.trans (G5_normalizes_fiveOddPart B5)
  have hprod : (G5 B5 : Set G) = (fiveOddPart B5 : Set G) * (CQ B5 : Set G) := by
    rw [c.G5_eq_fiveOddPart_sup_CQ d.card_Z B5 q,coe_mul_of_right_le_normalizer_left _ _ hn]
  change x ∈ (G5 B5 : Set G) at hB
  rw [hprod] at hB
  obtain ⟨p,hp,t,ht,rfl⟩ := hB
  have htC : t∈centralizer (fiveOddPart B5 : Set G) := by
    have hh := (centralizer (fiveOddPart B5 : Set G)).mul_mem
      ((centralizer (fiveOddPart B5 : Set G)).inv_mem (hPC hp)) hx
    simpa only [inv_mul_cancel_left] using hh
  change p*t ∈ fiveOddPart B5
  rw [hCQ ht htC,mul_one]
  exact hp

namespace FiveInverterData
variable (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (q : FiveQuaternionData B5) (v : Choices.FiveInverterData c B5)

include c q v in
theorem fixed_five_card (hP : Nat.card (fiveOddPart B5) = 125) :
    Nat.card (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G) = 5 := by
  have he := v.oddPart_card_formula c B5 d.card_Z q
  rw [hP] at he
  apply Nat.pow_left_injective (by decide : 2 ≠ 0)
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5) he.symm

include c q v in
theorem elementary_of_commutative (hP : Nat.card (fiveOddPart B5) = 125)
    [IsMulCommutative (fiveOddPart B5)] : IsElementaryAbelian 5 (fiveOddPart B5) := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨b,hb,u,hu,w,hw,he⟩ := v.factorization c B5 d.card_Z q x x.property
  have hf := fixed_five_card c B5 q v hP
  have hfw : Nat.card (fiveOddPart B5 ⊓ centralizer ({c.z*v.i} : Set G) : Subgroup G) = 5 :=
    (v.fixed_card_eq c B5).symm.trans hf
  have hb5 : b^5=1 := by
    have hh := pow_card_eq_one' (x := (⟨b,hb⟩ : B5Image B5))
    rw [B5Image_card d.card_Z B5] at hh
    exact congrArg Subtype.val hh
  have hu5 : u^5=1 := by
    have hh := pow_card_eq_one' (x := (⟨u,hu⟩ : (fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) : Subgroup G)))
    rw [hf] at hh
    exact congrArg Subtype.val hh
  have hw5 : w^5=1 := by
    have hh := pow_card_eq_one' (x := (⟨w,hw⟩ : (fiveOddPart B5 ⊓ centralizer ({c.z*v.i} : Set G) : Subgroup G)))
    rw [hfw] at hh
    exact congrArg Subtype.val hh
  have hbP := B5Image_le_fiveOddPart d.card_Z B5 hb
  have hcbu : Commute b u := (fiveOddPart B5).le_centralizer hu.1 b hbP
  have hcbw : Commute b w := (fiveOddPart B5).le_centralizer hw.1 b hbP
  have hcuw : Commute u w := (fiveOddPart B5).le_centralizer hw.1 u hu.1
  apply Subtype.ext
  change (x : G)^5=1
  rw [he,(hcbw.mul_left hcuw).mul_pow,hcbu.mul_pow,hb5,hu5,hw5]
  simp

include c q v in
theorem fixed_five_conjugate (hP : Nat.card (fiveOddPart B5) = 125) :
    ∃ g : G, (B5Image B5).conjBy g =
      fiveOddPart B5 ⊓ centralizer ({v.i} : Set G) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp v.z_class
  let A := fiveOddPart B5 ⊓ centralizer ({v.i} : Set G)
  have hAH : A.conjBy g ≤ d.toTypeRuSetup.H := by
    rintro x ⟨a,ha,rfl⟩
    rw [c.H_eq_centralizer_z,mem_centralizer_singleton_iff]
    change g*v.i*g⁻¹=c.z at hg
    rw [← hg]
    simpa only [map_mul,MulAut.conj_apply,MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp ha.2)
  have hAc : Nat.card (A.conjBy g) = 5 := by
    change Nat.card (A.map (MulAut.conj g).toMonoidHom) = 5
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact fixed_five_card c B5 q v hP
  obtain ⟨j,hj⟩ := five_subgroup_conjugate_into_base B5 (A.conjBy g) hAH hAc
  have he : A.conjBy ((j : G)*g) = B5Image B5 := by rwa [← conjBy_mul] at hj
  refine ⟨((j : G)*g)⁻¹,?_⟩
  rw [← he,conjBy_inv]

include c q v in
theorem noncommutative_of_normalizer_control
    (hG : Nat.card G = 2^14 * 3^3 * 5^3 * 7 * 13 * 29)
    (hP : Nat.card (fiveOddPart B5) = 125)
    (hn : normalizer (fiveOddPart B5 : Set G) ≤ normalizer (B5Image B5 : Set G)) :
    ¬ IsMulCommutative (fiveOddPart B5) := by
  intro hc
  let := hc
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨S,hS⟩ := exists_sylow_five_of_order hG (fiveOddPart B5) hP
  have hSc : IsMulCommutative S := by rw [hS]; exact hc
  let := hSc
  obtain ⟨g,hg⟩ := fixed_five_conjugate c B5 q v hP
  have he := S.conjugate_subgroup_eq_of_abelian_normalizer (B5Image B5)
    (by rw [hS]; exact B5Image_le_fiveOddPart d.card_Z B5)
    (by simpa only [← Sylow.coe_coe,hS] using hn) g (by rw [hg,hS]; exact inf_le_left)
  have hbi : B5Image B5 ≤ centralizer ({v.i} : Set G) := by rw [← he,hg]; exact inf_le_right
  have hbot := v.common_fixed_eq_bot c B5 d.card_Z q
  rw [c.fiveOddPart_inf_centralizer_z d.card_Z B5 q,inf_eq_left.mpr hbi] at hbot
  have hcard := B5Image_card d.card_Z B5
  rw [hbot,card_bot] at hcard
  contradiction

include c q v in
/-- The source prime-cube group is extraspecial once the actual normalizer
comparison has been proved by the linear-action calculation. -/
theorem extraspecial_of_normalizer_control
    (hG : Nat.card G = 2^14 * 3^3 * 5^3 * 7 * 13 * 29)
    (hP : Nat.card (fiveOddPart B5) = 125)
    (hn : normalizer (fiveOddPart B5 : Set G) ≤ normalizer (B5Image B5 : Set G)) :
    IsExtraspecial 5 (fiveOddPart B5) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact IsExtraspecial.of_noncommutative_card_prime_cube hP
    (noncommutative_of_normalizer_control c B5 q v hG hP hn)

end FiveInverterData
end CFSG.Quasithin.ChapterJ.Section03
