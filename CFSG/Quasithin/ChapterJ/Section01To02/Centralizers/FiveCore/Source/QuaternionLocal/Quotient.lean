module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.OddComplement
public import Theory.SpecificGroups.SymmetricFive.OddLocal

/-!
# The odd quotient calculations for the five-centralizer

The literal Ru₂ quotient has two-group kernel, so it embeds odd subgroups.
The S₅ calculation gives their orders as one, three or five. Its five-cycle
centralizer also gives C_H(B₅) = B₅ C_Q(B₅), before any quaternion recognition.
These are the quotient steps of Aschbacher–Smith J.2.7(5), printed pp.435–436
(PDF pp.446–447 of `refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup

namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]
/-- The actual quotient marking embeds every odd subgroup of H. -/
theorem TypeRuSetup.quotientMap_injective_on_odd (d : TypeRuSetup G)
    (A : Subgroup d.H) (hodd : Odd (Nat.card A)) :
    Function.Injective (d.ru2.quotientMap.comp A.subtype) := by
  have hk : IsPGroup 2 d.ru2.quotientMap.ker := by
    rw [d.ru2.quotient_kernel]
    exact (isPGroup_pCoreIn 2 d.H).comap_subtype
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hd : Disjoint A d.ru2.quotientMap.ker := disjoint_of_coprime_natCard (by
    rw [hn]
    exact (Nat.coprime_two_left.mpr hodd).symm.pow_right n)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  exact Subtype.ext (hd.le_bot ⟨x.property, hx⟩)

/-- The odd-subgroup bound used on printed p.436, from the genuine Ru₂ quotient. -/
theorem TypeRuSetup.odd_subgroup_card (d : TypeRuSetup G) (A : Subgroup G)
    (hA : A ≤ d.H) (hodd : Odd (Nat.card A)) :
    Nat.card A = 1 ∨ Nat.card A = 3 ∨ Nat.card A = 5 := by
  let AH := A.subgroupOf d.H
  have hc : Nat.card AH = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv
  have hi := d.quotientMap_injective_on_odd AH (hc.symm ▸ hodd)
  have hm : Nat.card (AH.map d.ru2.quotientMap) = Nat.card A := by
    simpa only [MonoidHom.range_comp, range_subtype] using
      (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hc
  simpa only [hm] using SymmetricFive.odd_subgroup_card (AH.map d.ru2.quotientMap) (hm.symm ▸ hodd)
end CFSG.Quasithin.ChapterJ

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The local centralizer product, with the original five-subgroup and core. -/
theorem H_inf_G5_eq_B5Image_sup_CQ (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (B5 : Sylow 5 d.toTypeRuSetup.H) :
    d.toTypeRuSetup.H ⊓ G5 B5 = B5Image B5 ⊔ CQ B5 := by
  let D := d.toTypeRuSetup
  have hcard : Nat.card B5 = 5 := by
    rw [B5.card_eq_multiplicity, d.ru2.card_H hZ]
    decide +kernel
  let : IsCyclic B5 := isCyclic_of_prime_card hcard
  obtain ⟨b, hb⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic B5)
  have hb5 : orderOf b = 5 := hb.trans hcard
  have hi := D.quotientMap_injective_on_odd (B5 : Subgroup D.H) (by
    rw [hcard]
    decide)
  have hbq : orderOf (d.ru2.quotientMap b) = 5 :=
    (Subgroup.orderOf_coe ((MonoidHom.ofInjective hi) b)).trans
      (((MonoidHom.ofInjective hi).orderOf_eq b).trans hb5)
  apply le_antisymm
  · intro x hx
    have hcomm : d.ru2.quotientMap ⟨x,hx.1⟩ ∈ zpowers (d.ru2.quotientMap b) := by
      rw [← SymmetricFive.centralizer_of_order_five hbq]
      apply mem_centralizer_singleton_iff.mpr
      have he : (⟨x,hx.1⟩ : D.H) * b = b * ⟨x,hx.1⟩ := by
        apply Subtype.ext
        exact (hx.2 b (mem_map_of_mem D.H.subtype b.property)).symm
      simpa only [map_mul] using congrArg d.ru2.quotientMap he
    obtain ⟨k,hk⟩ := mem_zpowers_iff.mp hcomm
    let a : D.H := (b : D.H) ^ k
    have ha : (a : G) ∈ B5Image B5 := mem_map_of_mem D.H.subtype
      ((B5 : Subgroup D.H).zpow_mem b.property k)
    have hax : (a⁻¹ * ⟨x,hx.1⟩ : D.H) ∈ d.ru2.quotientMap.ker := by
      change d.ru2.quotientMap (a⁻¹ * ⟨x,hx.1⟩) = 1
      simp only [map_mul, map_inv, a, map_zpow, hk, inv_mul_cancel]
    rw [d.ru2.quotient_kernel] at hax
    have hCQ : (a : G)⁻¹ * x ∈ CQ B5 :=
      ⟨hax, (G5 B5).mul_mem ((G5 B5).inv_mem (B5Image_le_G5 hZ B5 ha)) hx.2⟩
    have hh := (B5Image B5 ⊔ CQ B5).mul_mem (mem_sup_left ha) (mem_sup_right hCQ)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le (le_inf (map_subtype_le _) (B5Image_le_G5 hZ B5))
      (le_inf (inf_le_left.trans (pCoreIn_le _ _)) inf_le_right)
end CFSG.Quasithin.ChapterJ.Centralizers.Choices

