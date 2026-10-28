module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.FittingProduct
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Theory.SpecificGroups.SymmetricFive.RadicalRange
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

theorem fitting_quotient_isThreeGroup
    {κ : GroupClass} (hG : IsSQTK κ G)
    (R M : Subgroup G) (hr : IsPRadical 2 R)
    (hcontrol : R.characteristicNormalizerClosure ≤ M)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hM : IsPGroup 2 (M ⊓ twoFittingCore G : Subgroup G)) :
    IsPGroup 3 (fittingSubgroup (G ⧸ pCore 2 G)) := by
  let F := twoFittingCore G
  let q := QuotientGroup.mk' (pCore 2 G)
  have hf : (generalizedFitting F).map F.subtype = pCore 2 G := by
    rw [generalizedFitting_eq_pCore_of_selfCentralizing 2
      (subnormal_core_selfCentralizing hc F (inferInstance : F.Normal).isSubnormal)]
    rw [pCore_subnormal_eq_comap 2 (inferInstance : F.Normal).isSubnormal,
      map_comap_eq_self (by rw [range_subtype]; exact twoCore_le_twoFittingCore)]
  obtain ⟨n,hn,B,hB,hprod⟩ := fitting_ordered_product hG R M hr hcontrol hf
  have hI : (M ⊓ F : Subgroup G).map q = ⊥ := by
    have hle : (M ⊓ F : Subgroup G).map q ≤ pPrimeCore 2 (G ⧸ pCore 2 G) := by
      apply (map_mono (f := q) inf_le_right).trans
      change ((fittingSubgroup (G ⧸ pCore 2 G)).comap q).map q ≤ _
      rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _]
      exact fitting_le_pPrimeCore_of_pCore_eq_bot 2 (pCore_quotient_pCore_eq_bot 2)
    have hp := hM.map q
    obtain ⟨a,ha⟩ := hp.exists_card_eq
    have hd := card_dvd_of_le hle
    rw [ha] at hd
    have he : a = 0 := by
      by_contra hne
      have h2 : 2 ∣ 2^a := dvd_pow_self 2 hne
      exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card (h2.trans hd)
    apply Subgroup.card_eq_one.mp
    simpa [he] using ha
  have hB3 (i : Fin n) : B i ≤ upperTwoThreeCore G := by
    apply (hB i).2.2.1.le_upperTwoThreeCore_of_quotient_three
    obtain ⟨e⟩ := (hB i).2.2.2.2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hF3 : F ≤ upperTwoThreeCore G := by
    intro x hx
    obtain ⟨m,hm,l,hl,rfl⟩ := (hprod x).mp hx
    apply mul_mem
    · have hm1 : q m = 1 := mem_bot.mp (hI ▸ mem_map_of_mem q hm)
      change q m ∈ pCore 3 (G ⧸ pCore 2 G)
      rw [hm1]; exact one_mem _
    · apply list_prod_mem
      intro y hy
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hy
      exact hB3 i (hl i)
  have hle := map_mono (f := q) hF3
  change (F.map q) ≤ ((pCore 3 (G ⧸ pCore 2 G)).comap q).map q at hle
  dsimp only [F,twoFittingCore] at hle
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hle
  exact pCore_isPGroup.to_le hle
theorem intersection_twoFittingCore_isTwoGroup (M : Subgroup G)
    (f : M →* Equiv.Perm (Fin 5)) (hA : alternatingGroup (Fin 5) ≤ f.range)
    (hk : IsPGroup 2 f.ker) : IsPGroup 2 (M ⊓ twoFittingCore G : Subgroup G) := by
  let F := twoFittingCore G
  let N := F.comap M.subtype
  let : N.Normal := inferInstance
  let : Group.IsSolvable F := twoFittingCore_solvable
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (M.subtype.comp N.subtype).codRestrict F (fun x => x.property))
    (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : F => (x : G)) h)))
  have hN := Theory.SpecificGroups.FivePointSylowParabolic.solvable_normal_le_ker f hA N
  have hmap := (hk.to_le hN).map M.subtype
  have he : N.map M.subtype = M ⊓ F := by
    rw [map_comap_eq, range_subtype, inf_comm]
  exact he ▸ hmap

end CFSG.Quasithin.ChapterC.Section02Source
