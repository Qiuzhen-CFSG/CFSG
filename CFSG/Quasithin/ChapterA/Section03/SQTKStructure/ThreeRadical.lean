module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeFitting
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# The three-prime radical of a nonquasisimple C-component

In the genuine noncentral A.3.6 alternatives the Fitting subgroup has order
prime to three. Its index in the solvable radical is two. Apply this to the
literal quotient of a C-component by its two-core and lift the order
restriction through that two-group kernel.

This is the structural fact used to select a nonsolvable χ₀ block in the
C.2.5 application of original15.2.4, printed p.1106; A.3.6 is on pp.43--45.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03
open Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
public theorem cComponent_radical_primeTo_three_of_not_quasisimple
    {κ : GroupClass} (hsq : IsSQTK κ G) {K : Subgroup G}
    (hK : K.IsCComponent) (hn : ¬ IsQuasisimple (K ⧸ pCore 2 K)) :
    ¬ 3 ∣ Nat.card (solvableRadical K) := by
  let Q := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (pCore 2 K)
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent (p := 2)
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.subgroupOf le_rfl
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using htop.map_quotient (pCore 2 K)
  have hsqQ : IsSQTK κ Q := by
    refine ⟨?_,(hsq.subgroup K).isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup).trans
      ((hsq.subgroup K).stronglyQuasithin p hp ho)
  have hnc : ¬ fittingSubgroup (⊤ : Subgroup Q) ≤ center (⊤ : Subgroup Q) := by
    intro hc
    have hr : solvableRadical (⊤ : Subgroup Q) = center (⊤ : Subgroup Q) := le_antisymm
      (solvableRadical_le_center_of_fitting_le_center hc)
      (le_solvableRadical _ inferInstance
        (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
    let := hbar.perfect
    let := hbar.isSimpleGroup_quotient_solvableRadical
    let : IsQuasisimple (⊤ : Subgroup Q) := ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  obtain ⟨alt,hcommon⟩ := ChapterA.Section03.CComponentCommutation.noncentralStructureInput
    κ Q hsqQ (pCore_quotient_pCore_eq_bot 2) ⊤ hbar hnc
  have hF3 : ¬ 3 ∣ Nat.card (fittingSubgroup (⊤ : Subgroup Q)) := by
    rcases alt with hnat | hnil
    · obtain ⟨he,p,hp,hgt,F,instF,finF,hF,v,e,hv⟩ := hnat
      let := instF
      let := finF
      have hc : Nat.card (generalizedFitting (⊤ : Subgroup Q)) = p^2 := by
        rw [Nat.card_congr v.toEquiv]
        change Nat.card (Fin 2 → F) = p^2
        rw [Nat.card_fun,Nat.card_fin,hF]
      rw [←he,hc]
      intro hd
      rcases (Nat.dvd_prime hp).mp (Nat.prime_three.dvd_of_dvd_pow hd) with heq | heq <;> omega
    · intro hd
      have hh := hnil.2.2.2 3 Nat.prime_three (hnil.1.symm ▸ hd)
      norm_num at hh
  have hrad3 : ¬ 3 ∣ Nat.card (solvableRadical (⊤ : Subgroup Q)) := by
    rcases hcommon.2.2.1 with ⟨he,hle,hi⟩ | ⟨hc,_,_⟩
    · have hmul := relIndex_mul_relIndex (⊥ : Subgroup (⊤ : Subgroup Q))
        (fittingSubgroup (⊤ : Subgroup Q)) (solvableRadical (⊤ : Subgroup Q)) bot_le hle
      rw [relIndex_bot_left,relIndex_bot_left,hi] at hmul
      rw [←hmul]
      exact fun hh => (Nat.prime_three.dvd_mul.mp hh).elim hF3 (by norm_num)
    · exact (hnc hc.le).elim
  have hradQ : ¬ 3 ∣ Nat.card (solvableRadical Q) := by
    let e : (⊤ : Subgroup Q) ≃* Q := topEquiv
    have he := Nat.card_congr ((solvableRadical (⊤ : Subgroup Q)).equivMapOfInjective
      e.toMonoidHom e.injective).toEquiv
    rw [map_solvableRadical_equiv e] at he
    rwa [←he]
  let A := solvableRadical K
  have hker : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective A.subtype A.subtype_injective
  have hker3 : ¬ 3 ∣ Nat.card (q.subgroupMap A).ker := by
    obtain ⟨n,hn⟩ := hker.exists_card_eq
    rw [hn]
    intro hh
    have hd := Nat.prime_three.dvd_of_dvd_pow hh
    norm_num at hd
  have hmap3 : ¬ 3 ∣ Nat.card (A.map q) := fun hd => hradQ
    (hd.trans (card_dvd_of_le (map_solvableRadical_le_of_surjective q (QuotientGroup.mk'_surjective _))))
  have hcard := (q.subgroupMap A).ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective A),card_top] at hcard
  exact fun hh => (Nat.prime_three.dvd_mul.mp (hcard.symm ▸ hh)).elim hker3 hmap3
end CFSG.Quasithin.ChapterA.Section03
