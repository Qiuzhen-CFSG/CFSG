module

public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
public import CFSG.Quasithin.ChapterA.Section02.OddCenterCovers.LocalRanks
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.SimpleException
public import Theory.GroupTheory.GeneralizedFitting.PerfectCentralComponentPair
public import Theory.GroupTheory.GeneralizedFitting.ComponentProductCenters

/-!
# Odd central covers of the exceptional unitary pair

The literal lifted components are perfect central covers of the two SU₃
factors. Their central quotients are the same PSU₃ groups. The genuine
odd-center cover bound forces both lifted centers to be three-groups;
the center of their commuting product is their center product. Thus no
nontrivial central kernel at a prime different from three can occur.

This supplies the central-cover restriction in Aschbacher–Smith A.2.11,
printed p.35; it does not assume that a central extension splits.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterA.Section02
universe u v
variable {G : Type u} {H : Type v} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite H] in
private theorem factor_center_isThreeGroup
    (f : PerfectCentralCovering.Cover G H) (hG : componentLayer G = ⊤)
    (hodd : Odd (Nat.card (center G))) (C : Subgroup G) (A : Subgroup H)
    (hC : IsComponent G C) (hm : C.map f.toMonoidHom = A)
    {n : ℕ} (hn : 2 ≤ n) (hA : IsSpecialUnitaryModel A 3 (2 ^ n)) :
    IsPGroup 3 (center C) := by
  let := hC.2
  let c := f.restrictComponent C A hC hm
  have hmodel : ClassicalGroup.IsPSU (C ⧸ center C) 3 (2 ^ n) :=
    (hA.projectiveModel (by omega)).of_mulEquiv c.quotientCenterEquiv
  have hd : Nat.card (center C) ∣ Nat.card (center G) := by
    have hh := card_dvd_of_le (hC.center_map_le_center_of_semisimple hG)
    rwa [card_map_of_injective C.subtype_injective] at hh
  have ho : Odd (Nat.card (center C)) :=
    Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr hodd).of_dvd_right hd)
  have hc : Nat.card (center C) ∣ 3 :=
    (OddCenterCovers.unitary_center_card_dvd hn hmodel ho).trans (Nat.gcd_dvd_left _ _)
  exact isPGroup_iff_card_dvd_pow.mpr ⟨1, by simpa only [pow_one] using hc⟩

theorem unitary_pair_cover_center_isThreeGroup
    (f : PerfectCentralCovering.Cover G H) (hodd : Odd (Nat.card (center G)))
    (A B : Subgroup H) (hA : IsComponent H A) (hB : IsComponent H B)
    (hne : A ≠ B) (hg : A ⊔ B = ⊤)
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hAm : IsSpecialUnitaryModel A 3 (2 ^ n))
    (hBm : IsSpecialUnitaryModel B 3 (2 ^ m)) :
    IsPGroup 3 (center G) := by
  have hG := f.semisimple (top_unique (hg ▸ sup_le (le_sSup hA) (le_sSup hB)))
  obtain ⟨C, D, hC, hD, hCD, hgen, hmC, hmD⟩ := f.exists_component_pair_lift A B hA hB hne hg
  have hZC := factor_center_isThreeGroup f hG hodd C A hC hmC hn hAm
  have hZD := factor_center_isThreeGroup f hG hodd D B hD hmD hm hBm
  have hzD : ((center D).map D.subtype).Normal := ⟨fun z hz g => by
    rw [mem_center_iff.mp (hD.center_map_le_center_of_semisimple hG hz) g,
      mul_inv_cancel_right]
    exact hz⟩
  let := hzD
  rw [center_eq_sup_center_of_commuting C D
    (commutator_eq_bot_iff_le_centralizer.mp (hC.commutator_eq_bot_of_ne hD hCD)) hgen]
  exact (hZC.map C.subtype).to_sup_of_normal_right (hZD.map D.subtype)

theorem TheoremAUnitaryPair.factors_ne_of_rank_three
    (d : TheoremAUnitaryPair H) (hr : primeRank 3 H = 3) : d.first ≠ d.second := by
  intro he
  have ht : d.first = ⊤ := by
    have hh := d.generates
    rw [← he, sup_idem] at hh
    exact hh
  let e : d.first ≃* H := (MulEquiv.subgroupCongr ht).trans topEquiv
  have hmodel := d.first_model.of_mulEquiv e.symm
  have hh := OddCenterCovers.unitary_special_threeRank_eq_two
    (by have := d.first_large; omega) d.first_odd hmodel
  omega

theorem TheoremAUnitaryPair.cover_center_isThreeGroup
    (d : TheoremAUnitaryPair H) (hr : primeRank 3 H = 3)
    (f : PerfectCentralCovering.Cover G H) (hodd : Odd (Nat.card (center G))) :
    IsPGroup 3 (center G) :=
  unitary_pair_cover_center_isThreeGroup f hodd d.first d.second
    d.first_component d.second_component (d.factors_ne_of_rank_three hr) d.generates
    (by have := d.first_large; omega) (by have := d.second_large; omega)
    d.first_model d.second_model

theorem TheoremAUnitaryPair.cover_kernel_eq_bot_of_ne_three
    (d : TheoremAUnitaryPair H) (hr : primeRank 3 H = 3)
    (f : PerfectCentralCovering.Cover G H) (hodd : Odd (Nat.card (center G)))
    {q : ℕ} [Fact q.Prime] (hne : q ≠ 3) (hq : IsPGroup q f.toMonoidHom.ker) :
    f.toMonoidHom.ker = ⊥ := by
  have ht := (d.cover_center_isThreeGroup hr f hodd).to_le f.ker_le_center
  have hdis : Disjoint f.toMonoidHom.ker f.toMonoidHom.ker :=
    IsPGroup.disjoint_of_ne q 3 hne _ _ hq ht
  simpa only [disjoint_self] using hdis

end CFSG.Quasithin.ChapterA.Section02
