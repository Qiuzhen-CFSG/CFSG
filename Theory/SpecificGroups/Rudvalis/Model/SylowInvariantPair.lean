module

public import Theory.SpecificGroups.Rudvalis.Model.SylowInvariantPair.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightCharacteristic
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.RankOneEightAction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer
public import Theory.SpecificGroups.Rudvalis.Model.SylowCenter
public import Theory.GroupTheory.CharacteristicCentralizerFusion

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Invariance of the aligned Rudvalis local pair

An automorphism preserving the marked Sylow two-subgroup fixes its unique
normal elementary eight-subgroup and its center. The first local is the full
ambient normalizer of the eight-subgroup. The elementary catalogue identifies
the marked involution subgroup with the ambient image of the Sylow center:
the center has order two, and every row of the catalogue contains that subgroup.
The checked inverse-GAP conjugator and both involution-centralizer inclusions
identify the second local with its full ambient normalizer. Transporting these
normalizers proves invariance of each local under every such automorphism.

All subgroups and conjugations are those of `SylowInvariantPair.Definitions`
on the original degree-4060 carrier. No outer automorphism or local quotient
calculation is used. The original ATLAS attribution remains in the imported
word-certificate modules.

Source: GLS3 Table 5.3r, printed p.279. This is the invariance input for the
Rudvalis extension-cover argument in Aschbacher–Smith E.1.14(5), printed p.214;
generation and the local quotient models are separate inputs to that argument.
-/

public section

open Subgroup
namespace Rudvalis.SylowInvariantPair
open SylowOvergroups RadicalCoverage.LocalCover

private theorem map_characteristic_image {G : Type*} [Group G]
    (P : Subgroup G) (K : Subgroup P) [K.Characteristic]
    (β : MulAut G) (hP : P.map β.toMonoidHom = P) :
    (K.map P.subtype).map β.toMonoidHom = K.map P.subtype := by
  let α : MulAut P := (β.subgroupMap P).trans (MulEquiv.subgroupCongr hP)
  have hK := characteristic_iff_map_eq.mp (inferInstance : K.Characteristic) α
  have he : β.toMonoidHom.comp P.subtype = P.subtype.comp α.toMonoidHom := rfl
  rw [map_map, he, ← map_map, hK]

/-- The characteristic eight-subgroup is invariant under every Sylow-preserving automorphism. -/
theorem elementary_two_invariant (β : MulAut Model)
    (hP : (sylow : Subgroup Model).map β.toMonoidHom = sylow) :
    (elementary 2).map β.toMonoidHom = elementary 2 := by
  let := RankOneEightCharacteristic.elementary_two_characteristic
  have h := map_characteristic_image localP ((elementary 2).subgroupOf localP) β hP
  rwa [map_subgroupOf_eq_of_le (elementary_le_localP 2)] at h

/-- The first aligned local is the full ambient normalizer of the marked eight-subgroup. -/
theorem first_eq_normalizer : locals 0 = normalizer (elementary 2 : Set Model) :=
  le_antisymm RankOneEightAction.max4_le_normalizer_eight
    (max4NormalizerBounds 2 (by decide) (by decide))

/-- The center of the literal four-word Sylow subgroup has order two. -/
theorem localP_center_card : Nat.card (center localP) = 2 := by
  let : Nontrivial localP := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [IntrinsicSylow.localP_card]; decide)
  let : Nontrivial (center localP) := IntrinsicSylow.localP_isPGroup.center_nontrivial
  exact Nat.le_antisymm (SylowCenter.sylow_center_card_le_two sylow)
    (Finite.one_lt_card (α := center localP))

/-- The first catalogue row is exactly the ambient image of the Sylow center. -/
theorem elementary_zero_eq_center :
    elementary 0 = (center localP).map localP.subtype := by
  let Z : Subgroup Model := (center localP).map localP.subtype
  have hc : Nat.card Z = 2 := by
    rw [card_map_of_injective localP.subtype_injective, localP_center_card]
  let : IsElementaryAbelian 2 (center localP) := {
    exponent_dvd_p := localP_center_card ▸ Group.exponent_dvd_nat_card }
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  have hn : localP ≤ normalizer (Z : Set Model) := by
    apply le_normalizer_iff.mpr
    intro p hp x hx
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨(⟨p, hp⟩ : localP) * a * (⟨p, hp⟩ : localP)⁻¹,
      (inferInstance : (center localP).Normal).conj_mem a ha ⟨p, hp⟩, rfl⟩
  have hne : Z ≠ ⊥ := by
    intro h
    rw [h] at hc
    norm_num at hc
  obtain ⟨i, hi⟩ := elementaryCatalogue Z hne (map_subtype_le _) hn inferInstance
  have hle : elementary 0 ≤ Z := by
    rw [hi]
    fin_cases i <;> apply Subgroup.closure_mono <;> simp [Set.subset_def]
  apply eq_of_le_of_card_ge hle
  have hzero : Nat.card (elementary 0) = 2 := by
    change Nat.card (closure {elementaryGenerator 0}) = 2
    rw [← zpowers_eq_closure, Nat.card_zpowers, Max6Certificate.elementary_zero_order]
  exact hc.trans hzero.symm |>.le

/-- The marked involution subgroup is invariant under every Sylow-preserving automorphism. -/
theorem elementary_zero_invariant (β : MulAut Model)
    (hP : (sylow : Subgroup Model).map β.toMonoidHom = sylow) :
    (elementary 0).map β.toMonoidHom = elementary 0 := by
  rw [elementary_zero_eq_center]
  exact map_characteristic_image localP (center localP) β hP

private theorem map_centralizer_singleton {G : Type*} [Group G]
    (e : MulAut G) (z : G) :
    (centralizer ({z} : Set G)).map e.toMonoidHom = centralizer ({e z} : Set G) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e y * e z = e z * e y
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hy)
  · intro x hx
    refine mem_map.mpr ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

/-- The second aligned local is the full normalizer of the marked involution subgroup. -/
theorem second_eq_normalizer : locals 1 = normalizer (elementary 0 : Set Model) := by
  have hC : max6 = centralizer ({Max6Certificate.centralInvolution} : Set Model) :=
    le_antisymm Max6Certificate.CentralizerCertificate.max6_le_centralizer
      Max6Certificate.centralizer_le_max6
  change max6.map (MulAut.conj Max6Certificate.conjugator).toMonoidHom = _
  rw [hC, map_centralizer_singleton, Max6Certificate.conjugator_alignment]
  change _ = normalizer (closure {elementaryGenerator 0} : Set Model)
  rw [← zpowers_eq_closure,
    normalizer_zpowers_eq_centralizer_of_order_two _ Max6Certificate.elementary_zero_order]

/-- Every automorphism preserving the fixed Sylow subgroup preserves each of the two aligned locals. -/
theorem locals_invariant (i : Fin 2) (β : MulAut Model)
    (hP : (sylow : Subgroup Model).map β.toMonoidHom = sylow) :
    (locals i).map β.toMonoidHom = locals i := by
  fin_cases i
  · change (locals 0).map β.toMonoidHom = locals 0
    rw [first_eq_normalizer, map_equiv_normalizer_eq, elementary_two_invariant β hP]
  · change (locals 1).map β.toMonoidHom = locals 1
    rw [second_eq_normalizer, map_equiv_normalizer_eq, elementary_zero_invariant β hP]

end Rudvalis.SylowInvariantPair
