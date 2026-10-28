module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.ElementaryCatalogue
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.POrder
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.TwoPartBound
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers
public import Theory.GroupTheory.SylowLocalCentralizerCriterion

/-!
# The Rudvalis central involution and condition E

The certified subgroup `localP` has order 2^14 and odd ambient index, hence
is Sylow. Each nontrivial normal elementary subgroup of it belongs to the
proved six-member catalogue, and every member contains the marked involution.
Applying the catalogue to a central involution's cyclic subgroup therefore
identifies every central involution with that marked element.

The existing ambient centralizer and conjugator certificates identify its
centralizer with a conjugate of the actual ATLAS max6 subgroup. Consequently,
characteristic two of max6 implies condition E by the Sylow-local centralizer
criterion. This covers all required maximal two-locals without treating
maximality among all subgroups as maximality among two-locals.

The self-centralizing two-core of max6 remains an explicit premise. Neither
its ATLAS structure label nor the centralizer identification proves that fact.
No ambient order formula, simplicity, or cyclic Sylow-center hypothesis is used.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5), p.482; GLS3 Table 5.3r, p.279. Concrete word sources and
conjugation conventions are documented in the imported Rudvalis modules.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate

private theorem localP_odd_index : ¬ 2 ∣ localP.index := by
  intro h
  apply RadicalCoverage.SylowCertificate.not_two_pow_fifteen_dvd_card_model
  rw [← localP.card_mul_index, IntrinsicSylow.localP_card]
  exact Nat.mul_dvd_mul_left 16384 h

/-- The existing fixed word subgroup, promoted to an ambient Sylow subgroup. -/
public noncomputable def sylowTwo : Sylow 2 Model :=
  IntrinsicSylow.localP_isPGroup.toSylow localP_odd_index

/-- The chosen Sylow has exactly the preserved fixed-word carrier. -/
public theorem sylowTwo_coe : (sylowTwo : Subgroup Model) = localP := by rfl

private theorem marked_mem_elementary (i : Fin 6) : elementaryGenerator 0 ∈ elementary i := by
  fin_cases i <;> apply Subgroup.subset_closure <;> simp

/-- Every central involution of the fixed ambient Sylow is the marked word. -/
public theorem sylow_central_involution_eq (z : sylowTwo)
    (hz : z ∈ center sylowTwo) (ho : orderOf z = 2) :
    (z : Model) = elementaryGenerator 0 := by
  classical
  have hoG : orderOf (z : Model) = 2 := (orderOf_coe z).trans ho
  have hne : zpowers (z : Model) ≠ ⊥ := by
    intro h
    have hz1 : (z : Model) = 1 := by
      have hm := mem_zpowers (z : Model)
      rw [h, mem_bot] at hm
      exact hm
    simp [hz1] at hoG
  have hle : zpowers (z : Model) ≤ localP := zpowers_le.mpr z.property
  have hn : localP ≤ normalizer (zpowers (z : Model) : Set Model) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two _ hoG]
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hz (⟨x, hx⟩ : sylowTwo)))
  have he : IsElementaryAbelian 2 (zpowers (z : Model)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa only [hoG] using pow_orderOf_eq_one (z : Model))
  obtain ⟨i, hi⟩ := elementaryCatalogue _ hne hle hn he
  have hm : elementaryGenerator 0 ∈ zpowers (z : Model) := hi ▸ marked_mem_elementary i
  rw [mem_zpowers_iff_mem_range_orderOf, hoG] at hm
  obtain ⟨n, hn, heq⟩ := Finset.mem_image.mp hm
  have hlt : n < 2 := Finset.mem_range.mp hn
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · have hm1 : elementaryGenerator 0 = 1 := by simpa using heq.symm
    have := elementary_zero_order
    simp [hm1] at this
  · simpa using heq

/-- The exact centralizer, with the certified orientation of conjugation. -/
public theorem marked_centralizer_eq :
    centralizer ({elementaryGenerator 0} : Set Model) =
      max6.map (MulAut.conj conjugator).toMonoidHom := by
  apply le_antisymm (centralizer_le_conjugate centralizer_le_max6)
  rintro x ⟨y, hy, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [← conjugator_alignment]
  exact (MulAut.conj conjugator).map_mul y centralInvolution |>.symm.trans
    ((congrArg (MulAut.conj conjugator)
      (mem_centralizer_singleton_iff.mp (CentralizerCertificate.max6_le_centralizer hy))).trans
        ((MulAut.conj conjugator).map_mul centralInvolution y))

/-- The remaining local core calculation suffices for the full condition E. -/
public theorem evenCharacteristic_of_max6 (h6 : HasCharacteristicTwo max6) :
    IsEvenCharacteristic Model := by
  apply IsEvenCharacteristicAt.all (T := sylowTwo)
  intro M hM hTM
  obtain ⟨Q, hQ, hp, rfl⟩ := hM.1
  apply normalizer_core_selfCentralizing_of_sylow_centralizers sylowTwo Q hp hQ hTM
  intro z hz ho
  change HasCharacteristicTwo (centralizer ({(z : Model)} : Set Model))
  rw [sylow_central_involution_eq z hz ho, marked_centralizer_eq]
  exact h6.of_equiv ((MulAut.conj conjugator).subgroupMap max6)

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
