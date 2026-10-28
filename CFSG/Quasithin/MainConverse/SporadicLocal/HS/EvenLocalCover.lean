module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralInvolutionCore
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeElementaryCentralizers
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue
public import Theory.GroupTheory.SylowContainingTwoLocal
public import Theory.GroupTheory.AbelianCentralizerNormalizer

/-!
# The exhaustive HS local cover for even characteristic

For the exact degree-100 ATLAS carrier, the three candidate local groups
are normalizers of explicitly defined elementary abelian subgroups. A
kernel-certified normal elementary catalogue inside the explicit order-512
subgroup gives exhaustive coverage of the maximal two-locals containing it,
once the ambient order bound makes that subgroup Sylow.

Only the first local requires its own normal self-centralizing two-subgroup.
For the other two, it suffices that the ambient elementary centralizers
are two-groups: the centralizers themselves supply the intrinsic witnesses.
The imported concrete calculations discharge the catalogue, subgroup order,
and all three local witnesses in `exists_normal_local_cover_of_card_dvd`.

Source: Aschbacher–Smith, condition E and Theorem 0.1.2(5), printed pp.3–4;
GLS volume 3, Table 5.3m, printed p.274. Only the ambient order-divisibility
bound remains an explicit premise of the assembled cover and condition-E
theorem. Its discharge and unconditional QT/E assembly belong to the parent.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.HSEvenLocalCover
open Subgroup
open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.EvenLocalCandidates

/-- The order-512 candidate is Sylow under the allowed ambient divisibility bound. -/
public theorem exists_sylow_of_card_dvd
    (hS : Nat.card subgroup = 2 ^ 9)
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    ∃ T : Sylow 2 Carrier, (T : Subgroup Carrier) = subgroup := by
  have hindex : ¬ 2 ∣ subgroup.index := by
    intro h
    have hd : 2 ^ 10 ∣ Nat.card Carrier := by
      rw [← subgroup.card_mul_index, hS]
      exact Nat.mul_dvd_mul_left (2 ^ 9) h
    have he := hd.trans hcard
    norm_num at he
  exact ⟨(IsPGroup.of_card hS).toSylow hindex, rfl⟩

/-- The catalogue classifies actual intrinsic normal elementary subgroups,
not the local overgroups whose coverage is the desired conclusion. -/
public theorem exists_local_cover_of_normal_elementary_catalogue
    (hS : Nat.card subgroup = 2 ^ 9)
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11)
    (hcatalogue : ∀ R : Subgroup subgroup, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ i : Fin 3, R.map subgroup.subtype = elementary i) :
    ∃ T : Sylow 2 Carrier, ∀ M : Subgroup Carrier, IsMaximalTwoLocal M →
      (T : Subgroup Carrier) ≤ M → ∃ i : Fin 3, Nonempty (M ≃* localGroup i) := by
  obtain ⟨T, hT⟩ := exists_sylow_of_card_dvd hS hcard
  have hcat : ∀ R : Subgroup T, R ≠ ⊥ → R.Normal → IsElementaryAbelian 2 R →
      ∃ i : Fin 3, R.map (T : Subgroup Carrier).subtype = elementary i := by
    rw [← hT] at hcatalogue
    exact hcatalogue
  refine ⟨T, ?_⟩
  intro M hM hTM
  obtain ⟨i, hi⟩ := Theory.GroupTheory.maximalTwoLocal_eq_of_normal_elementary_catalogue
    T elementary hcat hM hTM
  exact ⟨i, ⟨MulEquiv.subgroupCongr hi⟩⟩

/-- Assemble the exact local-cover contract from the three independent model calculations. -/
public theorem exists_normal_local_cover_of_model_facts
    (hS : Nat.card subgroup = 2 ^ 9)
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11)
    (hcatalogue : ∀ R : Subgroup subgroup, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ i : Fin 3, R.map subgroup.subtype = elementary i)
    (hzero : ∃ Q : Subgroup (localGroup 0), Q.Normal ∧ IsPGroup 2 Q ∧
      centralizer (Q : Set (localGroup 0)) ≤ Q)
    (hlarge : ∀ i : Fin 3, i ≠ 0 → IsPGroup 2 (centralizer (elementary i : Set Carrier))) :
    ∃ (T : Sylow 2 Carrier) (Q : ∀ i : Fin 3, Subgroup (localGroup i)),
      (∀ i, (Q i).Normal) ∧ (∀ i, IsPGroup 2 (Q i)) ∧
      (∀ i, centralizer (Q i : Set (localGroup i)) ≤ Q i) ∧
      (∀ M : Subgroup Carrier, IsMaximalTwoLocal M → (T : Subgroup Carrier) ≤ M →
        ∃ i : Fin 3, Nonempty (M ≃* localGroup i)) := by
  classical
  have hex : ∀ i : Fin 3, ∃ Q : Subgroup (localGroup i), Q.Normal ∧ IsPGroup 2 Q ∧
      centralizer (Q : Set (localGroup i)) ≤ Q := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact hzero
    · let := elementary_isElementaryAbelian i
      exact Theory.GroupTheory.exists_normal_selfCentralizing_pSubgroup_of_abelian_centralizer
        (elementary i) (hlarge i hi)
  choose Q hn hp hc using hex
  obtain ⟨T, hcover⟩ := exists_local_cover_of_normal_elementary_catalogue hS hcard hcatalogue
  exact ⟨T, Q, hn, hp, hc, hcover⟩

/-- Conditional condition-E assembly; the explicit model premises must still be discharged. -/
public theorem evenCharacteristic_of_model_facts
    (hS : Nat.card subgroup = 2 ^ 9)
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11)
    (hcatalogue : ∀ R : Subgroup subgroup, R ≠ ⊥ → R.Normal →
      IsElementaryAbelian 2 R → ∃ i : Fin 3, R.map subgroup.subtype = elementary i)
    (hzero : ∃ Q : Subgroup (localGroup 0), Q.Normal ∧ IsPGroup 2 Q ∧
      centralizer (Q : Set (localGroup 0)) ≤ Q)
    (hlarge : ∀ i : Fin 3, i ≠ 0 → IsPGroup 2 (centralizer (elementary i : Set Carrier))) :
    IsEvenCharacteristic Carrier := by
  obtain ⟨T, Q, hn, hp, hc, hcover⟩ :=
    exists_normal_local_cover_of_model_facts hS hcard hcatalogue hzero hlarge
  exact evenCharacteristic_of_local_normal_cover T localGroup Q hn hp hc hcover

/-- The three actual normalizers form an exhaustive cover of the maximal
two-locals containing one Sylow subgroup. Each has an intrinsic normal
self-centralizing two-subgroup. Only the ambient order bound is assumed. -/
public theorem exists_normal_local_cover_of_card_dvd
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    ∃ (T : Sylow 2 Carrier) (Q : ∀ i : Fin 3, Subgroup (localGroup i)),
      (∀ i, (Q i).Normal) ∧ (∀ i, IsPGroup 2 (Q i)) ∧
      (∀ i, centralizer (Q i : Set (localGroup i)) ≤ Q i) ∧
      (∀ M : Subgroup Carrier, IsMaximalTwoLocal M → (T : Subgroup Carrier) ≤ M →
        ∃ i : Fin 3, Nonempty (M ≃* localGroup i)) := by
  exact exists_normal_local_cover_of_model_facts subgroup_card hcard
    normal_elementary_catalogue
    CentralInvolutionCore.exists_normal_selfCentralizing_two_subgroup
    large_elementary_centralizer_isPGroup

/-- The exact ATLAS HS carrier satisfies condition E under the ambient
order-divisibility bound, with every local model calculation discharged. -/
public theorem evenCharacteristic_of_card_dvd
    (hcard : Nat.card Carrier ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11) :
    IsEvenCharacteristic Carrier := by
  obtain ⟨T, Q, hn, hp, hc, hcover⟩ := exists_normal_local_cover_of_card_dvd hcard
  exact evenCharacteristic_of_local_normal_cover T localGroup Q hn hp hc hcover

end CFSG.Quasithin.MainConverse.SporadicLocal.HSEvenLocalCover
