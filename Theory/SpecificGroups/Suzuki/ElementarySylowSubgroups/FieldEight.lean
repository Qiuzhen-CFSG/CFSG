module

public import Theory.SpecificGroups.Suzuki.SubgroupContainment
public import Theory.SpecificGroups.Suzuki.BorelInvolutionCore
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Subgroups with a Sylow subgroup of order two in Sz(8)

A subgroup of a Suzuki Borel with Sylow two-subgroup of order two lies
in the root group. Indeed, its Sylow subgroup is the inverse image of the
Borel's unique Sylow subgroup, hence normal and central. The centralizer
of its nonidentity element lies in the root group.

Consequently a subgroup of Sz(8) satisfying standard containment, with
Sylow two-subgroup of order two and order divisible by seven, has order
fourteen. The nonsplit normalizers have orders 52 and 20, the root group
has order 64, and the split normalizer has order 14.

Source: GLS4, Chapter 4, Lemma 3.8, and its application in Chapter 2,
the last paragraph of Lemma 14.9; the root centralizer calculation is
Huppert--Blackburn, Finite Groups III, XI.3.10.
-/

namespace BenderSuzuki.MatrixGroups
open Subgroup

/-- In a Borel, a Sylow subgroup of order two forces containment in the root
group, by normality and the centralizer of its nonidentity element. -/
public theorem suzukiBorel_subgroup_le_root_of_sylow_card_two {m : ℕ}
    (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : H ≤ SuzukiBorelSubgroup m) (V : Sylow 2 H) (hV : Nat.card V = 2) :
    H ≤ SuzukiRootSubgroup m := by
  obtain ⟨S, hS⟩ := suzukiBorel_root_isSylow m hm
  have hSn : (S : Subgroup (SuzukiBorelSubgroup m)).Normal :=
    hS ▸ suzukiRootSubgroup_normal_in_borel m
  let := S.unique_of_normal hSn
  obtain ⟨Q, hQ⟩ := V.exists_comap_eq_of_injective (inclusion_injective hH)
  have hVS : (V : Subgroup H) = (S : Subgroup (SuzukiBorelSubgroup m)).comap
      (inclusion hH) := by
    rw [← hQ, Subsingleton.elim Q S]
  have hVn : (V : Subgroup H).Normal := by
    rw [hVS]
    exact hSn.comap _
  let := hVn
  have hVc := central_of_normal_card_two (V : Subgroup H) hV
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : V)).mp hV
  have ha1 : ((a : H) : SuzukiMatrixGroup m) ≠ 1 := by
    intro he
    exact ha (Subtype.ext (Subtype.ext he))
  have haR : ((a : H) : SuzukiMatrixGroup m) ∈ SuzukiRootSubgroup m := by
    have h : (a : H) ∈ (V : Subgroup H) := a.property
    rw [hVS, hS] at h
    exact h
  apply le_trans ?_ (suzukiRootSubgroup_centralizer_le m hm haR ha1)
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  have h := (mem_center_iff.mp (hVc a.property)) (⟨x, hx⟩ : H)
  exact congrArg Subtype.val h

/-- The literal nonsplit normalizers in Sz(8) have orders 52 and 20. -/
public theorem SuzukiNonsplitTorusPair.normalizer_cards_at_eight
    (T : SuzukiNonsplitTorusPair 1) :
    Nat.card (normalizer (T.plus : Set (SuzukiMatrixGroup 1))) = 52 ∧
    Nat.card (normalizer (T.minus : Set (SuzukiMatrixGroup 1))) = 20 := by
  constructor
  · have h := relIndex_mul_card_of_le (le_normalizer (H := T.plus))
    rw [T.plus_maximal.normalizer_index_eq_four (by decide), T.plus_card] at h
    exact h.symm
  · have h := relIndex_mul_card_of_le (le_normalizer (H := T.minus))
    rw [T.minus_maximal.normalizer_index_eq_four (by decide), T.minus_card] at h
    exact h.symm

/-- Standard containment forces order fourteen when the Sylow two-subgroup
has order two and seven divides the subgroup order. -/
public theorem suzuki_card_fourteen_of_standard_containment
    (T : SuzukiNonsplitTorusPair 1) (H : Subgroup (SuzukiMatrixGroup 1))
    (hH : SuzukiStandardContainment T H) (V : Sylow 2 H)
    (hV : Nat.card V = 2) (hseven : 7 ∣ Nat.card H) : Nat.card H = 14 := by
  obtain ⟨g, hg⟩ := hH
  let K := H.map (MulAut.conj g).toMonoidHom
  let e : H ≃* K := H.equivMapOfInjective _ (MulAut.conj g).injective
  have hcard : Nat.card H = Nat.card K := Nat.card_congr e.toEquiv
  let W : Sylow 2 K := V.mapSurjective (f := e.toMonoidHom) e.surjective
  have hW : Nat.card W = 2 :=
    (Nat.card_congr ((V : Subgroup H).equivMapOfInjective e.toMonoidHom
      e.injective).toEquiv).symm.trans hV
  have hsevenK : 7 ∣ Nat.card K := hcard ▸ hseven
  rcases hg with hB | hS | hP | hM
  · have hKR := suzukiBorel_subgroup_le_root_of_sylow_card_two (by decide) K hB W hW
    have hdiv := hsevenK.trans (card_dvd_of_le hKR)
    rw [suzukiRootSubgroup_card 1 (by decide)] at hdiv
    norm_num at hdiv
  · have hdiv := card_dvd_of_le hS
    rw [suzukiSplitTorus_normalizer_card 1 (by decide)] at hdiv
    have htwo : 2 ∣ Nat.card K := by
      simpa only [hW] using (W : Subgroup K).card_subgroup_dvd_card
    have hlower : 14 ∣ Nat.card K :=
      (show Nat.Coprime 2 7 by decide).mul_dvd_of_dvd_of_dvd htwo hsevenK
    exact hcard.trans (Nat.dvd_antisymm hdiv hlower)
  · have hdiv := hsevenK.trans (card_dvd_of_le hP)
    rw [T.normalizer_cards_at_eight.1] at hdiv
    norm_num at hdiv
  · have hdiv := hsevenK.trans (card_dvd_of_le hM)
    rw [T.normalizer_cards_at_eight.2] at hdiv
    norm_num at hdiv

end BenderSuzuki.MatrixGroups
