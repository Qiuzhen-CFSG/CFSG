module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.LocalConfiguration
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.SporadicModels.JankoTwoHigmanSims
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Extension
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Enlarging the local subgroup using even characteristic

Let K be the component in the source local configuration and Q a nontrivial
two-subgroup of K whose ambient normalizer contains M. If K has even
characteristic, the inner normalizer of Q has characteristic two, since it
contains a Sylow two-subgroup of K. The ambient normalizer has two-group
quotient over that inner normalizer, so it also has characteristic two.
The actual maximality hypothesis now forces M to equal that normalizer.

This replaces a separate calculation of C_K(Q) by the already established
even-characteristic property of the concrete model. The relative normality,
component--Sylow generation and all ambient actions are retained.
Source: Aschbacher--Smith, 15.3.43(e), printed p.1140. The extension argument
is the same as the plane-normalizer argument in `Held.Reduction`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.RudvalisLocalAction
variable {G : Type*} [Group G] [Finite G] {K S M Y V : Subgroup G}

/-- Maximality applies to every covered nontrivial component two-subgroup. -/
theorem local_eq_normalizer_of_even (c : LocalConfiguration K S M Y V)
    (heven : IsEvenCharacteristic K) (Q : Subgroup G) (hQK : Q ≤ K)
    (hq : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hMN : M ≤ normalizer (Q : Set G)) :
    M = normalizer (Q : Set G) := by
  let : K.Normal := c.normal
  let N := normalizer (Q : Set G)
  have hSN : S ≤ N := c.sylow_le_local.trans hMN
  obtain ⟨P, hP⟩ := c.sylow
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal K
  have hTN : (T : Subgroup K) ≤ N.subgroupOf K := by
    rw [hT, hP]
    exact fun _ hx => hSN hx
  have hlocal : IsTwoLocal (N.subgroupOf K) := by
    rw [show N.subgroupOf K = normalizer (Q.subgroupOf K : Set K) from
      subgroupOf_normalizer_eq hQK]
    refine ⟨Q.subgroupOf K, ?_, hq.comap_subtype, rfl⟩
    intro hb
    apply hne
    rw [← map_subgroupOf_eq_of_le hQK, hb, Subgroup.map_bot]
  obtain ⟨D, hND, hD⟩ := Finite.exists_le_maximal hlocal
  have hNDchar : HasCharacteristicTwo (N.subgroupOf K) := by
    have hh := centralizer_pCore_le_of_sylow_le (T.subtype (hTN.trans hND))
      ((N.subgroupOf K).subgroupOf D) (fun _ hx => hTN hx) (heven T D hD (hTN.trans hND))
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hND)).mp hh
  let e : N.subgroupOf K ≃* K.subgroupOf N := {
    toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hNchar : HasCharacteristicTwo N := by
    have hqN : IsPGroup 2 (N ⧸ K.subgroupOf N) := by
      intro x
      induction x using QuotientGroup.induction_on with | H n =>
        obtain ⟨k, hk⟩ := JankoTwoHigmanSims.quotient_is_two_group c
          (QuotientGroup.mk' K (n : G))
        refine ⟨k, ?_⟩
        change QuotientGroup.mk' (K.subgroupOf N) n ^ 2 ^ k = 1
        rw [← map_pow]
        apply (QuotientGroup.eq_one_iff _).mpr
        change (n : G) ^ 2 ^ k ∈ K
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' K ((n : G) ^ 2 ^ k) = 1
        rw [map_pow]
        exact hk
    exact Theory.GroupTheory.centralizer_pCore_le_of_normal_pGroup_quotient
      (K.subgroupOf N) ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp hNDchar) hqN
  exact le_antisymm hMN (c.maximal.2
    (Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 2 hNchar) hMN)
end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.RudvalisLocalAction
