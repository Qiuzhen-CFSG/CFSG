module

public import Theory.Representation.BinaryOffender.TwoCoreFixedSpace
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.NormalPSubgroupCoprimeSupplement
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Fixed spaces with an odd normal supplement

Suppose G = NKA, where N is normal of odd order, A is a two-group,
K = [K,A], and K is quasisimple or has odd order. Then O₂(G) lies in KA
and centralizes NK. For a faithful finite-dimensional binary action this
identifies C_G(C_V(O₂(G))) with O₂(G).

The Sylow supplement theorem puts the two-core inside KA. Component
calculus there proves centralization of quasisimple K using perfectness;
for odd K, disjoint normal subgroups commute. The P × Q fixed-space lemma
then applies to the normal subgroup NK with two-group quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.10,
printed p.72 (PDF p.83). The normal odd subgroup may be either the Fitting
subgroup or its centralizer of the minimal-offender-generated subgroup.
-/

public section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender

variable {G V : Type*} [Group G] [Finite G]

private theorem twoGroup_coprime {P : Subgroup G} (hP : IsPGroup 2 P)
    {n : ℕ} (hn : Nat.Coprime 2 n) : Nat.Coprime (Nat.card P) n := by
  obtain ⟨e, he⟩ := hP.exists_card_eq
  rw [he]
  exact hn.pow_left e

theorem twoCore_le_and_centralizes_of_odd_normal_supplement (N K A : Subgroup G) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N))
    (hK : IsQuasisimple K ∨ Nat.Coprime 2 (Nat.card K))
    (hKA : ⁅K, A⁆ = K) (hgen : N ⊔ (K ⊔ A) = ⊤) :
    pCore 2 G ≤ K ⊔ A ∧ pCore 2 G ≤ centralizer ((N ⊔ K : Subgroup G) : Set G) := by
  let Q := pCore 2 G
  have hQS : Q ≤ K ⊔ A :=
    normal_pSubgroup_le_of_coprime_normal_supplement N (K ⊔ A) Q hN hgen pCore_isPGroup
  have hQN : ⁅Q, N⁆ = ⊥ :=
    commutator_eq_bot_of_disjoint
      (disjoint_of_coprime_natCard (twoGroup_coprime pCore_isPGroup hN))
  let S := K ⊔ A
  let K₀ := K.subgroupOf S
  let Q₀ := Q.subgroupOf S
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer (hKA ▸ normalizer_commutator_ge_right K A))
  have hQ₀ : IsPGroup 2 Q₀ := pCore_isPGroup.comap_subtype
  have hQK₀ : ⁅Q₀, K₀⁆ = ⊥ := by
    rcases hK with hK | hK
    · let : IsQuasisimple K := hK
      let : IsQuasisimple K₀ :=
        IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show K ≤ S from le_sup_left)).symm
      have hc : IsComponent S K₀ := ⟨(inferInstance : K₀.Normal).isSubnormal, inferInstance⟩
      rcases hc.normal_dichotomy Q₀ with hle | hc
      · let : Group.IsNilpotent K₀ := (hQ₀.to_le hle).isNilpotent
        let : IsSimpleGroup (K₀ ⧸ center K₀) := IsQuasisimple.simple
        let : Nontrivial K₀ := (QuotientGroup.mk'_surjective (center K₀)).nontrivial
        exact (Group.IsPerfect.not_isSolvable K₀ inferInstance).elim
      · rwa [commutator_comm]
    · have hkcard : Nat.card K₀ = Nat.card K :=
        Nat.card_congr (subgroupOfEquivOfLe (show K ≤ S from le_sup_left)).toEquiv
      apply commutator_eq_bot_of_disjoint
      apply disjoint_of_coprime_natCard
      exact twoGroup_coprime hQ₀ (hkcard ▸ hK)
  have hQK : ⁅Q, K⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map S.subtype) hQK₀
    simpa only [Q₀, K₀, map_commutator, Subgroup.map_bot,
      map_subgroupOf_eq_of_le (show Q ≤ S from hQS),
      map_subgroupOf_eq_of_le (show K ≤ S from le_sup_left)] using hh
  refine ⟨hQS, le_centralizer_iff.mp ?_⟩
  apply sup_le
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQN)
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQK)

theorem fixedSpace_kernel_eq_twoCore_of_odd_normal_supplement [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hfaith : Function.Injective ρ) (N K A : Subgroup G) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N))
    (hK : IsQuasisimple K ∨ Nat.Coprime 2 (Nat.card K))
    (hA : IsPGroup 2 A) (hKA : ⁅K, A⁆ = K) (hgen : N ⊔ (K ⊔ A) = ⊤) :
    subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G := by
  have hAnorm : A ≤ normalizer (K : Set G) := hKA ▸ normalizer_commutator_ge_right K A
  let : (N ⊔ K).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen, ← sup_assoc]
    apply sup_le (N ⊔ K).le_normalizer
    simpa only [sup_comm K N] using hAnorm.trans
      (normalizer_le_normalizer_sup_normal (H := K) (K := N))
  exact fixedSpace_kernel_eq_twoCore_of_centralizes ρ hfaith (N ⊔ K)
    (quotient_isPGroup_of_sup_eq_top A (N ⊔ K) hA
      (by simpa only [sup_assoc, sup_comm, sup_left_comm] using hgen))
    (twoCore_le_and_centralizes_of_odd_normal_supplement N K A hN hK hKA hgen).2

end Representation.BinaryOffender
