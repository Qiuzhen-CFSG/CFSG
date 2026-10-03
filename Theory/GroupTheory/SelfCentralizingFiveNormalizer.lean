module

public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.Tactic

/-!
# Cyclic complements in a self-centralizing five-normalizer

If a subgroup of order five is self-centralizing and has normalizer of order
twenty, Schur–Zassenhaus supplies a complement of order four. Its conjugation
action on the five-subgroup is faithful, so the cyclic automorphism group of
that subgroup makes the complement cyclic. The result is stated in the ambient
group, retaining both intersection and generation.

This is the elementary splitting used by Wong (1964), Theorem 6(a), p.107,
DOI 10.1017/S1446788700022771.
-/

namespace Subgroup

/-- A self-centralizing five-subgroup with normalizer order twenty has a cyclic
four-complement inside its actual normalizer. -/
public theorem exists_cyclic_four_complement_of_card_twenty
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (hP : Nat.card P = 5) (hC : centralizer (P : Set G) = P)
    (hN : Nat.card (normalizer (P : Set G)) = 20) :
    ∃ F : Subgroup G, IsCyclic F ∧ Nat.card F = 4 ∧
      F ≤ normalizer (P : Set G) ∧ P ⊓ F = ⊥ ∧ P ⊔ F = normalizer (P : Set G) := by
  let N := normalizer (P : Set G)
  let PN := P.subgroupOf N
  have hPN : Nat.card PN = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe P.le_normalizer).toEquiv).trans hP
  have hindex : PN.index = 4 := by
    have h := PN.card_mul_index
    rw [hPN, hN] at h
    omega
  obtain ⟨K, hK⟩ := exists_right_complement'_of_coprime
    (show (Nat.card PN).Coprime PN.index by rw [hPN, hindex]; decide)
  have hKcard : Nat.card K = 4 := hK.symm.index_eq_card.symm.trans hindex
  let γ : K →* MulAut P := P.normalizerMonoidHom.comp K.subtype
  have hγ : Function.Injective γ := by
    apply (MonoidHom.ker_eq_bot_iff γ).mp
    apply bot_unique
    intro k hk
    have hkP : (k : N) ∈ PN := by
      have hh : (k : N) ∈ P.normalizerMonoidHom.ker := hk
      rwa [normalizerMonoidHom_ker, hC] at hh
    exact Subtype.ext (disjoint_def.mp hK.disjoint hkP k.property)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let eAut : MulAut P ≃* (ZMod 5)ˣ := by
    have h := IsCyclic.mulAutMulEquiv P
    rw [hP] at h
    exact h
  let : IsCyclic (MulAut P) := isCyclic_of_injective eAut.toMonoidHom eAut.injective
  let : IsCyclic K := isCyclic_of_injective γ hγ
  let F := K.map N.subtype
  let eF := K.equivMapOfInjective N.subtype N.subtype_injective
  refine ⟨F, isCyclic_of_surjective eF eF.surjective, ?_, ?_, ?_, ?_⟩
  · exact (card_map_of_injective N.subtype_injective).trans hKcard
  · exact map_subtype_le K
  · have h := congrArg (fun H : Subgroup N => H.map N.subtype) hK.disjoint.eq_bot
    rwa [map_inf _ _ _ N.subtype_injective, map_subgroupOf_eq_of_le P.le_normalizer,
      map_bot] at h
  · have h := congrArg (fun H : Subgroup N => H.map N.subtype) hK.sup_eq_top
    rw [map_sup, map_subgroupOf_eq_of_le P.le_normalizer,
      ← MonoidHom.range_eq_map, range_subtype] at h
    exact h

end Subgroup
