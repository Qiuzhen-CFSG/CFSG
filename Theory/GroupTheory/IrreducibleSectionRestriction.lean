module
public import Theory.GroupTheory.IrreducibleCenterSeed
/-!
# Restricting irreducible sections and quotient-center bounds

An irreducible conjugation section whose actor and larger term lie in H
remains irreducible after restriction to H. A quotient-center preimage
bound is equivalently the elementwise assertion that every element of S
commuting with S modulo Z lies in the specified subgroup. This expression
transports through subtype maps without comparing quotient instances.

Source application: the intrinsic Mc quotient in Aschbacher--Smith
14.6.9(k)--(n), printed p.1027.
-/

public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem irreducible_section_subgroupOf
    (H B A C : Subgroup G) (hBH : B ≤ H) (hCH : C ≤ H)
    (hirr : IsIrreducibleSection B A C) :
    IsIrreducibleSection (B.subgroupOf H) (A.subgroupOf H) (C.subgroupOf H) := by
  have hAH := hirr.1.trans hCH
  refine ⟨comap_mono hirr.1,?_,?_⟩
  · intro he
    apply hirr.2.1
    have he' := congrArg (Subgroup.map H.subtype) he
    simpa only [map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hCH] using he'
  · intro W hAW hWC hi
    have hWA : A ≤ W.map H.subtype := by
      rw [←map_subgroupOf_eq_of_le hAH]
      exact map_mono hAW
    have hCW : W.map H.subtype ≤ C := (map_mono hWC).trans_eq
      (map_subgroupOf_eq_of_le hCH)
    have hinv : IsConjugateInvariantBy (W.map H.subtype) B := by
      intro b w hw
      obtain ⟨v,hv,rfl⟩ := hw
      exact mem_map_of_mem H.subtype (hi ⟨⟨b,hBH b.property⟩,b.property⟩ v hv)
    rcases hirr.2.2 (W.map H.subtype) hWA hCW hinv with he | he
    · left
      apply (Subgroup.map_injective H.subtype_injective)
      rw [map_subgroupOf_eq_of_le hAH]
      exact he
    · right
      apply (Subgroup.map_injective H.subtype_injective)
      rw [map_subgroupOf_eq_of_le hCH]
      exact he

theorem quotient_center_preimage_le_iff
    (S Z E : Subgroup G) [(Z.subgroupOf S).Normal] :
    ((center (S ⧸ Z.subgroupOf S)).comap (QuotientGroup.mk' (Z.subgroupOf S))).map S.subtype ≤ E ↔
      ∀ s ∈ S, (∀ t ∈ S, ⁅t,s⁆ ∈ Z) → s ∈ E := by
  let q := QuotientGroup.mk' (Z.subgroupOf S)
  constructor
  · intro hh s hs hc
    apply hh
    refine ⟨⟨s,hs⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨t,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf S) y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hc t t.property)
  · intro hh s hs
    obtain ⟨x,hx,rfl⟩ := hs
    apply hh x x.property
    intro t ht
    have he := mem_center_iff.mp hx (q ⟨t,ht⟩)
    change ⁅(⟨t,ht⟩:S),x⁆ ∈ Z.subgroupOf S
    apply (QuotientGroup.eq_one_iff (⁅(⟨t,ht⟩:S),x⁆)).mp
    change q ⁅(⟨t,ht⟩:S),x⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact he

theorem normalizes_subgroupOf_of_normalizes (H B A : Subgroup G)
    (hn : B ≤ normalizer (A : Set G)) :
    B.subgroupOf H ≤ normalizer (A.subgroupOf H : Set H) := by
  intro b hb
  apply mem_normalizer_iff.mpr
  intro a
  exact mem_normalizer_iff.mp (hn hb) (a : G)

end Theory.GroupTheory
