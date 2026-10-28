module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Placement
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.RelativeQuotient
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.GroupTheory.Amalgam.LocalStructure
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Intrinsic second-core calculations for the fixed Hall--Janko factors

An isomorphism of the second factor modulo the fixed radical with S₃
identifies that radical with the intrinsic two-core: it is a normal two-group
and S₃ has no nontrivial normal two-subgroup. The checked radical order is 64.
The actual injective inclusion of the carrier into its permutation extension
then transports both the intrinsic core and its quotient to `Seed.outerL 1`.

The full-normalizer coverage and quotient certificates give `p₂/q₂ ≃ S₃ × C₃`.
The relative normal closure of the Sylow image is its S₃ factor, giving the
radical quotient of the literal normal closure `Seed.l₂`. Thus all second-core
and quotient calculations below are unconditional. Normal closure remains
relative to `p₂`; identification with the full automorphism group is separate.
Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
open Theory.GroupTheory Seed PairNormalizer

/-- The genuine inclusion identifies the two copies of the second local factor. -/
noncomputable def secondFactorEquiv : l₂ ≃* outerL 1 :=
  Subgroup.equivMapOfInjective l₂ intoExtension intoExtension_injective

/-- In particular the intrinsic cores, rather than ambient cores, correspond. -/
noncomputable def secondCoreEquiv : pCore 2 l₂ ≃* pCore 2 (outerL 1) :=
  LocalCoreTransport.coreEquiv 2 secondFactorEquiv

noncomputable def secondQuotientEquiv :
    (l₂ ⧸ pCore 2 l₂) ≃* (outerL 1 ⧸ pCore 2 (outerL 1)) :=
  LocalCoreTransport.quotientEquiv 2 secondFactorEquiv

/-- The radical quotient suffices to identify the intrinsic two-core. -/
theorem l₂_core_eq_of_radical_quotient
    (hq : Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3))) :
    pCore 2 l₂ = q₂.subgroupOf l₂ := by
  obtain ⟨e⟩ := hq
  let f : l₂ →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hfker : f.ker = q₂.subgroupOf l₂ := by
    ext x
    change e (QuotientGroup.mk x) = 1 ↔ x ∈ q₂.subgroupOf l₂
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hp : IsPGroup 2 f.ker := by
    rw [hfker]
    exact q₂_isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe q₂_le_l₂).symm
  exact (ker_eq_twoCore_of_surjective_perm_three f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hp).symm.trans hfker

/-- The relative quotient and the checked radical determine the second-factor order. -/
theorem card_l₂_of_radical_quotient
    (hq : Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3))) :
    Nat.card l₂ = 384 := by
  obtain ⟨e⟩ := hq
  have hi : (q₂.subgroupOf l₂).index = 6 := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hc : Nat.card (q₂.subgroupOf l₂) = 64 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe q₂_le_l₂).toEquiv).trans card_q₂
  have h := (q₂.subgroupOf l₂).card_mul_index
  rw [hc, hi] at h
  exact h.symm

/-- The requested intrinsic core cardinality follows from the checked radical enumeration. -/
theorem l₂_core_card_of_radical_quotient
    (hq : Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3))) :
    Nat.card (pCore 2 l₂) = 64 := by
  rw [l₂_core_eq_of_radical_quotient hq]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe q₂_le_l₂).toEquiv).trans card_q₂

/-- Replacing the radical with the proved intrinsic core preserves the actual quotient. -/
theorem l₂_quotient_of_radical_quotient
    (hq : Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3))) :
    Nonempty ((l₂ ⧸ pCore 2 l₂) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := hq
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (l₂_core_eq_of_radical_quotient ⟨e⟩)).trans e⟩

/-- The image factor has the same intrinsic two-core order. -/
theorem outerL₂_core_card_of_radical_quotient
    (hq : Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3))) :
    Nat.card (pCore 2 (outerL 1)) = 64 :=
  (Nat.card_congr secondCoreEquiv.symm.toEquiv).trans
    (l₂_core_card_of_radical_quotient hq)

/-- The outer second quotient is transported along the literal carrier inclusion. -/
theorem outerL₂_quotient_of_radical_quotient
    (hq : Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3))) :
    Nonempty ((outerL 1 ⧸ pCore 2 (outerL 1)) ≃* Equiv.Perm (Fin 3)) :=
  (l₂_quotient_of_radical_quotient hq).map (fun e => secondQuotientEquiv.symm.trans e)

/-- The checked full-normalizer quotient determines the relative normal-closure quotient.
This uses only the radical quotient of `p₂`, with no premise about the core of `l₂`. -/
theorem l₂_radical_quotient :
    Nonempty ((l₂ ⧸ q₂.subgroupOf l₂) ≃* Equiv.Perm (Fin 3)) :=
  l₂_radical_quotient_of_p₂_radical_quotient
    (p₂_quotient_of_coverage full_normalizer_le_candidate candidate_quotient_equiv)

/-- The fixed radical is exactly the intrinsic two-core of the second factor. -/
theorem l₂_core_eq : pCore 2 l₂ = q₂.subgroupOf l₂ :=
  l₂_core_eq_of_radical_quotient l₂_radical_quotient

/-- The second factor has order `64 · 6`. -/
theorem card_l₂ : Nat.card l₂ = 384 :=
  card_l₂_of_radical_quotient l₂_radical_quotient

/-- The second intrinsic two-core has the source order `2⁶`. -/
theorem l₂_core_card : Nat.card (pCore 2 l₂) = 64 :=
  l₂_core_card_of_radical_quotient l₂_radical_quotient

/-- The second factor modulo its intrinsic two-core is S₃. -/
theorem l₂_quotient : Nonempty ((l₂ ⧸ pCore 2 l₂) ≃* Equiv.Perm (Fin 3)) :=
  l₂_quotient_of_radical_quotient l₂_radical_quotient

/-- The same intrinsic core order holds in the concrete permutation extension. -/
theorem outerL₂_core_card : Nat.card (pCore 2 (outerL 1)) = 64 :=
  outerL₂_core_card_of_radical_quotient l₂_radical_quotient

/-- The extension's second factor modulo its intrinsic two-core is S₃. -/
theorem outerL₂_quotient :
    Nonempty ((outerL 1 ⧸ pCore 2 (outerL 1)) ≃* Equiv.Perm (Fin 3)) :=
  outerL₂_quotient_of_radical_quotient l₂_radical_quotient

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
