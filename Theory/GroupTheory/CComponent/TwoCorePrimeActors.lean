module
public import Theory.GroupTheory.CComponent.PrimeRankOuterTwo

/-!
# Odd prime actors through the ambient two-core quotient

Coprime-kernel absorption preserves whether an odd-prime actor lies in a
normal subgroup. A C-component with quasisimple two-core quotient becomes
an ordinary component in this literal ambient quotient. These facts allow
ordinary-component automorphism theorems to apply without assuming that
the original two-core is central.

Source: Aschbacher–Smith, A.3.18, pp.51–53; original 4.3.12(2), p.617.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.CComponentPrimeRank
variable {G : Type*} [Group G] [Finite G]

/-- Odd-prime membership lifts through any normal two-subgroup. -/
theorem prime_actor_mem_of_twoGroup_image (N B : Subgroup G) [N.Normal] [B.Normal]
    (hN : IsPGroup 2 N) {p : ℕ} (ho : Odd p) (x : G) (hx : orderOf x = p)
    (hi : QuotientGroup.mk' N x ∈ B.map (QuotientGroup.mk' N)) : x ∈ B := by
  apply Theory.GroupAction.ComponentRankAction.prime_element_mem_of_image_mem
    (QuotientGroup.mk' N) ?_ B x hx hi
  rw [QuotientGroup.ker_mk']
  obtain ⟨k, hk⟩ := hN.exists_card_eq
  rw [hk]
  exact (Nat.coprime_two_right.mpr ho).pow_right k

/-- A quasisimple two-core quotient is an ordinary component in the
ambient two-core quotient, without assuming the original core central. -/
theorem twoCore_image_isComponent {B : Subgroup G} (hB : B.IsCComponent)
    [IsQuasisimple (B ⧸ pCore 2 B)] :
    IsComponent (G ⧸ pCore 2 G) (B.map (QuotientGroup.mk' (pCore 2 G))) := by
  exact ⟨hB.subnormal.map (QuotientGroup.mk'_surjective _),
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hB)⟩

end Theory.GroupTheory.CComponentPrimeRank
