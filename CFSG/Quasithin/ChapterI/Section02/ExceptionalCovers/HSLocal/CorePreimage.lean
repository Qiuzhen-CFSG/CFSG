module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Setup

/-!
# The two-core under the literal HS normalizer covering map

Restrict the specified central quotient map to M and its actual model
normalizer. This is a surjection with kernel Z(K), embedded relatively in
M. When the center has order two, the inverse image of the model two-core
is exactly Q, and its order doubles. This keeps the central-cover kernel
and two-core maps available for the remaining abelian-core calculation.

Source: the HS normalizer paragraph of Aschbacher–Smith I.2.2(5), printed
p.412 / PDF p.423. No identification of the model two-core with 4³ is assumed.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Subgroup
open Sporadic.LeechRelated.HS.BlockNormalizer
variable {K : Type*} [Group K]

theorem modelMap_ker (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (modelMap e).ker = center K := by
  ext x
  change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

theorem center_le_M (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    center K ≤ M e := by
  intro x hx
  change modelMap e x ∈ baseNormalizer
  have h : modelMap e x = 1 := by
    change x ∈ (modelMap e).ker
    rwa [modelMap_ker]
  rw [h]
  exact one_mem _

/-- Restriction of the same quotient map to the actual normalizer preimage. -/
def localMap (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    M e →* baseNormalizer :=
  ((modelMap e).comp (M e).subtype).codRestrict baseNormalizer (fun m => m.property)

theorem localMap_surjective
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Function.Surjective (localMap e) := by
  intro x
  obtain ⟨k, hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) x.val
  change modelMap e k = x.val at hk
  have hm : k ∈ M e := by
    change modelMap e k ∈ baseNormalizer
    exact hk.symm ▸ x.property
  exact ⟨⟨k, hm⟩, Subtype.ext hk⟩

theorem localMap_ker
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (localMap e).ker = (center K).subgroupOf (M e) := by
  ext x
  change localMap e x = 1 ↔ (x : K) ∈ center K
  rw [← Subtype.val_inj]
  change modelMap e (x : K) = 1 ↔ (x : K) ∈ center K
  change (x : K) ∈ (modelMap e).ker ↔ _
  rw [modelMap_ker]

theorem localMap_ker_card
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Nat.card (localMap e).ker = Nat.card (center K) := by
  rw [localMap_ker]
  exact Nat.card_congr (subgroupOfEquivOfLe (center_le_M e)).toEquiv

/-- The normalizer's actual two-core pulls back to Q in the double cover. -/
theorem Q_eq_model_core_preimage [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    Q e = (pCore 2 baseNormalizer).comap (localMap e) := by
  have hk : IsPGroup 2 (localMap e).ker := IsPGroup.of_card (n := 1)
    (by rw [localMap_ker_card, hZ, pow_one])
  exact ((localMap e).comap_pCore_of_ker_isPGroup (localMap_surjective e) hk).symm

/-- The actual preimage core has twice the order of the model core. -/
theorem Q_card [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    Nat.card (Q e) = 2 * Nat.card (pCore 2 baseNormalizer) := by
  have hk : IsPGroup 2 (localMap e).ker := IsPGroup.of_card (n := 1)
    (by rw [localMap_ker_card, hZ, pow_one])
  simpa only [Q, localMap_ker_card, hZ] using
    (localMap e).card_pCore_of_ker_isPGroup (localMap_surjective e) hk

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
