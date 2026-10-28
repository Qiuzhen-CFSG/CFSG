module
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Embedded Sylow cores and normalized commutator cores

The p-core of a Sylow normalizer is its Sylow subgroup, and faithful maps
preserve this identity with the literal ambient inclusions. An element
centralizing B and normalizing K also normalizes O_p([B,C_G(K)]): conjugation
preserves the commutator, and the p-core is characteristic inside it.

These are the subgroup arguments used for T, V and T₁ in GLS, Volume 4,
Chapter 2, the definitions before Lemma 13.4 and its proof. They assert no
ambient normality of the local groups.
-/

open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- A faithful image of a Sylow subgroup is the core of its mapped normalizer. -/
public theorem sylow_map_eq_pCoreIn_of_normalizer_map_eq {p : ℕ}
    (P : Sylow p H) (f : H →* G) (hf : Function.Injective f)
    (K : Subgroup G) (hK : (normalizer (P : Set H)).map f = K) :
    (P : Subgroup H).map f = K.pCoreIn p := by
  have he : (normalizer (P : Set H)).pCoreIn p = (P : Subgroup H) := by
    apply le_antisymm
    · have hc := pCoreIn_le_sylow (normalizer (P : Set H)) (P.subtype (P : Subgroup H).le_normalizer)
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hc hx
      exact hy
    · exact le_pCoreIn_of_normalizes P.isPGroup' (P : Subgroup H).le_normalizer le_rfl
  rw [← hK, ← map_pCoreIn_of_injective p _ f hf, he]

/-- Relative characteristicity preserves the commutator core under both normalizers. -/
public theorem centralizer_inf_normalizer_le_normalizer_commutator_core
    (B K : Subgroup G) (p : ℕ) :
    centralizer (B : Set G) ⊓ normalizer (K : Set G) ≤
      normalizer ((⁅B, centralizer (K : Set G)⁆).pCoreIn p : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    ⁅B, centralizer (K : Set G)⁆ (pCore p (⁅B, centralizer (K : Set G)⁆ : Subgroup G)))
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator]
  have hB := mem_normalizer_iff_map_conj_eq.mp (centralizer_le_normalizer (B : Set G) hg.1)
  have hC := mem_normalizer_iff_map_conj_eq.mp ((normalizer_le_normalizer_centralizer K) hg.2)
  rw [hB, hC]
end Subgroup
