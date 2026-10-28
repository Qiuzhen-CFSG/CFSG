module
public import Theory.GroupTheory.SylowNormalizerCentralizerCore

/-!
# Recognizing commutator cores by a normalized Sylow image

A p-subgroup contained in H and normalizing a Sylow p-subgroup of H lies
in that Sylow subgroup. Consequently, if [B,C] lies in H and normalizes
the embedded Sylow subgroup T, while T ≤ C and [B,T]=T, its p-core is T.
Normality is relative to [B,C]; neither H nor T must be ambient normal.

Source: the subgroup argument in GLS, Volume 4, Chapter 2, Lemma 13.4.
-/

namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ}

/-- A p-subgroup normalizing an embedded Sylow subgroup lies in it. -/
public theorem le_sylow_image_of_normalizes
    (H : Subgroup G) (P : Sylow p H) {K T : Subgroup G}
    (hP : (P : Subgroup H).map H.subtype = T)
    (hK : IsPGroup p K) (hKH : K ≤ H) (hKT : K ≤ normalizer (T : Set G)) : K ≤ T := by
  have hpre : T.comap H.subtype = (P : Subgroup H) := by
    rw [← hP, comap_map_eq_self_of_injective H.subtype_injective]
  have hn : K.subgroupOf H ≤ normalizer (P : Set H) := by
    apply le_normalizer_iff.mpr
    intro a ha b hb
    rw [← hpre]
    exact ((hKT ha) b).mp (hP ▸ mem_map_of_mem H.subtype hb)
  have hp : IsPGroup p (K.subgroupOf H) := hK.comap_subtype
  have hle : K.subgroupOf H ≤ (P : Subgroup H) := by
    calc
      K.subgroupOf H ≤ K.subgroupOf H ⊓ normalizer (P : Set H) := le_inf le_rfl hn
      _ = K.subgroupOf H ⊓ (P : Subgroup H) := hp.inf_normalizer_sylow P
      _ ≤ (P : Subgroup H) := inf_le_right
  have hm := map_mono (f := H.subtype) hle
  rwa [map_subgroupOf_eq_of_le hKH, hP] at hm

/-- A commutator subgroup containing and normalizing the Sylow image has that p-core. -/
public theorem commutator_pCoreIn_eq_sylow_image
    (H : Subgroup G) (P : Sylow p H) (T B C : Subgroup G)
    (hP : (P : Subgroup H).map H.subtype = T)
    (hH : ⁅B, C⁆ ≤ H) (hN : ⁅B, C⁆ ≤ normalizer (T : Set G))
    (hTC : T ≤ C) (hBT : ⁅B, T⁆ = T) : (⁅B, C⁆).pCoreIn p = T := by
  have hT : IsPGroup p T := hP ▸ P.isPGroup'.map H.subtype
  apply le_antisymm
  · exact le_sylow_image_of_normalizes H P hP (isPGroup_pCoreIn p _)
      ((pCoreIn_le p _).trans hH) ((pCoreIn_le p _).trans hN)
  · apply le_pCoreIn_of_normalizes hT _ hN
    rw [← hBT]
    exact commutator_mono le_rfl hTC

end Subgroup
