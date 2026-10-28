module

public import Theory.GroupTheory.SylowCentralFusion.LocalMover

/-!
# Normal-closure selection for central conjugates

If a distinct conjugate of z also centralizes T, Burnside's fusion lemma gives
a mover in N_G(T). Generate the conjugates of z under this normalizer. The
resulting Q lies in T and in the ambient normal closure of z. Since all of T
normalizes Q, its normalizer has the specified Sylow subgroup automatically.

This is the first case of Glauberman's Lemma 1, p.155, Math. Z. 93 (1966),
DOI 10.1007/BF01111033. The construction works for any element of T.
-/

namespace SylowCentralFusion
open Subgroup
universe u
variable {G : Type u} [Group G]

/-- Generate z's conjugates under N_G(T). The resulting subgroup is normal
in N_G(T), contained in T, and contained in the ambient normal closure of z. -/
public theorem exists_normalClosure_normalizerSelection_of_normalizes_sylow
    (T : Sylow 2 G) (z : G) (hzT : z ∈ (T : Subgroup G))
    (hf : ∃ g ∈ normalizer (T : Set G), g * z * g⁻¹ ≠ z) :
    ∃ s : NormalizerSelection T z,
      s.subgroup ≤ normalClosure ({z} : Set G) := by
  let N := normalizer (T : Set G)
  let zn : N := ⟨z, le_normalizer hzT⟩
  let C : Subgroup N := normalClosure ({zn} : Set N)
  let Q := C.map N.subtype
  let : ((T : Subgroup G).subgroupOf N).Normal := by
    change ((T : Subgroup G).subgroupOf (normalizer ((T : Subgroup G) : Set G))).Normal
    infer_instance
  have hCN : C ≤ (T : Subgroup G).subgroupOf N :=
    normalClosure_le_normal (Set.singleton_subset_iff.mpr hzT)
  have hQT : Q ≤ (T : Subgroup G) := by
    intro q hq
    obtain ⟨c, hc, rfl⟩ := hq
    exact hCN hc
  have hzQ : z ∈ Q := mem_map.mpr ⟨zn, subset_normalClosure (by simp), rfl⟩
  have hNQ : N ≤ normalizer (Q : Set G) := by
    intro n hn
    apply le_normalizer_map N.subtype
    refine mem_map.mpr ⟨⟨n, hn⟩, ?_, rfl⟩
    rw [C.normalizer_eq_top]
    exact mem_top _
  have hTN : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    le_normalizer.trans hNQ
  have hSylow : ∃ R : Sylow 2 (normalizer (Q : Set G)),
      (R : Subgroup (normalizer (Q : Set G))).map
        (normalizer (Q : Set G)).subtype =
          (T : Subgroup G) ⊓ normalizer (Q : Set G) := by
    exact ⟨T.subtype hTN, by rw [Sylow.coe_subtype, subgroupOf_map_subtype]⟩
  obtain ⟨g, hgN, hgm⟩ := hf
  refine ⟨⟨Q, hQT, hzQ, hSylow, g, hNQ hgN, hgm⟩, ?_⟩
  change C.map N.subtype ≤ normalClosure ({z} : Set G)
  simpa only [Set.image_singleton, subtype_apply, zn] using
    map_normalClosure_le ({zn} : Set N) N.subtype

/-- Burnside fusion supplies the normal-closure selection when a distinct
conjugate of z centralizes the Sylow subgroup. -/
public theorem exists_normalClosure_normalizerSelection_of_central_conjugate
    [Finite G] (T : Sylow 2 G) (z : G) (hzT : z ∈ (T : Subgroup G))
    (hz : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hf : ∃ g : G, g * z * g⁻¹ ∈ centralizer (T : Set G) ∧ g * z * g⁻¹ ≠ z) :
    ∃ s : NormalizerSelection T z,
      s.subgroup ≤ normalClosure ({z} : Set G) := by
  obtain ⟨g, hgc, hgm⟩ := hf
  obtain ⟨n, hn, he⟩ := T.conj_eq_normalizer_conj_of_mem_centralizer z g⁻¹
    hz (by simpa only [inv_inv] using hgc)
  apply exists_normalClosure_normalizerSelection_of_normalizes_sylow T z hzT
  refine ⟨n⁻¹, (normalizer (T : Set G)).inv_mem hn, ?_⟩
  simpa only [inv_inv, ← he] using hgm

end SylowCentralFusion
