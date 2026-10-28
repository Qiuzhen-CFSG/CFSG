module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionLayer

/-!
# The natural kernel and fixed line of the canonical core

The elementary local core Q centralizes V, while C_P(V)=P∩V.
Consequently P∩Q=P∩V. Conversely C_H(P)=C_H(K) and D∩V=⟨z⟩
identify the fixed subgroup of P on V with the marked central line.
These identities retain the literal embedding of P from H into G and
supply the kernel and fixed-space inputs to its symmetric-five image.

Source: Aschbacher–Smith, proof of 6.2.13, printed p.687.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The kernel of the canonical core in the local quotient is its natural eight. -/
theorem LocalAnalysis.equality_core_inf_local_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    (equalityCore L R z).map (centralizer ({z} : Set G)).subtype ⊓
        (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      layer L R ⊓ (equalityCore L R z).map (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hc := A.equality_core_layer_centralizer h611 hz hp.plusType
  apply le_antisymm
  · rintro x ⟨⟨p, hpP, rfl⟩, hq⟩
    have hpC : p ∈ centralizer ((layer L R).subgroupOf H : Set H) := by
      intro v hv
      exact Subtype.ext (local_core_centralizes_layer h611 hq v hv)
    have hh : p ∈ equalityCore L R z ⊓ (layer L R).subgroupOf H := hc ▸ ⟨hpP, hpC⟩
    exact ⟨hh.2, mem_map_of_mem H.subtype hpP⟩
  · exact le_inf inf_le_right
      (inf_le_left.trans (h611.layer_le_V.trans (reduced_le_core h611.V_mem)))

/-- The canonical core fixes only the central line on the natural layer.
Together with the natural Sylow fixed plane this excludes an inner four-image. -/
theorem LocalAnalysis.equality_layer_core_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    layer L R ⊓ centralizer
      ((equalityCore L R z).map (centralizer ({z} : Set G)).subtype : Set G) = zpowers z := by
  let H := centralizer ({z} : Set G)
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hVH := layer_le_involution_centralizer h611 hz
  have hc := A.equality_core_centralizer h611 hnatural hz
  apply le_antisymm
  · intro x hx
    have hxH : (⟨x, hVH hx.1⟩ : H) ∈ centralizer (equalityCore L R z : Set H) := by
      intro p hpP
      exact Subtype.ext (hx.2 p (mem_map_of_mem H.subtype hpP))
    have hxD : x ∈ equalityCentralizer L R z :=
      mem_map_of_mem H.subtype (hc ▸ hxH)
    have hh : x ∈ equalityCentralizer L R z ⊓ layer L R := ⟨hxD, hx.1⟩
    rwa [A.equality_centralizer_inf_layer h611 hz hp.core_center] at hh
  · apply le_inf (zpowers_le.mpr hz.1)
    apply zpowers_le.mpr
    rintro p ⟨pH, hpP, rfl⟩
    exact mem_centralizer_singleton_iff.mp pH.property

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
