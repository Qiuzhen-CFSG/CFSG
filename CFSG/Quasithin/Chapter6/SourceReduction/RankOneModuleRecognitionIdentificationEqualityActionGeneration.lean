module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityActionRecognition

/-!
# Generation of the involution centralizer in the equality branch

The central marked transvection normally generates the actual actor quotient
by G.6.4. It lies in the image of the layer, so the layer's normal closure K
maps onto H/O₂(H). Thus H = KO₂(H), and O₂(H) lies in the chosen Sylow
two-subgroup T, giving the literal ambient supplement H = KT.

This conclusion precedes exclusion of the larger action models and is reused
by the canonical pair construction. It asserts no splitting of the extension.

Source: Aschbacher–Smith, 6.2.13, printed p.687 (PDF p.704).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The normal closure of the actual layer maps onto the entire actor quotient. -/
theorem LocalAnalysis.equalityLayerClosure_image_top
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ZS (T : Subgroup G) L R) :
    (equalityLayerClosure L R z).map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) =
      ⊤ := by
  obtain ⟨a, ha, _, _, _, hgen, _⟩ :=
    A.equality_action_classification h611 hnatural hz horder hTH hbranch
  apply top_unique
  rw [← hgen]
  apply normalClosure_le_normal
  rintro x ⟨rfl⟩
  exact (map_mono (show (layer L R).subgroupOf (centralizer ({z} : Set G)) ≤
    equalityLayerClosure L R z from le_normalClosure)) ha

/-- The quotient generation lifts to the literal source supplement H = KT. -/
theorem LocalAnalysis.equalityLayerClosure_sup_sylow
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R =
      ZS (T : Subgroup G) L R) :
    centralizer ({z} : Set G) =
      (equalityLayerClosure L R z).map (centralizer ({z} : Set G)).subtype ⊔ (T : Subgroup G) := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let Q := pCore 2 H
  let S := (T : Subgroup G).subgroupOf H
  have hKQ : K ⊔ Q = ⊤ := by
    have hmap : K.map (QuotientGroup.mk' Q) = ⊤ :=
      A.equalityLayerClosure_image_top h611 hnatural hz horder hTH hbranch
    have he := congrArg (comap (QuotientGroup.mk' Q)) hmap
    simpa only [QuotientGroup.comap_map_mk', comap_top, sup_comm] using he
  have hQS : Q ≤ S := by
    simpa only [Sylow.coe_subtype] using fitting_pCore_le_sylow (T.subtype hTH)
  have hKS : K ⊔ S = ⊤ := top_unique (hKQ ▸ sup_le_sup_left hQS K)
  have he := congrArg (map H.subtype) hKS
  rw [Subgroup.map_sup] at he
  change map H.subtype K ⊔ map H.subtype ((T : Subgroup G).subgroupOf H) =
    map H.subtype ⊤ at he
  rw [map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] at he
  exact he.symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
