module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.JoinKernel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.PairedGeneration

/-!
# Covering the plus actor by the original component--Sylow join

Containment of Lᵥ⁺ in K₋⁺ makes the map from K∨Tᵥ onto the full plus actor
surjective. The original W_K also lies in this join: every conjugation of
its seed by the full actor agrees with one from the join. Consequently
the paired argument can use the proved two-group kernel on K∨Tᵥ without
requiring a stronger containment of Lᵥ in K₋ before taking plus images.

Source: the paired Borel step of Aschbacher--Smith 13.6.14, pp.929--930.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G]

theorem joinPlusMap_image_source (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (B : Subgroup G) (hB : B ≤ K ⊔ Tv T v) :
    (B.subgroupOf (K ⊔ Tv T v)).map (joinPlusMap K L T z v hL hz) =
      plusImage K L T z v hL hz B := by
  ext y
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact mem_map.mpr ⟨inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) b,hb,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact mem_map.mpr ⟨⟨b,hB hb⟩,hb,rfl⟩

theorem joinPlusMap_surjective_of_plus_placement_source
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v)) :
    Function.Surjective (joinPlusMap K L T z v hL hz) := by
  apply MonoidHom.range_eq_top.mp
  apply top_le_iff.mp
  rw [←paired_plus_generation_of_plus_placement_source K L T z v hL hz hLv]
  have hKm : Kminus K T v ≤ K ⊔ Tv T v :=
    conjugateSpanBy_le le_sup_left (le_sup_right.trans (K ⊔ Tv T v).le_normalizer)
  rw [←joinPlusMap_image_source K L T z v hL hz _ hKm,
    ←joinPlusMap_image_source K L T z v hL hz _ le_sup_right]
  exact sup_le (map_le_range _ _) (map_le_range _ _)

theorem WK_le_join_of_plus_placement_source
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hzT : z ∈ Tv T v)
    (hLv : plusImage K L T z v hL hz (Lv L v) ≤
      plusImage K L T z v hL hz (Kminus K T v)) :
    WK K L T z v ≤ K ⊔ Tv T v := by
  let H := K ⊔ Tv T v
  let A := plusActor K L T v
  have hZH : zpowers z ≤ H := zpowers_le.mpr ((show Tv T v ≤ H from le_sup_right) hzT)
  have hZW : zpowers z ≤ WK K L T z v := le_conjugateSpanBy _ _
  apply (closure_le _).mpr
  rintro x ⟨a,ha,u,hu,rfl⟩
  let aA : A := ⟨a,(show Kminus K T v ⊔ Lv L v ≤ A from le_sup_left) ha⟩
  obtain ⟨b,hb⟩ := joinPlusMap_surjective_of_plus_placement_source K L T z v hL hz hLv
    (plusMk K L T z v hL hz aA)
  have he := congrArg (fun g => ((plusAction K L T z v hL hz g ⟨u,hZW hu⟩ : WK K L T z v) : G)) hb
  have he' : (b : G) * u * (b : G)⁻¹ = a * u * a⁻¹ := he
  rw [←he']
  exact H.mul_mem (H.mul_mem b.property (hZH hu)) (H.inv_mem b.property)

theorem joinPlusMap_ker_source (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (joinPlusMap K L T z v hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf (K ⊔ Tv T v) := by
  ext x
  change inclusion (sup_le (K_le_plusActor K L T v) le_sup_right) x ∈
    (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
