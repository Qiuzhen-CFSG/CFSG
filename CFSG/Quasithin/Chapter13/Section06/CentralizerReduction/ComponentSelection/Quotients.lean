module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Notation

/-!
# Comparing the star and plus action quotients

Since W_K lies in U_v, the kernel of the star action on K₋L_vT_v is
contained in the kernel of its action on W_K. Factoring the latter map
through the former constructs a surjective star-to-plus homomorphism.
Its kernel is the star image of the relative centralizer of W_K, and
both actions are proved to agree on every element of W_K.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
1 March 2004 manuscript, the paragraph preceding 13.6.14, printed p.929.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Subgroup
variable {G : Type*} [Group G]

/-- The surjection from a subgroup of G_v to its actual star image. -/
def starImageMap (z v : G) (H : Subgroup G) (hH : H ≤ Gv v) :
    H →* starImage z v H :=
  ((starMk z v).comp (inclusion hH)).codRestrict (starImage z v H)
    (fun x => mem_map.mpr ⟨⟨x, hH x.property⟩, x.property, rfl⟩)

theorem starImageMap_surjective (z v : G) (H : Subgroup G) (hH : H ≤ Gv v) :
    Function.Surjective (starImageMap z v H hH) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem starImageMap_ker (z v : G) (H : Subgroup G) (hH : H ≤ Gv v) :
    (starImageMap z v H hH).ker = (centralizer (Uv z v : Set G)).subgroupOf H := by
  ext x
  change starImageMap z v H hH x = 1 ↔ (x : G) ∈ centralizer (Uv z v : Set G)
  rw [Subtype.ext_iff]
  change (⟨x, hH x.property⟩ : Gv v) ∈ (starMk z v).ker ↔ _
  rw [starMk_ker]
  rfl

theorem plusActor_le_Gv (K L T : Subgroup G) (v : G) (hK : K ≤ Gv v) :
    plusActor K L T v ≤ Gv v :=
  sup_le (sup_le (Kminus_le_Gv K T v hK) (Lv_le_Gv L v)) inf_le_right

theorem plusMk_surjective (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (plusMk K L T z v hL hz) := QuotientGroup.mk'_surjective _

theorem plusMk_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (plusMk K L T z v hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf (plusActor K L T v) :=
  (QuotientGroup.ker_mk' _).trans (plusConjugation_ker K L T z v hL hz)

/-- Centralizing U_v implies centralizing W_K, so the plus map factors through
this star image. Both kernels are computed inside the same actual actor. -/
theorem starImageMap_ker_le_plusMk_ker (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (starImageMap z v (plusActor K L T v) (plusActor_le_Gv K L T v hK)).ker ≤
      (plusMk K L T z v hL hz).ker := by
  rw [starImageMap_ker, plusMk_ker]
  exact comap_mono (Subgroup.centralizer_le (WK_le_Uv K L T z v hK))

/-- The actual quotient homomorphism (K₋L_vT_v)* → (K₋L_vT_v)⁺. -/
noncomputable def starToPlus (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    starImage z v (plusActor K L T v) →* Gplus K L T z v hL hz :=
  (starImageMap z v (plusActor K L T v) (plusActor_le_Gv K L T v hK)).liftOfSurjective
    (starImageMap_surjective z v _ _) ⟨plusMk K L T z v hL hz,
      starImageMap_ker_le_plusMk_ker K L T z v hK hL hz⟩

theorem starToPlus_mk (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (x : plusActor K L T v) :
    starToPlus K L T z v hK hL hz
      (starImageMap z v (plusActor K L T v) (plusActor_le_Gv K L T v hK) x) =
        plusMk K L T z v hL hz x := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem starToPlus_surjective (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (starToPlus K L T z v hK hL hz) := by
  intro y
  obtain ⟨x, rfl⟩ := plusMk_surjective K L T z v hL hz y
  exact ⟨starImageMap z v _ _ x, starToPlus_mk K L T z v hK hL hz x⟩

/-- The exact kernel of the star-to-plus map is the star image of the
relative centralizer of W_K. -/
theorem starToPlus_ker (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (starToPlus K L T z v hK hL hz).ker =
      ((centralizer (WK K L T z v : Set G)).subgroupOf (plusActor K L T v)).map
        (starImageMap z v (plusActor K L T v) (plusActor_le_Gv K L T v hK)) := by
  have hc : (starToPlus K L T z v hK hL hz).comp
      (starImageMap z v (plusActor K L T v) (plusActor_le_Gv K L T v hK)) =
        plusMk K L T z v hL hz := by
    ext x
    exact starToPlus_mk K L T z v hK hL hz x
  rw [← plusMk_ker K L T z v hL hz, ← hc, ← MonoidHom.comap_ker,
    map_comap_eq_self_of_surjective (starImageMap_surjective z v _ _)]

/-- The star action restricted to W_K agrees with the plus action through
the constructed quotient map. -/
theorem starToPlus_action (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (x : starImage z v (plusActor K L T v)) (w : WK K L T z v) :
    ((starAction z v x ⟨w, WK_le_Uv K L T z v hK w.property⟩ : Uv z v) : G) =
      ((plusAction K L T z v hL hz (starToPlus K L T z v hK hL hz x) w :
        WK K L T z v) : G) := by
  obtain ⟨a, rfl⟩ := starImageMap_surjective z v (plusActor K L T v)
    (plusActor_le_Gv K L T v hK) x
  rw [starToPlus_mk]
  rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
