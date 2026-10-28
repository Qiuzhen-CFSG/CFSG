module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Frattini
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import Theory.GroupTheory.SylowImageIntersection

/-!
# The component Baumann normalizer and its literal parabolic image

Work inside K T_v, where K is normal and T_v is Sylow. The Baumann
Frattini lift factors as k t. Since T_v normalizes its Baumann subgroup,
k does as well. Sylow image transport supplies an element of K ∩ T_v
with the same image as t, correcting k to a lift inside N_K(Baum(T)).
This keeps the arbitrary quotient kernel and the relative normalizer.

Applying 13.6.4 and the literal Baumann radical equality identifies the
image under the chosen component action with the full line parabolic.
No action of the two-residual onto that full parabolic is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the Frattini argument in the proof of Lemma 13.6.20, printed p.931.
-/

public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry
open ChapterB
variable {G D : Type*} [Group G] [Group D] [Finite G]

private theorem baumann_lift (P : Sylow 2 G) (f : G →* D) (x : G)
    (hx : f x ∈ normalizer ((baumann (P : Subgroup G)).map f : Set D)) :
    ∃ a ∈ normalizer (baumann (P : Subgroup G) : Set G), f a = f x := by
  let B := baumann (P : Subgroup G)
  have hB : (B.map f).subgroupOf f.range = B.map f.rangeRestrict := by
    apply map_injective f.range.subtype_injective
    rw [map_subgroupOf_eq_of_le (map_le_range _ _), map_map]
    rfl
  have hx' : f.rangeRestrict x ∈ normalizer (B.map f.rangeRestrict : Set f.range) := by
    rw [← hB, ← subgroupOf_normalizer_eq (map_le_range _ _)]
    exact hx
  rw [← baumann_normalizer_map P f.rangeRestrict f.rangeRestrict_surjective] at hx'
  obtain ⟨a, ha, he⟩ := hx'
  exact ⟨a, ha, congrArg Subtype.val he⟩

private theorem normal_baumann_normalizer_image
    (P : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hNP : N ⊔ (P : Subgroup G) = ⊤) (f : G →* D) :
    (N ⊓ normalizer (baumann (P : Subgroup G) : Set G)).map f =
      N.map f ⊓ normalizer ((baumann (P : Subgroup G)).map f : Set D) := by
  apply le_antisymm (le_inf (map_mono inf_le_left)
    ((map_mono inf_le_right).trans ((baumann (P : Subgroup G)).le_normalizer_map f)))
  rintro q ⟨⟨n, hn, rfl⟩, hqn⟩
  obtain ⟨a, ha, he⟩ := baumann_lift P f n hqn
  obtain ⟨k, hk, t, ht, hkt⟩ := mem_sup_of_normal_left.mp (hNP.symm ▸ mem_top a)
  have htB : t ∈ normalizer (baumann (P : Subgroup G) : Set G) :=
    normalizer_le_normalizer_baumann _ ((P : Subgroup G).le_normalizer ht)
  have hkB : k ∈ normalizer (baumann (P : Subgroup G) : Set G) := by
    have hh := (normalizer (baumann (P : Subgroup G) : Set G)).mul_mem ha
      ((normalizer (baumann (P : Subgroup G) : Set G)).inv_mem htB)
    simpa only [← hkt, mul_inv_cancel_right] using hh
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal N
  have hi := P.map_image_eq_inf N _ Q hQ inf_le_left f
  have hft : f t ∈ N.map f := by
    have hh : f t = (f k)⁻¹ * f n := by rw [← he, ← hkt, map_mul]; group
    rw [hh]
    exact mul_mem (inv_mem (mem_map_of_mem f hk)) (mem_map_of_mem f hn)
  have hm : f t ∈ ((P : Subgroup G) ⊓ N).map f := by
    rw [hi]
    exact ⟨mem_map_of_mem f ht, hft⟩
  obtain ⟨u, hu, heu⟩ := hm
  refine ⟨k * u, ⟨mul_mem hk hu.2, mul_mem hkB ?_⟩, ?_⟩
  · exact normalizer_le_normalizer_baumann _ ((P : Subgroup G).le_normalizer hu.1)
  · rw [map_mul, heu, ← map_mul, hkt, he]

open ComponentSelection
variable {K L T : Subgroup G} {z v : G}

/-- The Frattini lift restricted to the actual component. -/
theorem componentNormalizer_plusImage
    (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (h1364 : baumann T = baumann (Tv T v)) :
    plusImage K L T z v hL hz (componentNormalizer K T) =
      plusImage K L T z v hL hz K ⊓
        normalizer (plusImage K L T z v hL hz (baumann T) : Set _) := by
  let H := K ⊔ Tv T v
  have hHA : H ≤ plusActor K L T v := sup_le (K_le_plusActor K L T v) le_sup_right
  have hBH : baumann T ≤ H := by rw [h1364]; exact inf_le_left.trans le_sup_right
  let f := (plusMk K L T z v hL hz).comp (inclusion hHA)
  have hmap (J : Subgroup G) (hJ : J ≤ H) :
      (J.subgroupOf H).map f = plusImage K L T z v hL hz J := by
    ext q
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨inclusion hHA a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, hJ ha⟩, ha, rfl⟩
  obtain ⟨P, hP⟩ := S.exists_map_subtype_eq_of_le
    (show H ≤ Gv v from sup_le hK inf_le_right)
    (show (S : Subgroup (Gv v)).map (Gv v).subtype ≤ H by rw [hS]; exact le_sup_right)
  have hB : baumann (P : Subgroup H) = (baumann T).subgroupOf H := by
    apply map_injective H.subtype_injective
    change ((P : Subgroup H) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (P : Subgroup H)) : Set H)).map
        H.subtype = _
    rw [baumann_map_injective H.subtype H.subtype_injective, hP, hS,
      map_subgroupOf_eq_of_le hBH, h1364]
    rfl
  let N := K.subgroupOf H
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  have hNP : N ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      hP, hS, ← MonoidHom.range_eq_map, H.range_subtype]
  have hh := normal_baumann_normalizer_image P N hNP f
  rw [hB, ← subgroupOf_normalizer_eq hBH] at hh
  change ((componentNormalizer K T).subgroupOf H).map f =
    (K.subgroupOf H).map f ⊓ normalizer (((baumann T).subgroupOf H).map f : Set _) at hh
  rw [hmap (componentNormalizer K T) (inf_le_left.trans le_sup_left), hmap _ le_sup_left, hmap _ hBH] at hh
  exact hh

/-- The literal action of N_K(Baum(T)) is the entire line parabolic. -/
theorem componentNormalizer_actionMap_range
    (hK : K ≤ Gv v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (d : DoubledCoordinates K L T z v hK hL hz)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (h1364 : baumann T = baumann (Tv T v))
    (hB : plusImage K L T z v hL hz (baumann T) =
      BinaryLinearThree.R.map (modelEmbedding d)) :
    (d.actionMap.comp
      (inclusion (show componentNormalizer K T ≤ K from inf_le_left))).range =
        Matrix.PSL3Two.lineParabolicSL := by
  let f := d.actionMap.comp
    (inclusion (show componentNormalizer K T ≤ K from inf_le_left))
  have hN := componentNormalizer_plusImage hK hL hz hn S hS h1364
  apply le_antisymm
  · rintro a ⟨k, rfl⟩
    rw [← normalizer_radical]
    have hm : modelEmbedding d (f k) ∈ normalizer
        (BinaryLinearThree.R.map (modelEmbedding d) : Set _) := by
      rw [← hB]
      have hk : modelEmbedding d (f k) ∈
          plusImage K L T z v hL hz (componentNormalizer K T) := by
        change modelEmbedding d (d.actionMap (inclusion inf_le_left k)) ∈ _
        rw [modelEmbedding_actionMap]
        exact ⟨inclusion (K_le_plusActor K L T v) (inclusion inf_le_left k), k.property, rfl⟩
      exact (hN ▸ hk).2
    have hi := le_normalizer_comap (H := BinaryLinearThree.R.map (modelEmbedding d))
      (modelEmbedding d) hm
    rwa [comap_map_eq_self_of_injective (modelEmbedding_injective d)] at hi
  · intro a ha
    have hm : modelEmbedding d a ∈ plusImage K L T z v hL hz (componentNormalizer K T) := by
      rw [hN, hB]
      refine ⟨(d.actor.symm a).property, ?_⟩
      apply BinaryLinearThree.R.le_normalizer_map (modelEmbedding d)
      exact ⟨a, normalizer_radical.symm ▸ ha, rfl⟩
    obtain ⟨k, hk, he⟩ := hm
    refine ⟨⟨k, hk⟩, ?_⟩
    apply modelEmbedding_injective d
    change modelEmbedding d (d.actionMap ⟨k, hk.1⟩) = modelEmbedding d a
    rw [modelEmbedding_actionMap]
    exact he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry
