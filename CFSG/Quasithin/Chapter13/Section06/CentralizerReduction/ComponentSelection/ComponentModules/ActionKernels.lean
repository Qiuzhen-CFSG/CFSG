module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Seeds
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Quotients
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The component in the plus action quotient

For every actual K in Y_z, its star image is subnormal in the star image
of K₋L_vT_v. The local C-component condition gives the first subnormal
chain, and the X_z normalization condition extends that chain to the
whole actor. Its image K⁺ is subnormal in the faithful plus quotient.

K⁺ is nontrivial: otherwise K and then its T_v-conjugate span centralize
W_K and hence z, contradicting membership in X_z. When the plus quotient
has trivial two-core, the actual restricted star-to-plus map kills
O₂(K*). It therefore gives a surjection K*/O₂(K*) → K⁺, proving that K⁺
is quasisimple. The restricted map's kernel is exactly the star image
of C_K(W_K). No T_v-invariance of K is assumed.

The two-reduced action condition is the relevant part of the source's
W_K ∈ R₂(K₋L_vT_v), obtained there using B.2.14. Deriving that condition
from the full earlier setup is separate from these quotient deductions.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
1 March 2004 manuscript, the paragraph preceding 13.6.14, printed p.929.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G]

private theorem map_span {D : Type*} [Group D] (f : G →* D) (Z H : Subgroup G) :
    (conjugateSpanBy Z H).map f = conjugateSpanBy (Z.map f) (H.map f) := by
  unfold conjugateSpanBy
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨h, hh, z, hz, rfl⟩, rfl⟩
    exact ⟨f h, mem_map.mpr ⟨h, hh, rfl⟩, f z, mem_map.mpr ⟨z, hz, rfl⟩,
      by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨h * z * h⁻¹, ⟨h, hh, z, hz, rfl⟩, by simp⟩

private theorem span_subgroupOf (Z H D : Subgroup G) (hZ : Z ≤ D) (hH : H ≤ D) :
    (conjugateSpanBy Z H).subgroupOf D =
      conjugateSpanBy (Z.subgroupOf D) (H.subgroupOf D) := by
  apply map_injective D.subtype_injective
  rw [map_subgroupOf_eq_of_le (conjugateSpanBy_le hZ (hH.trans D.le_normalizer)),
    map_span, map_subgroupOf_eq_of_le hZ, map_subgroupOf_eq_of_le hH]

theorem starImage_Kminus (K T : Subgroup G) (z v : G) (hK : K ≤ Gv v) :
    starImage z v (Kminus K T v) =
      conjugateSpanBy (starImage z v K) (starImage z v (Tv T v)) := by
  unfold starImage Kminus
  rw [span_subgroupOf K (Tv T v) (Gv v) hK inf_le_right, map_span]

theorem le_starPreimage_starImage (z v : G) (H : Subgroup G) (hH : H ≤ Gv v) :
    H ≤ starPreimage z v (starImage z v H) := by
  intro x hx
  exact mem_map.mpr ⟨⟨x, hH hx⟩, mem_map.mpr ⟨⟨x, hH hx⟩, hx, rfl⟩, rfl⟩

/-- The extra elements in the full preimage differ by the actual action kernel. -/
theorem starPreimage_starImage_factor (z v : G) (H : Subgroup G)
    {x : G} (hx : x ∈ starPreimage z v (starImage z v H)) :
    ∃ h ∈ H, ∃ c ∈ Gv v ⊓ centralizer (Uv z v : Set G), x = h * c := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, he⟩ := ha
  have hc : b⁻¹ * a ∈ (starMk z v).ker := by
    change starMk z v (b⁻¹ * a) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  rw [starMk_ker] at hc
  exact ⟨b, hb, (b : G)⁻¹ * a, ⟨(b⁻¹ * a).property, hc⟩, by simp⟩

theorem starPreimage_starImage_centralizes_seed_iff (z v : G)
    (H : Subgroup G) (hH : H ≤ Gv v) :
    starPreimage z v (starImage z v H) ≤ centralizer ({z} : Set G) ↔
      H ≤ centralizer ({z} : Set G) := by
  constructor
  · exact fun h => (le_starPreimage_starImage z v H hH).trans h
  · intro h x hx
    obtain ⟨k, hk, c, hc, rfl⟩ := starPreimage_starImage_factor z v H hx
    exact mul_mem (h hk) ((centralizer_le (show ({z} : Set G) ⊆ Uv z v from
      Set.singleton_subset_iff.mpr (z_mem_Uv z v))) hc.2)

theorem K_le_plusActor (K L T : Subgroup G) (v : G) : K ≤ plusActor K L T v :=
  (le_conjugateSpanBy K (Tv T v)).trans (le_sup_left.trans le_sup_left)

theorem plusImage_eq_bot_iff (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (H : Subgroup G) (hH : H ≤ plusActor K L T v) :
    plusImage K L T z v hL hz H = ⊥ ↔ H ≤ centralizer (WK K L T z v : Set G) := by
  rw [plusImage, Subgroup.map_eq_bot_iff, plusMk_ker]
  constructor
  · intro h x hx
    exact h (show (⟨x, hH hx⟩ : plusActor K L T v) ∈ H.subgroupOf _ from hx)
  · intro h x hx
    exact h hx

theorem plusImage_ne_bot_of_mem_Yz (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v) :
    plusImage K L T z v hL hz K ≠ ⊥ := by
  intro hb
  have hc := (plusImage_eq_bot_iff K L T z v hL hz K (K_le_plusActor K L T v)).mp hb
  have hN : Tv T v ≤ normalizer (centralizer (WK K L T z v : Set G) : Set G) := by
    have hn := plusActor_normalizes_WK K L T z v hL hz
    exact (le_sup_right.trans hn).trans
      ((normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (inferInstance : ((centralizer (WK K L T z v : Set G)).subgroupOf
          (normalizer (WK K L T z v : Set G))).Normal))
  have hcminus : Kminus K T v ≤ centralizer (WK K L T z v : Set G) :=
    conjugateSpanBy_le hc hN
  have hseed : Kminus K T v ≤ centralizer ({z} : Set G) :=
    hcminus.trans (centralizer_le (Set.singleton_subset_iff.mpr
      (le_conjugateSpanBy (zpowers z) (Kminus K T v ⊔ Lv L v) (mem_zpowers z))))
  have hm := hK.2.2.2
  rw [← starImage_Kminus K T z v hK.1.1] at hm
  exact hm ((starPreimage_starImage_centralizes_seed_iff z v (Kminus K T v)
    (Kminus_le_Gv K T v hK.1.1)).mpr hseed)


theorem starImage_sup (z v : G) (H D : Subgroup G) (hH : H ≤ Gv v) (hD : D ≤ Gv v) :
    starImage z v (H ⊔ D) = starImage z v H ⊔ starImage z v D := by
  unfold starImage
  rw [subgroupOf_sup hH hD, Subgroup.map_sup]

theorem starImageMap_subgroup (z v : G) (H D : Subgroup G)
    (hD : D ≤ Gv v) (hHD : H ≤ D) :
    (H.subgroupOf D).map (starImageMap z v D hD) =
      (starImage z v H).subgroupOf (starImage z v D) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_map.mpr ⟨⟨y, hD y.property⟩, hy, rfl⟩
  · intro hx
    obtain ⟨y, hy, he⟩ := hx
    exact mem_map.mpr ⟨⟨y, hHD hy⟩, hy, Subtype.ext he⟩

theorem starImage_Kminus_normal_in_actor (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) :
    ((starImage z v (Kminus K T v)).subgroupOf
      (starImage z v (plusActor K L T v))).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    (map_mono (comap_mono (show Kminus K T v ≤ plusActor K L T v from
      le_sup_left.trans le_sup_left)))).mpr
  change starImage z v (plusActor K L T v) ≤
    normalizer (starImage z v (Kminus K T v) : Set _)
  have hnorm := hK.2.2.1.1
  rw [← starImage_Kminus K T z v hK.1.1] at hnorm
  rw [plusActor, starImage_sup z v (Kminus K T v ⊔ Lv L v) (Tv T v)
    (sup_le (Kminus_le_Gv K T v hK.1.1) (Lv_le_Gv L v)) inf_le_right,
    starImage_sup z v (Kminus K T v) (Lv L v) (Kminus_le_Gv K T v hK.1.1) (Lv_le_Gv L v)]
  exact sup_le (sup_le (starImage z v (Kminus K T v)).le_normalizer
    (le_sup_left.trans hnorm)) (le_sup_right.trans hnorm)

/-- The local C-component condition supplies subnormality before any claim
that T_v fixes K. -/
theorem starImage_K_subnormal_in_Kminus (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) :
    ((starImage z v K).subgroupOf (starImage z v (Kminus K T v))).IsSubnormal := by
  have hJ : K ⊔ Tv T v ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hs := hK.1.2.1.subnormal.map
    (starImageMap_surjective z v (K ⊔ Tv T v) hJ)
  rw [starImageMap_subgroup z v K (K ⊔ Tv T v) hJ le_sup_left] at hs
  have hnJ : Kminus K T v ≤ K ⊔ Tv T v :=
    conjugateSpanBy_le le_sup_left (le_sup_right.trans (K ⊔ Tv T v).le_normalizer)
  exact hs.comap (inclusion (map_mono (comap_mono hnJ)))

theorem starImage_K_subnormal_in_actor (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v) :
    ((starImage z v K).subgroupOf (starImage z v (plusActor K L T v))).IsSubnormal := by
  let A := starImage z v (plusActor K L T v)
  let N := starImage z v (Kminus K T v)
  let H := starImage z v K
  have hNA : N ≤ A := map_mono (comap_mono (le_sup_left.trans le_sup_left))
  have hHN : H ≤ N := map_mono (comap_mono (le_conjugateSpanBy K (Tv T v)))
  have hn := starImage_Kminus_normal_in_actor K L T z v hK
  have hs := starImage_K_subnormal_in_Kminus K L T z v hK
  apply Subgroup.IsSubnormal.trans (comap_mono hHN) ?_ hn.isSubnormal
  exact hs.comap (subgroupOfEquivOfLe hNA).toMonoidHom


/-- The comparison map sends the literal star image to the literal plus image. -/
theorem starToPlus_image (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (H : Subgroup G)
    (hH : H ≤ plusActor K L T v) :
    ((starImage z v H).subgroupOf (starImage z v (plusActor K L T v))).map
      (starToPlus K L T z v hK hL hz) = plusImage K L T z v hL hz H := by
  rw [← starImageMap_subgroup z v H (plusActor K L T v)
    (plusActor_le_Gv K L T v hK) hH, map_map]
  have he : (starToPlus K L T z v hK hL hz).comp
      (starImageMap z v (plusActor K L T v) (plusActor_le_Gv K L T v hK)) =
        plusMk K L T z v hL hz := by
    ext x
    exact starToPlus_mk K L T z v hK hL hz x
  rw [he]
  rfl

theorem plusImage_K_subnormal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v) :
    (plusImage K L T z v hL hz K).IsSubnormal := by
  have hs := (starImage_K_subnormal_in_actor K L T z v hK).map
    (starToPlus_surjective K L T z v hK.1.1 hL hz)
  rwa [starToPlus_image K L T z v hK.1.1 hL hz K (K_le_plusActor K L T v)] at hs

/-- Restriction of the actual star-to-plus map to K*. -/
noncomputable def componentStarToPlus (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    starImage z v K →* plusImage K L T z v hL hz K :=
  ((starToPlus K L T z v hK hL hz).comp
    (inclusion (map_mono (comap_mono (K_le_plusActor K L T v))))).codRestrict
    (plusImage K L T z v hL hz K) (by
      intro x
      rw [← starToPlus_image K L T z v hK hL hz K (K_le_plusActor K L T v)]
      exact mem_map.mpr ⟨⟨x, map_mono (comap_mono (K_le_plusActor K L T v)) x.property⟩,
        x.property, rfl⟩)

theorem componentStarToPlus_surjective (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (componentStarToPlus K L T z v hK hL hz) := by
  intro x
  have hx : (x : Gplus K L T z v hL hz) ∈
      ((starImage z v K).subgroupOf (starImage z v (plusActor K L T v))).map
        (starToPlus K L T z v hK hL hz) := by
    simpa only [starToPlus_image K L T z v hK hL hz K (K_le_plusActor K L T v)]
      using x.property
  obtain ⟨y, hy, he⟩ := hx
  exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- Compatibility with representatives in the original component. -/
theorem componentStarToPlus_mk (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (k : K) :
    (componentStarToPlus K L T z v hK hL hz (starImageMap z v K hK k) :
      Gplus K L T z v hL hz) =
        plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) := by
  exact starToPlus_mk K L T z v hK hL hz (inclusion (K_le_plusActor K L T v) k)

/-- The component comparison kernel is precisely the star image of C_K(W_K). -/
theorem componentStarToPlus_ker (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (componentStarToPlus K L T z v hK hL hz).ker =
      ((centralizer (WK K L T z v : Set G)).subgroupOf K).map (starImageMap z v K hK) := by
  have he : ((componentStarToPlus K L T z v hK hL hz).comp
      (starImageMap z v K hK)).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf K := by
    ext x
    change componentStarToPlus K L T z v hK hL hz (starImageMap z v K hK x) = 1 ↔ _
    rw [Subtype.ext_iff, componentStarToPlus_mk]
    change inclusion (K_le_plusActor K L T v) x ∈ (plusMk K L T z v hL hz).ker ↔ _
    rw [plusMk_ker]
    rfl
  rw [← he, ← MonoidHom.comap_ker,
    map_comap_eq_self_of_surjective (starImageMap_surjective z v K hK)]

/-- The R₂ condition on W_K kills the two-core of the component star image.
Subnormality is derived from the local family, not assumed as invariance of K. -/
theorem componentStarToPlus_twoCore_le_ker [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    pCore 2 (starImage z v K) ≤ (componentStarToPlus K L T z v hK.1.1 hL hz).ker := by
  let f := componentStarToPlus K L T z v hK.1.1 hL hz
  have he : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK),
      hR]
    change (plusImage K L T z v hL hz K).subtype.ker = ⊥
    exact (MonoidHom.ker_eq_bot_iff _).mpr (plusImage K L T z v hL hz K).subtype_injective
  have hmap : (pCore 2 (starImage z v K)).map f ≤
      pCore 2 (plusImage K L T z v hL hz K) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f
      (componentStarToPlus_surjective K L T z v hK.1.1 hL hz),
      pCore_isPGroup.map f⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hmap.trans he.le))

/-- The literal quotient K*/O₂(K*) maps onto K+. -/
noncomputable def componentCoreQuotientToPlus [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    (starImage z v K ⧸ pCore 2 (starImage z v K)) →* plusImage K L T z v hL hz K :=
  QuotientGroup.lift _ (componentStarToPlus K L T z v hK.1.1 hL hz)
    (componentStarToPlus_twoCore_le_ker K L T z v hL hz hK hR)

theorem componentCoreQuotientToPlus_surjective [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    Function.Surjective (componentCoreQuotientToPlus K L T z v hL hz hK hR) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (componentStarToPlus_surjective K L T z v hK.1.1 hL hz) _

/-- The quasisimplicity assertion preceding 13.6.14 from the R₂ output of B.2.14. -/
theorem plusImage_K_quasisimple [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    Theory.GroupTheory.IsQuasisimple (plusImage K L T z v hL hz K) := by
  let := hK.2.1
  have : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  exact Theory.GroupTheory.IsQuasisimple.of_surjective
    (componentCoreQuotientToPlus K L T z v hL hz hK hR)
    (componentCoreQuotientToPlus_surjective K L T z v hL hz hK hR)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
