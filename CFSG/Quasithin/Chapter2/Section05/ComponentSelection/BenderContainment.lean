module

public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.BenderSylow
public import Theory.GroupTheory.ComponentSaturatedSylow

/-!
# Bender component intersections without normality

The component stabilizer controls its coordinate projection. Its orbit
under H_U is a two-group because distinct components commute, and source
saturation puts the entire orbit in O2(H_U). A nontrivial inner marker
therefore gives a nontrivial component intersection; the full Bender model
Sylow theorem identifies its unique Sylow overgroup. Its orbit is again a
two-group, so saturation forces the intersection to be that Sylow subgroup.

Source: Aschbacher--Smith 2.5.3(3), printed p.552. The original marker
is supplied separately by the earlier source construction.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M H U HU : Subgroup G}

/-- Component permutation is allowed: the actor only stabilizes the
coordinate subgroup through its component stabilizer. -/
theorem bender_component_sylow_intersection_of_inner
    (hpair : (U, HU) ∈ localPairsIn (Chapter1.He G) M H)
    (hsat : ∀ P : Subgroup G, P ≤ H → IsPGroup 2 P →
      HU ≤ normalizer (P : Set G) → P ≤ twoCore HU)
    (D : Subgroup H) (hD : IsComponent H D)
    (hm : ClassificationModels.IsBenderModel D)
    (z : H) (hz : (z : G) ∈ twoCore HU)
    (hinner : z ∈ D ⊔ centralizer (D : Set H))
    (hnoncentral : z ∉ centralizer (D : Set H)) :
    ∃ P : Sylow 2 D, ((P : Subgroup D).map D.subtype).map H.subtype =
      D.map H.subtype ⊓ twoCore HU := by
  let A := HU.subgroupOf H
  let Q := (twoCore HU).subgroupOf H
  have hsatH : ∀ P : Subgroup H, IsPGroup 2 P →
      A ≤ normalizer (P : Set H) → P ≤ Q := by
    intro P hp hn x hx
    have hna : HU ≤ normalizer (P.map H.subtype : Set G) := by
      intro a ha
      exact P.le_normalizer_map H.subtype ⟨⟨a, hpair.2 ha⟩, hn ha, rfl⟩
    exact hsat _ (map_subtype_le P) (hp.map H.subtype) hna
      (mem_map_of_mem H.subtype hx)
  have hAQ : A ≤ normalizer (Q : Set H) := by
    intro a ha x
    exact le_normalizer_twoCore HU ha (x : G)
  have hQp : IsPGroup 2 Q := (isPGroup_pCoreIn 2 HU).comap_subtype
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  have hc := BenderFusion.OmegaNormalizerModels.centerless_of_bender_model hm
  have hZ : IsPGroup 2 (center D) := hc ▸ IsPGroup.of_bot
  obtain ⟨d, hd, hdc⟩ := hD.exists_noncentral_intersection_of_saturation hZ hQp hAQ hsatH
    hz hinner hnoncentral
  have hu : ∀ P R : Sylow 2 D, Q.subgroupOf D ≤ P → Q.subgroupOf D ≤ R → P = R := by
    intro P R hP hR
    apply bender_sylow_eq_of_inf_ne_bot hm P R
    intro hb
    have hd1 : (⟨d, hd.1⟩ : D) = 1 := mem_bot.mp (hb ▸
      (show (⟨d, hd.1⟩ : D) ∈ (P : Subgroup D) ⊓ (R : Subgroup D) from
        ⟨hP hd.2, hR hd.2⟩))
    have hdval : d = 1 := congrArg Subtype.val hd1
    exact hdc (hdval.symm ▸ (centralizer (D : Set H)).one_mem)
  obtain ⟨P, hP⟩ := hD.exists_sylow_eq_inf_of_saturation hQp hAQ hsatH hu
  refine ⟨P, ?_⟩
  rw [hP]
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨mem_map_of_mem H.subtype hd.1, hd.2⟩
  · rintro ⟨⟨d, hd, rfl⟩, hq⟩
    exact ⟨d, ⟨hd, hq⟩, rfl⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
