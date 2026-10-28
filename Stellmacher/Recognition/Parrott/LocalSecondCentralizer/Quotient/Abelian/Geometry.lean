module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.FixedRoot
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Pair normalizers above the second-transfer quotient

Write Y for the original Sylow image in G and Z for its center, also mapped
into G. The inverse image of the centralizer of an involution k⟨v⟩ is the
normalizer of ⟨k,v⟩. This module retains that pair and the actual embedding
of L, and identifies the image of Z with the specified central four-group.

Source: Parrott (1972), Lemma 8, printed p.683, observation (ii).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- The actual order-128 Sylow image, called Y in the source. -/
@[expose] public noncomputable def sylowImage : Subgroup G :=
  (t.S : Subgroup t.L).map t.embedding

/-- The center of Y, with its original inclusion in G. -/
@[expose] public noncomputable def sylowCenter : Subgroup G :=
  (center t.sylowImage).map t.sylowImage.subtype

/-- The relative normalizer N_Y(⟨k,v⟩), as a subgroup of G. -/
@[expose] public noncomputable def pairNormalizer (k : G) : Subgroup G :=
  t.sylowImage ⊓ normalizer ((zpowers k ⊔ zpowers n.v : Subgroup G) : Set G)

public theorem sylowImage_card [Finite G] : Nat.card t.sylowImage = 128 := by
  change Nat.card ((t.S : Subgroup t.L).map
    ((centralizer ({n.v} : Set G)).subtype.comp
      (t.M.subtype.comp t.L.subtype))) = 128
  rw [t.S_image]
  exact t.Y_card

public theorem sylowCenter_eq_omega_center :
    t.sylowCenter =
      (center (omega₁ (pCore 2 (normalizer (d.F : Set G))) (p := 2))).map
        (((normalizer (d.F : Set G)).subtype.comp
          (pCore 2 (normalizer (d.F : Set G))).subtype).comp
            (omega₁ (pCore 2 (normalizer (d.F : Set G))) (p := 2)).subtype) := by
  exact (congrArg (fun A : Subgroup G => (center A).map A.subtype)
    t.S_image).trans t.Y_center

public theorem sylowCenter_eq_coreCenter_sup_line :
    t.sylowCenter =
      (center (pCore 2 (normalizer (d.F : Set G)))).map
        ((normalizer (d.F : Set G)).subtype.comp
          (pCore 2 (normalizer (d.F : Set G))).subtype) ⊔ zpowers n.v := by
  rw [t.sylowCenter_eq_omega_center, n.omega_center_eq, n.core_center_eq]

public theorem sylowCenter_card [Finite G] : Nat.card t.sylowCenter = 8 := by
  rw [t.sylowCenter_eq_omega_center]
  exact n.ambient_omega_center_card

public theorem sylowCenter_le_sylowImage : t.sylowCenter ≤ t.sylowImage :=
  map_subtype_le _

public theorem sylowCenter_le_centralizer :
    t.sylowCenter ≤ centralizer (t.sylowImage : Set G) := by
  rintro a ⟨aY, ha, rfl⟩ b hb
  exact congrArg t.sylowImage.subtype (mem_center_iff.mp ha ⟨b, hb⟩)

public theorem sylowCenter_le_elementary : t.sylowCenter ≤ d.F := by
  rw [t.sylowCenter_eq_omega_center]
  exact n.omega_center_le_inf.trans inf_le_right

public theorem v_mem_sylowCenter : n.v ∈ t.sylowCenter := by
  rw [t.sylowCenter_eq_coreCenter_sup_line]
  exact mem_sup_right (mem_zpowers n.v)

public theorem sylowCenter_quotient_image :
    (t.sylowCenter.comap t.embedding).map (QuotientGroup.mk' (zpowers t.v)) =
      t.quotientCoreCenter := by
  let ZK := (center (pCore 2 (normalizer (d.F : Set G)))).map
    ((normalizer (d.F : Set G)).subtype.comp
      (pCore 2 (normalizer (d.F : Set G))).subtype)
  have hZY : ZK ≤ t.sylowImage := by
    intro a ha
    exact t.elementary_le_sylow_image
      (n.omega_center_le_inf (n.core_center_le_omega_center ha)).2
  have hZR := hZY.trans (map_le_range t.embedding _)
  have hZCR := t.sylowCenter_le_sylowImage.trans (map_le_range t.embedding _)
  have he : t.sylowCenter.comap t.embedding = ZK.comap t.embedding ⊔ zpowers t.v := by
    apply map_injective t.embedding_injective
    rw [map_comap_eq_self hZCR, Subgroup.map_sup, map_comap_eq_self hZR,
      MonoidHom.map_zpowers, t.v_image]
    exact t.sylowCenter_eq_coreCenter_sup_line
  rw [he, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hv : QuotientGroup.mk' (zpowers t.v) t.v = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (mem_zpowers t.v)
  rw [hv, zpowers_one_eq_bot, sup_bot_eq]
  rfl

/-- A lift of a quotient point outside the central four-group lies outside Z(Y). -/
public theorem lift_not_mem_sylowCenter {k : t.L}
    (hk : QuotientGroup.mk' (zpowers t.v) k ∉ t.quotientCoreCenter) :
    t.embedding k ∉ t.sylowCenter := by
  intro he
  apply hk
  rw [← t.sylowCenter_quotient_image]
  exact mem_map_of_mem (QuotientGroup.mk' (zpowers t.v)) he

/-- Pulling back an involution centralizer gives the literal pair normalizer. -/
public theorem localCentralizer_preimage_map [Finite G] {k : t.L}
    (hk2 : orderOf (QuotientGroup.mk' (zpowers t.v) k) = 2) :
    ((t.quotientLocalCentralizer (QuotientGroup.mk' (zpowers t.v) k)).comap
      (QuotientGroup.mk' (zpowers t.v))).map t.embedding =
        t.pairNormalizer (t.embedding k) := by
  let q := QuotientGroup.mk' (zpowers t.v)
  let P := zpowers k ⊔ zpowers t.v
  have hkerS : q.ker ≤ (t.S : Subgroup t.L) := by
    rw [QuotientGroup.ker_mk']
    apply zpowers_le.mpr
    obtain ⟨a, ha, he⟩ := t.elementary_le_sylow_image n.v_mem_inf.2
    have he' : a = t.v := t.embedding_injective (he.trans t.v_image.symm)
    exact he' ▸ ha
  have hpre : (centralizer ({q k} : Set t.Quotient)).comap q = normalizer (P : Set t.L) := by
    rw [← normalizer_zpowers_eq_centralizer_of_order_two (q k) hk2,
      comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
      ← MonoidHom.map_zpowers q k, comap_map_eq, QuotientGroup.ker_mk']
  have hpair : P.map t.embedding = zpowers (t.embedding k) ⊔ zpowers n.v := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, t.v_image]
  have hn : (normalizer (P.map t.embedding : Set G)).comap t.embedding =
      normalizer (P : Set t.L) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective t.embedding_injective]
  change (((t.S : Subgroup t.L).map q ⊓ centralizer ({q k} : Set t.Quotient)).comap q).map
    t.embedding = _
  rw [comap_inf, comap_map_eq_self hkerS, hpre]
  apply le_antisymm
  · rintro a ⟨b, hb, rfl⟩
    refine ⟨mem_map_of_mem t.embedding hb.1, ?_⟩
    change t.embedding b ∈ normalizer ((zpowers (t.embedding k) ⊔ zpowers n.v : Subgroup G) : Set G)
    rw [← hpair]
    exact show b ∈ (normalizer (P.map t.embedding : Set G)).comap t.embedding from hn.symm ▸ hb.2
  · rintro a ⟨⟨b, hb, rfl⟩, ha⟩
    refine ⟨b, ⟨hb, ?_⟩, rfl⟩
    rw [← hn]
    change t.embedding b ∈ normalizer (P.map t.embedding : Set G)
    rwa [hpair]

end Stellmacher.Recognition.ParrottSecondTransferData
