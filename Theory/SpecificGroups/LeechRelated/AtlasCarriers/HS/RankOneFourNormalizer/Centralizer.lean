module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.RankOneFourNormalizer.Certificates

/-!
# The HS four-group normalizer preserves the elementary eight

The four-group centralizer is a two-group normalized by the marked Sylow,
so is contained in that Sylow. Its normal elementary subgroups lie in the
marked elementary eight by the exhaustive rejection test. Since that eight
is itself normal in the centralizer, it is characteristic there. Normalizing
the four-group therefore normalizes the eight.

Sources: GLS3, Table 5.3m; Aschbacher–Smith, proof of 15.3.43, p.1140.
-/

namespace Sporadic.LeechRelated.HS.RankOneFourNormalizer
open Subgroup EvenLocalCandidates EvenLocalCandidates.SylowCatalogueData BlockNormalizer

private theorem elementary_mono {i j : Fin 3} (h : i ≤ j) : elementary i ≤ elementary j :=
  closure_mono (Set.image_mono (fun _ hk => hk.trans h))

/-- The marked four-group is normal in the marked Sylow subgroup. -/
public theorem sylow_le_four_normalizer : subgroup ≤ normalizer (elementary 1 : Set Carrier) := by
  change closure (Set.range sylowGenerator) ≤ _
  apply (closure_le _).mpr
  rintro g ⟨i, rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge
  · rw [elementary, MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro x ⟨y, ⟨j, hj, rfl⟩, rfl⟩
    change sylowGenerator i * elementaryGenerator j * (sylowGenerator i)⁻¹ ∈ elementary 1
    rw [baseSylow_conjugation]
    apply small_mem_elementary
    have ht : ∀ i j : Fin 3, j ≤ 1 →
        (![![1, 3, 4], ![1, 2, 7], ![1, 3, 4]] i j : Fin 8).val < 4 := by decide
    exact ht i j hj
  · exact le_of_eq (Nat.card_congr ((MulAut.conj (sylowGenerator i)).subgroupMap
      (elementary 1)).toEquiv)

/-- The full ambient four-group centralizer lies in the marked Sylow. -/
public theorem four_centralizer_le_sylow :
    centralizer (elementary 1 : Set Carrier) ≤ subgroup := by
  have hn := sylow_le_four_normalizer.trans (normalizer_le_normalizer_centralizer (elementary 1))
  have hp := baseSylow.isPGroup'.to_sup_of_normal_right'
    (large_elementary_centralizer_isPGroup 1 (by decide)) hn
  exact sup_eq_left.mp (baseSylow.is_maximal' hp le_sup_left)

private theorem eight_le_four_centralizer :
    elementary 2 ≤ centralizer (elementary 1 : Set Carrier) := by
  let := elementary_isElementaryAbelian 2
  intro x hx y hy
  exact setLike_mul_comm (elementary_mono (by decide : (1 : Fin 3) ≤ 2) hy) hx

/-- The elementary eight is characteristic inside the full ambient centralizer
of the four-group; normality is relative to this centralizer. -/
public theorem eight_characteristic_in_four_centralizer :
    ((elementary 2).subgroupOf (centralizer (elementary 1 : Set Carrier))).Characteristic := by
  let C := centralizer (elementary 1 : Set Carrier)
  let Q := (elementary 2).subgroupOf C
  let : IsElementaryAbelian 2 (elementary 2) := elementary_isElementaryAbelian 2
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.subgroupOf eight_le_four_centralizer
  let : Q.Normal := (normal_subgroupOf_iff_le_normalizer eight_le_four_centralizer).mpr
    (four_centralizer_le_sylow.trans baseSylow_le_normalizer)
  apply characteristic_iff_map_le.mpr
  intro φ
  let A := Q.map φ.toMonoidHom
  let : A.Normal := Subgroup.Normal.map inferInstance φ.toMonoidHom φ.surjective
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  intro x hx
  have hs : (x : Carrier) ^ 2 = 1 :=
    congrArg Subtype.val (elemPow_eq_one_of_isElementaryAbelian x (show x ∈ A from hx))
  obtain ⟨j, hj⟩ := small_of_centralizer_normal_element x
    (four_centralizer_le_sylow x.property) hs (by
      intro g hg
      have hm : (⟨g, hg⟩ : C) * x * (⟨g, hg⟩ : C)⁻¹ ∈ A :=
        Subgroup.Normal.conj_mem (inferInstance : A.Normal) x hx ⟨g, hg⟩
      exact congrArg Subtype.val (setLike_mul_comm (show x ∈ A from hx) hm))
  change (x : Carrier) ∈ elementary 2
  rw [← hj]
  exact small_mem_elementary j 2 j.isLt

/-- Exhaustive normalizer containment for the fixed degree-100 HS carrier. -/
public theorem four_normalizer_le_eight_normalizer :
    normalizer (elementary 1 : Set Carrier) ≤ normalizer (elementary 2 : Set Carrier) := by
  let := eight_characteristic_in_four_centralizer
  have h := normalizer_le_normalizer_characteristic_image
    (centralizer (elementary 1 : Set Carrier))
    ((elementary 2).subgroupOf (centralizer (elementary 1 : Set Carrier)))
  rw [map_subgroupOf_eq_of_le eight_le_four_centralizer] at h
  exact (normalizer_le_normalizer_centralizer (elementary 1)).trans h

end Sporadic.LeechRelated.HS.RankOneFourNormalizer
