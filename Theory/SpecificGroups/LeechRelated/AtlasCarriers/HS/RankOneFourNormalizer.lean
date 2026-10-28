module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.RankOneFourNormalizer.Fixed

/-!
# Normal-four normalizer enlargement in the Higman–Sims group

For any finite group actually isomorphic to the fixed degree-100 HS carrier,
a normal elementary four-group in a Sylow two-subgroup has a strictly smaller
normalizer than a characteristic subgroup of that Sylow whose ambient
centralizer is a two-group.

Conjugate the supplied Sylow to the marked Sylow. The exhaustive elementary
catalogue identifies its four-group with `elementary 1`; the witness is the
characteristic eight `elementary 2`. Its four-group centralizer calculation
proves forward containment, and the full action on the eight proves reverse
noncontainment. Transport all five conclusions through the actual composed
equivalence. Normality and characteristicity are relative to the Sylow.

Sources: GLS3, Table 5.3m; Aschbacher–Smith, combined manuscript of 1 March
2004, the sporadic paragraph of 15.3.43, printed p.1140; 1.1.5(3)(f), p.502.
-/

namespace Sporadic.LeechRelated.HS.RankOneFourNormalizer
open Subgroup EvenLocalCandidates BlockNormalizer

private theorem characteristic_subgroupOf_map
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (Q T : Subgroup G) (hc : (Q.subgroupOf T).Characteristic) :
    ((Q.map e.toMonoidHom).subgroupOf (T.map e.toMonoidHom)).Characteristic := by
  let u := e.subgroupMap T
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, rfl⟩ := u.surjective x
  have hy : y ∈ Q.subgroupOf T :=
    (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hx
  have ha := characteristic_iff_le_comap.mp hc (MulAut.congr u.symm a) hy
  have htrans : u (MulAut.congr u.symm a y) = a (u y) := u.apply_symm_apply _
  change a (u y) ∈ (Q.map e.toMonoidHom).subgroupOf (T.map e.toMonoidHom)
  rw [← htrans]
  exact mem_map_of_mem e.toMonoidHom ha

private theorem map_centralizer {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (Q : Subgroup G) :
    (centralizer (Q : Set G)).map e.toMonoidHom =
      centralizer (Q.map e.toMonoidHom : Set H) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem enlargement_of_aligned_equiv
    {D : Type*} [Group D] [Finite D] (f : D ≃* Carrier) (T : Subgroup D)
    (hT : T.map f.toMonoidHom = subgroup) (W : Subgroup D) (hWT : W ≤ T)
    (hn : (W.subgroupOf T).Normal) (he : IsElementaryAbelian 2 W)
    (hc : Nat.card W = 4) :
    ∃ Q : Subgroup D, Q ≤ T ∧ (Q.subgroupOf T).Characteristic ∧
      IsPGroup 2 (centralizer (Q : Set D)) ∧
      normalizer (W : Set D) ≤ normalizer (Q : Set D) ∧
      ¬ normalizer (Q : Set D) ≤ normalizer (W : Set D) := by
  have hback : subgroup.map f.symm.toMonoidHom = T := by
    rw [← hT]
    simp [map_map]
  let W' := W.map f.toMonoidHom
  have hw' : W' ≤ subgroup := hT ▸ map_mono hWT
  have hn' : (W'.subgroupOf subgroup).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hw').mpr
    rw [← hT, ← map_normalizer_eq_of_bijective W f.bijective]
    exact map_mono ((normal_subgroupOf_iff_le_normalizer hWT).mp hn)
  let := he
  have he' : IsElementaryAbelian 2 W' := IsElementaryAbelian.map _
  have hc' : Nat.card W' = 4 := (card_map_of_injective f.injective).trans hc
  have hW' : W' = elementary 1 := normal_four_eq W' hw' hn' he' hc'
  have hWback : (elementary 1).map f.symm.toMonoidHom = W := by
    rw [← hW']
    simp [W', map_map]
  let Q := (elementary 2).map f.symm.toMonoidHom
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · exact hback ▸ map_mono (elementary_le_subgroup 2)
  · have h := characteristic_subgroupOf_map f.symm (elementary 2) subgroup
      baseElementary_characteristic
    rwa [hback] at h
  · have h := (large_elementary_centralizer_isPGroup 2 (by decide)).map f.symm.toMonoidHom
    rwa [map_centralizer] at h
  · have h := map_mono (f := f.symm.toMonoidHom) four_normalizer_le_eight_normalizer
    rwa [map_normalizer_eq_of_bijective _ f.symm.bijective,
      map_normalizer_eq_of_bijective _ f.symm.bijective, hWback] at h
  · intro h
    apply eight_normalizer_not_le_four_normalizer
    have hm := map_mono (f := f.toMonoidHom) h
    rw [map_normalizer_eq_of_bijective _ f.bijective,
      map_normalizer_eq_of_bijective _ f.bijective] at hm
    change normalizer (Q.map f.toMonoidHom : Set Carrier) ≤ normalizer (W' : Set Carrier) at hm
    rw [hW'] at hm
    have hQ : Q.map f.toMonoidHom = elementary 2 := by simp [Q, map_map]
    rwa [hQ] at hm

/-- The intrinsic HS normalizer enlargement, transported along the supplied
actual carrier equivalence and Sylow conjugacy. No model premises remain. -/
public theorem enlargement_of_equiv {D : Type*} [Group D] [Finite D]
    (e : D ≃* Carrier) (T : Sylow 2 D) (W : Subgroup D)
    (hWT : W ≤ (T : Subgroup D))
    (hn : (W.subgroupOf (T : Subgroup D)).Normal)
    (he : IsElementaryAbelian 2 W) (hc : Nat.card W = 4) :
    ∃ Q : Subgroup D, Q ≤ (T : Subgroup D) ∧
      (Q.subgroupOf (T : Subgroup D)).Characteristic ∧
      IsPGroup 2 (centralizer (Q : Set D)) ∧
      normalizer (W : Set D) ≤ normalizer (Q : Set D) ∧
      ¬ normalizer (Q : Set D) ≤ normalizer (W : Set D) := by
  let T' : Sylow 2 Carrier := T.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier T' baseSylow
  let f := e.trans (MulAut.conj g)
  have hT : (T : Subgroup D).map f.toMonoidHom = subgroup := by
    have h := congrArg (fun P : Sylow 2 Carrier => (P : Subgroup Carrier)) hg
    change ((T : Subgroup D).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = subgroup at h
    rw [map_map] at h
    exact h
  exact enlargement_of_aligned_equiv f T hT W hWT hn he hc

end Sporadic.LeechRelated.HS.RankOneFourNormalizer
