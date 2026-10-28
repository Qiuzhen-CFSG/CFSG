module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RankOneFourNormalizer.Centralizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Sylow

/-!
# The normal-four normalizer witness in the actual Hall–Janko carrier

The unique normal elementary four-group in the fixed Sylow is the embedded
center of Seed.q₂. Its full normalizer lies in N(q₂), whose order is 1152,
and C(q₂) is that same four-group. The radical q₂ is characteristic in the
fixed Sylow. These facts provide the enlargement used in the sporadic
inspection of Aschbacher–Smith 15.3.43, printed p.1140; see also 1.1.5(3)(f),
printed p.502, and GLS3 Table 5.3g.

For an arbitrary finite realization, Sylow conjugacy after the supplied
multiplicative equivalence carries the input Sylow to Seed.s. Pulling back
q₂ through this actual equivalence preserves relative characteristicity,
the centralizer bound, normalizer containment and normalizer order. No model
premises, automorphism classification or simplicity calculation are assumed.
The fixed Sylow uses SecondParabolic.sylow and the proved first-local order.
-/

public section
namespace Sporadic.LeechRelated.J2.RankOneFourNormalizer
open Theory.GroupTheory Subgroup ExceptionalParabolics Seed PairNormalizer

private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (H : Subgroup A) (hH : H.Characteristic) :
    (H.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  refine ⟨b y, (characteristic_iff_le_comap.mp hH b) hy, ?_⟩
  exact e.apply_symm_apply _

private theorem relative_characteristic_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (Q S : Subgroup A) (h : (Q.subgroupOf S).Characteristic) :
    ((Q.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)).Characteristic := by
  let f := e.subgroupMap S
  have hm : (Q.subgroupOf S).map f.toMonoidHom =
      (Q.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom) := by
    ext x
    simp only [mem_map_equiv, mem_subgroupOf]
    change e.symm (x : B) ∈ Q ↔ (x : B) ∈ Q.map e.toMonoidHom
    exact mem_map_equiv.symm
  rw [← hm]
  exact characteristic_map_equiv f _ h

/-- The radical centralizer is exactly the four-group identified by the Sylow calculation. -/
theorem centralizer_eq_four : centralizer (q₂ : Set Carrier) = four := by
  apply le_antisymm
  · intro x hx
    refine ⟨⟨x, centralizer_le_q₂ hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hx y y.property)
  · rintro _ ⟨x, hx, rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)

/-- The fixed radical has centralizer of order four in the original ATLAS carrier. -/
theorem card_centralizer_q₂ : Nat.card (centralizer (q₂ : Set Carrier)) = 4 := by
  rw [centralizer_eq_four, card_four]

/-- Every normal elementary four-group in any Sylow of a group actually isomorphic to J₂
has the intrinsic characteristic normalizer enlargement, with no additional model premises. -/
theorem enlargement_of_equiv {D : Type*} [Group D] [Finite D]
    (e : D ≃* Carrier) (T : Sylow 2 D) (W : Subgroup D)
    (hWT : W ≤ (T : Subgroup D))
    (hWn : (W.subgroupOf (T : Subgroup D)).Normal)
    (hWe : IsElementaryAbelian 2 W) (hW4 : Nat.card W = 4) :
    ∃ Q : Subgroup D, Q ≤ (T : Subgroup D) ∧
      (Q.subgroupOf (T : Subgroup D)).Characteristic ∧
      IsPGroup 2 (centralizer (Q : Set D)) ∧
      normalizer (W : Set D) ≤ normalizer (Q : Set D) ∧
      9 ∣ Nat.card (normalizer (Q : Set D)) := by
  let T' : Sylow 2 Carrier := T.mapSurjective (f := e.toMonoidHom) e.surjective
  let U : Sylow 2 Carrier := SecondParabolic.sylow FirstParabolic.card_l₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier T' U
  let f : D ≃* Carrier := e.trans (MulAut.conj g)
  have hT : (T : Subgroup D).map f.toMonoidHom = s := by
    have hh := congrArg (fun P : Sylow 2 Carrier => (P : Subgroup Carrier)) hg
    change ((T : Subgroup D).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = s at hh
    simpa only [map_map, f, MulEquiv.toMonoidHom_eq_coe, MulEquiv.coe_monoidHom_trans] using hh
  let W' := W.map f.toMonoidHom
  have hWs : W' ≤ s := hT ▸ map_mono hWT
  have hWn' : (W'.subgroupOf s).Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [← hT]
    exact (map_mono ((normal_subgroupOf_iff_le_normalizer hWT).mp hWn)).trans
      (W.le_normalizer_map f.toMonoidHom)
  let := hWe
  have hWe' : IsElementaryAbelian 2 W' := IsElementaryAbelian.map f.toMonoidHom
  have hW4' : Nat.card W' = 4 := (card_map_of_injective f.injective).trans hW4
  have hn : normalizer (W' : Set Carrier) ≤ p₂ :=
    normal_four_normalizer_le W' hWs hWn' hWe' hW4'
  let Q := q₂.map f.symm.toMonoidHom
  have hback : s.map f.symm.toMonoidHom = (T : Subgroup D) := by
    rw [← hT]
    simp [map_map]
  have hQT : Q ≤ (T : Subgroup D) := by
    rw [← hback]
    exact map_mono q₂_le_s
  have hchar : (Q.subgroupOf (T : Subgroup D)).Characteristic := by
    rw [← hback]
    exact relative_characteristic_map f.symm q₂ s q₂_characteristic
  have hQmap : Q.map f.toMonoidHom = q₂ := by
    simp [Q, map_map]
  have hc : centralizer (Q : Set D) ≤ Q := by
    intro x hx
    have hfx : f x ∈ centralizer (q₂ : Set Carrier) := by
      rw [← hQmap]
      exact map_centralizer_le_centralizer_image (Q : Set D) f.toMonoidHom
        (mem_map_of_mem _ hx)
    have hmem := centralizer_le_q₂ hfx
    exact ⟨f x, hmem, f.symm_apply_apply x⟩
  refine ⟨Q, hQT, hchar,
    (q₂_isPGroup.map f.symm.toMonoidHom).of_injective (Subgroup.inclusion hc)
      (Subgroup.inclusion_injective hc), ?_, ?_⟩
  · apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq, hQmap]
    exact hn
  · have hcard : Nat.card (normalizer (Q : Set D)) = 1152 := by
      rw [← card_map_of_injective (f := f.toMonoidHom) f.injective, map_equiv_normalizer_eq, hQmap]
      exact card_p₂
    rw [hcard]
    decide

end Sporadic.LeechRelated.J2.RankOneFourNormalizer
