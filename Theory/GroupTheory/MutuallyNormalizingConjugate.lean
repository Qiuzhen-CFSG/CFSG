module
public import Theory.GroupTheory.ConjugatePairInternalLift
public import Mathlib.GroupTheory.Nilpotent
/-!
# Mutually normalizing conjugates of a finite p-subgroup

If a p-subgroup is not weakly closed in its normalizer, it has a distinct
conjugate which normalizes it and is normalized by it. Start with a
conjugate in the normalizer. Their join is a p-group. If mutual
normalization fails, the normalizer condition inside this join gives a
second conjugate with both inclusions; transport this pair back to the
original subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.13, printed pp.22–23. The original Chapter 13 core is an actual
consumer of the theorem.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem nonnormal_pair [Group.IsNilpotent G] (X : Subgroup G)
    (hx : normalizer (X : Set G) ≠ ⊤) :
    ∃ a : G, X.conjBy a ≠ X ∧
      X.conjBy a ≤ normalizer (X : Set G) ∧
      X ≤ normalizer (X.conjBy a : Set G) := by
  let N := normalizer (X : Set G)
  obtain ⟨a, ha, han⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent N (lt_top_iff_ne_top.mpr hx))
  have hfix : N.conjBy a = N := mem_normalizer_iff_map_conj_eq.mp ha
  have hxn : X.conjBy a ≤ N := (map_mono X.le_normalizer).trans_eq hfix
  have hnx : N ≤ normalizer (X.conjBy a : Set G) := by
    change N ≤ normalizer (X.map (MulAut.conj a).toMonoidHom : Set G)
    rw [← map_equiv_normalizer_eq X (MulAut.conj a)]
    exact hfix.ge
  exact ⟨a, fun he => han (mem_normalizer_iff_map_conj_eq.mpr he), hxn,
    X.le_normalizer.trans hnx⟩

/-- A p-subgroup which is not weakly closed in its normalizer has a distinct
mutually normalizing conjugate. -/
theorem exists_mutually_normalizing_conjugate {p : ℕ} [Fact p.Prime]
    (X : Subgroup G) (hp : IsPGroup p X)
    (hweak : ∃ a : G, X.conjBy a ≤ normalizer (X : Set G) ∧ X.conjBy a ≠ X) :
    ∃ a : G, X.conjBy a ≠ X ∧
      X.conjBy a ≤ normalizer (X : Set G) ∧
      X ≤ normalizer (X.conjBy a : Set G) := by
  obtain ⟨a, ha, hne⟩ := hweak
  let Y := X.conjBy a
  let P := X ⊔ Y
  have hP : IsPGroup p P := hp.to_sup_of_normal_left'
    (hp.map (MulAut.conj a).toMonoidHom) ha
  have hYP : Y ≤ P := le_sup_right
  by_cases hnormal : P ≤ normalizer (Y : Set G)
  · exact ⟨a,hne,ha,le_sup_left.trans hnormal⟩
  have hnot : normalizer (Y.subgroupOf P : Set P) ≠ ⊤ := by
    rw [← subgroupOf_normalizer_eq hYP]
    exact fun he => hnormal (subgroupOf_eq_top.mp he)
  let : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨b,hb,hbY,hYb⟩ := nonnormal_pair (Y.subgroupOf P) hnot
  have hback : (Y.subgroupOf P).map P.subtype = Y := map_subgroupOf_eq_of_le hYP
  have hneq : Y.conjBy b.val ≠ Y := by
    intro he
    apply hb
    apply map_injective P.subtype_injective
    rw [map_conjBy_hom,hback]
    exact he
  have hbY' : Y.conjBy b.val ≤ normalizer (Y : Set G) := by
    have hm := map_mono (f := P.subtype) hbY
    rw [map_conjBy_hom,hback,←subgroupOf_normalizer_eq hYP,subgroupOf_map_subtype] at hm
    exact hm.trans inf_le_left
  have hYb' : Y ≤ normalizer (Y.conjBy b.val : Set G) := by
    have hm := map_mono (f := P.subtype) hYb
    rw [hback] at hm
    have hn := ((Y.subgroupOf P).conjBy b).le_normalizer_map P.subtype
    rw [map_conjBy_hom,hback] at hn
    exact hm.trans hn
  let c := a⁻¹ * b.val * a
  have htrans : (Y.conjBy b.val).conjBy a⁻¹ = X.conjBy c := by
    dsimp [Y,c]
    rw [conjBy_conjBy,conjBy_conjBy,mul_assoc]
  have hcancel : Y.conjBy a⁻¹ = X := conjBy_inv X a
  refine ⟨c, ?_, ?_, ?_⟩
  · intro he
    apply hneq
    apply map_injective (f := (MulAut.conj a⁻¹).toMonoidHom) (MulAut.conj a⁻¹).injective
    exact htrans.trans (he.trans hcancel.symm)
  · have hm := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hbY'
    rw [map_equiv_normalizer_eq] at hm
    change (Y.conjBy b.val).conjBy a⁻¹ ≤ normalizer (Y.conjBy a⁻¹ : Set G) at hm
    rwa [htrans,hcancel] at hm
  · have hm := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hYb'
    rw [map_equiv_normalizer_eq] at hm
    change Y.conjBy a⁻¹ ≤ normalizer ((Y.conjBy b.val).conjBy a⁻¹ : Set G) at hm
    rwa [htrans,hcancel] at hm
end Subgroup
