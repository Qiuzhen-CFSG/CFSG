module
public import Theory.GroupTheory.IndexTwoConjugateJoin
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Intersections and commutators of an index-two conjugate pair

If an index-two subgroup D of S normalizes A, the S-conjugates of A are
A and its conjugate by any s outside D. Elements of D fix both, while the
other coset exchanges them. Their intersection and commutator are therefore
normalized by S. The calculation uses the actual ambient conjugation maps.

Source: the elementary index-two calculation used in Aschbacher--Smith,
12.6.4 and 12.6.12, printed pp.824--826.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- An index-two action preserves the intersection and commutator of the two conjugates. -/
theorem le_normalizer_inf_and_commutator_conjugate_of_relIndex_two
    (A D S : Subgroup G) (hD : D ≤ S) (hi : D.relIndex S = 2)
    (hn : D ≤ normalizer (A : Set G)) (s : G) (hs : s ∈ S) (hsD : s ∉ D) :
    let F := A.map (MulAut.conj s).toMonoidHom
    S ≤ normalizer ((A ⊓ F : Subgroup G) : Set G) ⊓
      normalizer ((⁅A,F⁆ : Subgroup G) : Set G) := by
  let F := A.map (MulAut.conj s).toMonoidHom
  have hDn : S ≤ normalizer (D : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hD).mp (normal_of_index_eq_two hi)
  have hDF : D ≤ normalizer (F : Set G) := by
    rw [show F = A.map (MulAut.conj s).toMonoidHom from rfl,
      ←map_equiv_normalizer_eq A (MulAut.conj s)]
    have hm := map_mono (f := (MulAut.conj s).toMonoidHom) hn
    have heq : D.map (MulAut.conj s).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp (hDn hs)
    rwa [heq] at hm
  have hDN : D ≤ normalizer ((A ⊓ F : Subgroup G) : Set G) ⊓
      normalizer ((⁅A,F⁆ : Subgroup G) : Set G) := by
    intro t ht
    have hA := mem_normalizer_iff_map_conj_eq.mp (hn ht)
    have hF := mem_normalizer_iff_map_conj_eq.mp (hDF ht)
    constructor
    · apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_inf _ _ _ (MulAut.conj t).injective,hA,hF]
    · apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_commutator,hA,hF]
  have hsq : s * s ∈ D := (D.subgroupOf S).mul_self_mem_of_index_two hi ⟨s,hs⟩
  have hFF : F.map (MulAut.conj s).toMonoidHom = A := by
    change (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s).toMonoidHom = A
    rw [map_map]
    have he : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (s*s)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
        mul_inv_rev,mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (hn hsq)
  have hsN : s ∈ normalizer ((A ⊓ F : Subgroup G) : Set G) ⊓
      normalizer ((⁅A,F⁆ : Subgroup G) : Set G) := by
    constructor
    · apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_inf _ _ _ (MulAut.conj s).injective]
      change F ⊓ F.map (MulAut.conj s).toMonoidHom = A ⊓ F
      rw [hFF,inf_comm]
    · apply mem_normalizer_iff_map_conj_eq.mpr
      rw [map_commutator]
      change ⁅F,F.map (MulAut.conj s).toMonoidHom⁆ = ⁅A,F⁆
      rw [hFF,commutator_comm]
  change S ≤ normalizer ((A ⊓ F : Subgroup G) : Set G) ⊓
    normalizer ((⁅A,F⁆ : Subgroup G) : Set G)
  intro t ht
  by_cases htD : t ∈ D
  · exact hDN htD
  · have hts : t * s⁻¹ ∈ D :=
      ((D.subgroupOf S).mul_mem_iff_of_index_two hi).mpr
        (show ((⟨t,ht⟩ : S) ∈ D.subgroupOf S ↔
          (⟨s⁻¹,S.inv_mem hs⟩ : S) ∈ D.subgroupOf S) from by
          change t ∈ D ↔ s⁻¹ ∈ D
          simp only [inv_mem_iff,htD,hsD])
    simpa only [inv_mul_cancel_right] using
      (normalizer ((A ⊓ F : Subgroup G) : Set G) ⊓
        normalizer ((⁅A,F⁆ : Subgroup G) : Set G)).mul_mem (hDN hts) hsN
end Subgroup
