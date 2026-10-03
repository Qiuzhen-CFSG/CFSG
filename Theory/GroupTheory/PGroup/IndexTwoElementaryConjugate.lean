module

public import Theory.ElementaryAbelian.Join
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.Group

/-!
# Conjugate elementary subgroups with an index-two normalizer

If an elementary subgroup has an index-two normalizer, its join with an
outside conjugate is normal. In the absence of normal elementary eights, an
elementary eight therefore cannot commute with its outside conjugate. This
constructs an actual outside involution, without any automizer hypothesis.

The proof uses the two cosets of the normalizer: the inside coset preserves
both factors, and the outside coset interchanges them. This is the elementary
subgroup geometry in Janko–Thompson, Math. Z. 113 (1970), p.388.
-/

namespace Subgroup
variable {P : Type*} [Group P]

/-- The join of a subgroup with an outside conjugate is normal when its
normalizer has index two. -/
public theorem sup_conjugate_normal_of_normalizer_index_two
    (E : Subgroup P) (hindex : (normalizer (E : Set P)).index = 2)
    (t : P) (ht : t ∉ normalizer (E : Set P)) :
    (E ⊔ E.map (MulAut.conj t).toMonoidHom).Normal := by
  let N := normalizer (E : Set P)
  let F := E.map (MulAut.conj t).toMonoidHom
  let J := E ⊔ F
  let : N.Normal := normal_of_index_eq_two hindex
  have hNF : N ≤ normalizer (F : Set P) := by
    rw [← map_equiv_normalizer_eq E (MulAut.conj t)]
    exact (mem_normalizer_iff_map_conj_eq.mp
      (show t ∈ normalizer (N : Set P) by
        rw [N.normalizer_eq_top]
        exact mem_top t)).ge
  have hNJ : N ≤ normalizer (J : Set P) :=
    (le_inf le_rfl hNF).trans (normalizer_inf_normalizer_le_normalizer_sup E F)
  have hFt : F.map (MulAut.conj t).toMonoidHom = E := by
    have hmaps : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (t ^ 2)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_two]
      group
    change (E.map _).map _ = E
    rw [map_map, hmaps]
    exact mem_normalizer_iff_map_conj_eq.mp (N.sq_mem_of_index_two hindex t)
  have htJ : t ∈ normalizer (J : Set P) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (E ⊔ F).map _ = E ⊔ F
    rw [map_sup]
    change F ⊔ F.map (MulAut.conj t).toMonoidHom = E ⊔ F
    rw [hFt]
    exact sup_comm F E
  apply normalizer_eq_top_iff.mp
  apply eq_top_iff.mpr
  intro g _
  by_cases hg : g ∈ N
  · exact hNJ hg
  · have hgt : g * t⁻¹ ∈ N := by
      rw [N.mul_mem_iff_of_index_two hindex, N.inv_mem_iff]
      exact iff_of_false hg ht
    change g ∈ normalizer (J : Set P)
    simpa using (normalizer (J : Set P)).mul_mem (hNJ hgt) htJ

/-- An elementary eight with an index-two normalizer has an involution
in every outside conjugate which does not centralize the original eight. -/
public theorem exists_involution_in_conjugate_not_centralizing
    [Finite P]
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E)
    (hindex : (normalizer (E : Set P)).index = 2)
    (t : P) (ht : t ∉ normalizer (E : Set P)) :
    ∃ x : P, x ∈ E.map (MulAut.conj t).toMonoidHom ∧
      orderOf x = 2 ∧ x ∉ centralizer (E : Set P) := by
  let F := E.map (MulAut.conj t).toMonoidHom
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hnot : ¬ F ≤ centralizer (E : Set P) := by
    intro hcomm
    let : IsElementaryAbelian 2 (E ⊔ F : Subgroup P) :=
      IsElementaryAbelian.sup_of_le_centralizer hcomm
    exact hno ⟨E ⊔ F, sup_conjugate_normal_of_normalizer_index_two E hindex t ht,
      inferInstance, hE.trans (card_le_of_le le_sup_left)⟩
  obtain ⟨x, hxF, hxC⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨x, hxF, ?_, hxC⟩
  apply orderOf_eq_prime_iff.mpr
  refine ⟨elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := F) x hxF, ?_⟩
  intro hx
  exact hxC (hx ▸ (centralizer (E : Set P)).one_mem)

end Subgroup
