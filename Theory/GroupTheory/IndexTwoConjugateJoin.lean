module
public import Theory.GroupTheory.IndexTwoNormalizer
/-!
# The join of two conjugates under an index-two action

If D has relative index two in S and normalizes A, an element of S outside
D exchanges A with its conjugate. Their join is therefore normalized by S.
The proof keeps the ambient subgroups and left-conjugation convention,
using normality of D and the two cosets.

Source: the elementary index-two argument used with the original Sylow
bound in Aschbacher--Smith 12.6.4 and 12.6.12, printed pp.824--826.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- An index-two actor stabilizes the join of the two conjugates. -/
theorem le_normalizer_sup_conjugate_of_relIndex_two
    (A D S : Subgroup G) (hD : D ≤ S) (hi : D.relIndex S = 2)
    (hn : D ≤ normalizer (A : Set G)) (s : G) (hs : s ∈ S) (hsD : s ∉ D) :
    S ≤ normalizer ((A ⊔ A.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
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
  have hDJ : D ≤ normalizer ((A ⊔ F : Subgroup G) : Set G) :=
    (le_inf hn hDF).trans (normalizer_inf_normalizer_le_normalizer_sup A F)
  have hsq : s * s ∈ D := (D.subgroupOf S).mul_self_mem_of_index_two hi ⟨s,hs⟩
  have hsJ : s ∈ normalizer ((A ⊔ F : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_sup]
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
    change F ⊔ F.map (MulAut.conj s).toMonoidHom = A ⊔ F
    rw [hFF]
    exact sup_comm _ _
  intro t ht
  by_cases htD : t ∈ D
  · exact hDJ htD
  · have hts : t * s⁻¹ ∈ D :=
      ((D.subgroupOf S).mul_mem_iff_of_index_two hi).mpr
        (show ((⟨t,ht⟩ : S) ∈ D.subgroupOf S ↔
          (⟨s⁻¹,S.inv_mem hs⟩ : S) ∈ D.subgroupOf S) from by
          change t ∈ D ↔ s⁻¹ ∈ D
          simp only [inv_mem_iff,htD,hsD])
    simpa only [inv_mul_cancel_right] using
      (normalizer ((A ⊔ F : Subgroup G) : Set G)).mul_mem (hDJ hts) hsJ
end Subgroup
