module
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# A normal symmetric-three subgroup splits off its centralizer

Trivial center gives disjointness, and every automorphism of S₃ is inner.
The resulting product equivalence is multiplication under the original
subgroup inclusions. It is used to control the actual normalizer of a
four-dimensional symmetric-three factor in the proof of 15.1.2.

Source: Aschbacher--Smith, 15.1.2, printed p.1085.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThree
open NormalSymmetricThreePairRank
variable {G : Type*} [Group G]

theorem centralizer_disjoint (H : Subgroup G) (j : H ≃* Equiv.Perm (Fin 3)) :
    Disjoint H (centralizer (H : Set G)) := by
  apply disjoint_def.mpr
  intro x hx hc
  have hz : j ⟨x,hx⟩ = 1 := by
    apply symmetricThree_center_trivial
    intro y
    have he : j.symm y * (⟨x,hx⟩ : H) = ⟨x,hx⟩ * j.symm y :=
      Subtype.ext (mem_centralizer_iff.mp hc _ (j.symm y).property)
    simpa only [map_mul,j.apply_symm_apply] using congrArg j he
  exact congrArg Subtype.val (j.injective (hz.trans j.map_one.symm))

theorem sup_centralizer_eq_top (H : Subgroup G) [H.Normal]
    (j : H ≃* Equiv.Perm (Fin 3)) : H ⊔ centralizer (H : Set G) = ⊤ := by
  apply top_unique
  intro g _
  let α : MulAut (Equiv.Perm (Fin 3)) := j.symm.trans ((MulAut.conjNormal g).trans j)
  obtain ⟨k,hk⟩ := symmetricThree_aut_inner α
  let h : H := j.symm k
  have he (x : H) : g * (x : G) * g⁻¹ = (h * x * h⁻¹ : H) := by
    change ((MulAut.conjNormal g x : H) : G) = _
    apply congrArg (fun a : H => (a : G))
    apply j.injective
    have hh := DFunLike.congr_fun hk (j x)
    simpa [α,h,MulAut.conj_apply] using hh
  have hc : (h : G)⁻¹ * g ∈ centralizer (H : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg (fun a : G => (h : G)⁻¹ * a * g) (he ⟨x,hx⟩)
    simpa [mul_assoc] using hh.symm
  have hm := (H ⊔ centralizer (H : Set G)).mul_mem
    ((show H ≤ H ⊔ centralizer (H : Set G) from le_sup_left) h.property)
    ((show centralizer (H : Set G) ≤ H ⊔ centralizer (H : Set G) from le_sup_right) hc)
  simpa only [← mul_assoc,mul_inv_cancel,one_mul] using hm

theorem exists_product_equiv (H : Subgroup G) [H.Normal]
    (j : H ≃* Equiv.Perm (Fin 3)) :
    ∃ e : H × centralizer (H : Set G) ≃* G,
      ∀ h c, e (h,c) = (h : G) * (c : G) := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting H
    (centralizer (H : Set G)) (centralizer_disjoint H j)
    (le_centralizer_iff.mpr le_rfl)
  let k := (MulEquiv.subgroupCongr (sup_centralizer_eq_top H j)).trans topEquiv
  exact ⟨e.trans k,he⟩
end Theory.GroupTheory.NormalSymmetricThree
