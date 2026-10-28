module
public import Theory.GroupTheory.IndexTwoExtensionEquivalence
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Extending compatible maps across an index-two overlap

Suppose maps of normal index-two subgroups and of chosen overgroups agree
on their intersection. If the intersection detects automorphisms of the
normal subgroup, conjugation by an outside overlap element agrees everywhere.
Its square also lies in the intersection, so the index-two extension theorem
extends both given maps simultaneously.

This is the gluing step for the doubled unitary amalgam in Aschbacher--Smith
13.5.17, printed p.922. No splitting assumption on either extension is used.
-/

public noncomputable section
open Subgroup
namespace Subgroup

/-- Compatible normal-subgroup and overlap maps extend when the intersection
detects automorphisms of the normal subgroup. The result retains both maps. -/
theorem exists_mulEquiv_of_index_two_overlap
    {G H : Type*} [Group G] [Group H]
    (N : Subgroup G) (N' : Subgroup H) [N.Normal] [N'.Normal]
    (hi : N.index = 2) (hi' : N'.index = 2)
    (B : Subgroup G) (B' : Subgroup H)
    (eN : N ≃* N') (eB : B ≃* B')
    (hcompat : ∀ (n : N) (hn : (n : G) ∈ B),
      (eN n : H) = (eB ⟨n, hn⟩ : H))
    (hdetect : ∀ α β : MulAut N,
      (∀ n : N, (n : G) ∈ B → α n = β n) → α = β)
    (a : B) (ha : (a : G) ∉ N) (ha' : (eB a : H) ∉ N') :
    ∃ e : G ≃* H, (∀ n : N, e n = (eN n : H)) ∧
      (∀ b : B, e b = (eB b : H)) := by
  let α : MulAut N := MulAut.conjNormal (a : G)
  let β : MulAut N := (eN.trans (MulAut.conjNormal (eB a : H))).trans eN.symm
  have hc (n : N) (hn : (n : G) ∈ B) :
      (eN (α n) : H) = (eB a : H) * (eN n : H) * (eB a : H)⁻¹ := by
    have hb : ((α n : N) : G) ∈ B := B.mul_mem
      (B.mul_mem a.property hn) (B.inv_mem a.property)
    rw [hcompat (α n) hb, hcompat n hn]
    have he : (⟨((α n : N) : G), hb⟩ : B) = a * ⟨n, hn⟩ * a⁻¹ := rfl
    rw [he, map_mul, map_mul, map_inv]
    rfl
  have hab : α = β := hdetect α β (by
    intro n hn
    apply eN.injective
    apply Subtype.ext
    change (eN (α n) : H) =
      (eN (eN.symm (MulAut.conjNormal (eB a : H) (eN n))) : H)
    rw [eN.apply_symm_apply]
    exact hc n hn)
  have hact (n : N) :
      (eN ⟨(a : G) * (n : G) * (a : G)⁻¹,
        (inferInstance : N.Normal).conj_mem n n.property a⟩ : H) =
      (eB a : H) * (eN n : H) * (eB a : H)⁻¹ := by
    change (eN (α n) : H) = _
    rw [hab]
    change (eN (eN.symm (MulAut.conjNormal (eB a : H) (eN n))) : H) = _
    rw [eN.apply_symm_apply]
    rfl
  have hsq : (eN ⟨(a : G)^2, N.sq_mem_of_index_two hi a⟩ : H) =
      (eB a : H)^2 := by
    rw [hcompat _ (B.pow_mem a.property 2)]
    change ((eB (a^2) : B') : H) = _
    rw [map_pow]
    rfl
  obtain ⟨e, heN, hea⟩ := exists_mulEquiv_of_index_two_extensions N N' hi hi'
    a (eB a) ha ha' eN hsq hact
  refine ⟨e, heN, ?_⟩
  intro b
  by_cases hb : (b : G) ∈ N
  · exact (heN ⟨b, hb⟩).trans (hcompat ⟨b, hb⟩ b.property)
  · have hx : (b : G) * (a : G)⁻¹ ∈ N := by
      rw [N.mul_mem_iff_of_index_two hi, N.inv_mem_iff]
      simp only [hb, ha]
    have hh := (heN ⟨(b : G) * (a : G)⁻¹, hx⟩).trans
      (hcompat ⟨_, hx⟩ (B.mul_mem b.property (B.inv_mem a.property)))
    change e ((b : G) * (a : G)⁻¹) = (eB (b * a⁻¹) : H) at hh
    simp only [map_mul, map_inv, coe_mul, coe_inv, hea] at hh
    exact mul_right_cancel hh

end Subgroup
