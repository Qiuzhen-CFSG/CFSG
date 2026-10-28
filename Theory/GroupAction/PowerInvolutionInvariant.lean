module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Reducibility of powers together with one involution

A family of automorphisms of a noncyclic abelian group preserves a proper
nonzero subgroup if each image of v is a power of v or of g(v), for one fixed
involutive automorphism g. The fixed subgroup of g works when it is proper
and nontrivial. Otherwise g is the identity or inversion, and any nontrivial
cyclic subgroup works. The acting family need not itself be a group.

This is the elementary action argument in Aschbacher–Smith, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace MulAut
variable {V : Type*} [Group V] [IsMulCommutative V]

/-- Pointwise powers and one involution preserve a proper nonzero subgroup. -/
theorem exists_invariant_of_power_involution (hnc : ¬ IsCyclic V)
    (D : Set (MulAut V)) (g : MulAut V) (hg : g ^ 2 = 1)
    (hp : ∀ a ∈ D, ∀ v, a v ∈ zpowers v ∨ a v ∈ zpowers (g v)) :
    ∃ A : Subgroup V, A ≠ ⊥ ∧ A ≠ ⊤ ∧ ∀ a ∈ D, ∀ v ∈ A, a v ∈ A := by
  classical
  let C := g.toMonoidHom.eqLocus (MonoidHom.id V)
  have hC : ∀ a ∈ D, ∀ v ∈ C, a v ∈ C := by
    intro a ha v hv
    rcases hp a ha v with hh | hh
    · exact (zpowers_le.mpr hv) hh
    · have he : g v = v := hv
      rw [he] at hh
      exact (zpowers_le.mpr hv) hh
  by_cases hCb : C = ⊥
  · have hinv : ∀ v, g v = v⁻¹ := by
      intro v
      have hv : g v * v ∈ C := by
        change g (g v * v) = g v * v
        have hh := DFunLike.congr_fun hg v
        change g (g v) = v at hh
        rw [map_mul, hh, mul_comm]
      exact mul_eq_one_iff_eq_inv.mp (Subgroup.mem_bot.mp (hCb ▸ hv))
    have hnt : Nontrivial V := by
      by_contra hh
      have := not_nontrivial_iff_subsingleton.mp hh
      exact hnc inferInstance
    obtain ⟨v, hv⟩ := exists_ne (1 : V)
    refine ⟨zpowers v, ?_, ?_, ?_⟩
    · intro hh
      exact hv (Subgroup.mem_bot.mp (hh ▸ mem_zpowers v))
    · exact fun hh => hnc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, hh⟩)
    · intro a ha x hx
      rcases hp a ha x with hh | hh
      · exact (zpowers_le.mpr hx) hh
      · rw [hinv] at hh
        exact (zpowers_le.mpr ((zpowers v).inv_mem hx)) hh
  · by_cases hCt : C = ⊤
    · have hid : ∀ v, g v = v := fun v => show v ∈ C from hCt.symm ▸ mem_top v
      have hnt : Nontrivial V := by
        by_contra hh
        have := not_nontrivial_iff_subsingleton.mp hh
        exact hnc inferInstance
      obtain ⟨v, hv⟩ := exists_ne (1 : V)
      refine ⟨zpowers v, ?_, ?_, ?_⟩
      · intro hh
        exact hv (Subgroup.mem_bot.mp (hh ▸ mem_zpowers v))
      · exact fun hh => hnc (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨v, hh⟩)
      · intro a ha x hx
        rcases hp a ha x with hh | hh
        · exact (zpowers_le.mpr hx) hh
        · rw [hid] at hh
          exact (zpowers_le.mpr hx) hh
    · exact ⟨C, hCb, hCt, hC⟩
end MulAut
