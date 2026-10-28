module

public import Theory.Alternating.Aut
public import Theory.GroupTheory.InnerStabilizerAction
import Mathlib.Tactic.Group

/-!
# Detecting outer A₅ actions with a five-cycle

Every automorphism of A₅ comes from conjugation in S₅. An explicit odd
permutation takes a fixed five-cycle to its square; multiplying by its inverse
reduces any odd conjugator to an even one. Therefore an outer restriction to
an actual A₅ subgroup would, after inner conjugation, give an ambient
automorphism sending an element of order five to its square.

This is the permutation-group step in Aschbacher–Smith, *The Classification
of Quasithin Groups*, proof of Lemma 1.3.9, printed p.514. The ambient
separation premise is explicit and is discharged in the parent module.
-/

public section

namespace CFSG.Quasithin.Chapter1.Terminal.LinearTwoStabilizer
open Equiv Equiv.Perm

private def c : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4
private def d : Perm (Fin 5) := swap 1 2 * swap 2 4 * swap 4 3

private theorem c_mem : c ∈ alternatingGroup (Fin 5) := by
  rw [mem_alternatingGroup]
  decide
private theorem d_sign : sign d = -1 := by decide
private theorem d_conj : d * c * d⁻¹ = c ^ 2 := by decide

private def fiveCycle : alternatingGroup (Fin 5) := ⟨c, c_mem⟩
private theorem fiveCycle_order : orderOf fiveCycle = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide : fiveCycle ^ 5 = 1) (by decide : fiveCycle ≠ 1)

private theorem aut_inner_or_moves_fiveCycle (β : MulAut (alternatingGroup (Fin 5))) :
    (∃ a : alternatingGroup (Fin 5), β = MulAut.conj a) ∨
    (∃ a : alternatingGroup (Fin 5), β fiveCycle = a * fiveCycle ^ 2 * a⁻¹) := by
  obtain ⟨σ, rfl⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective β
  by_cases hσ : σ ∈ alternatingGroup (Fin 5)
  · left
    exact ⟨⟨σ, hσ⟩, rfl⟩
  · right
    have hs : sign σ = -1 := (Int.units_eq_one_or (sign σ)).resolve_left hσ
    have ha : σ * d⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [mem_alternatingGroup, map_mul, map_inv, hs, d_sign]
      decide
    refine ⟨⟨σ * d⁻¹, ha⟩, ?_⟩
    apply Subtype.ext
    change σ * c * σ⁻¹ = (σ * d⁻¹) * c ^ 2 * (σ * d⁻¹)⁻¹
    rw [← d_conj]
    group

/-- If no ambient automorphism sends an element of order five to its square,
then the stabilizer of every actual A₅ subgroup acts by inner automorphisms. -/
theorem hasInnerStabilizerAction_of_orderFive_square_separation
    {G : Type*} [Group G]
    (hsep : ∀ (α : MulAut G) (x : G), orderOf x = 5 → α x ≠ x ^ 2)
    (A : Subgroup G) (e : A ≃* alternatingGroup (Fin 5)) :
    A.HasInnerStabilizerAction := by
  intro α hα
  let r : MulAut A := (α.subgroupMap A).trans (MulEquiv.subgroupCongr hα)
  let β : MulAut (alternatingGroup (Fin 5)) := e.symm.trans (r.trans e)
  rcases aut_inner_or_moves_fiveCycle β with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨e.symm a, (e.symm a).property, ?_⟩
    intro x hx
    have h := MulEquiv.congr_fun ha (e ⟨x, hx⟩)
    have he : r ⟨x, hx⟩ = e.symm a * ⟨x, hx⟩ * (e.symm a)⁻¹ := by
      apply e.injective
      simpa [β, MulAut.conj_apply] using h
    exact congrArg Subtype.val he
  · let x : A := e.symm fiveCycle
    let a' : A := e.symm a
    have ho : orderOf (x : G) = 5 := by
      exact (orderOf_injective A.subtype Subtype.val_injective x).trans
        ((e.symm.orderOf_eq fiveCycle).trans fiveCycle_order)
    have he : α (x : G) = (a' : G) * (x : G) ^ 2 * (a' : G)⁻¹ := by
      have hh : r x = a' * x ^ 2 * a'⁻¹ := by
        apply e.injective
        simpa [β, x, a'] using ha
      exact congrArg Subtype.val hh
    exfalso
    apply hsep (MulAut.conj (a' : G)⁻¹ * α) (x : G) ho
    change (a' : G)⁻¹ * α (x : G) * ((a' : G)⁻¹)⁻¹ = (x : G) ^ 2
    rw [he]
    group

end CFSG.Quasithin.Chapter1.Terminal.LinearTwoStabilizer
