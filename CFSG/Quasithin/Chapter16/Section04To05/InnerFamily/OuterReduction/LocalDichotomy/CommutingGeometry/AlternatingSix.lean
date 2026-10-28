module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic

/-!
# The alternating-six exception in the commuting-conjugate argument

Eight explicit even permutations provide a distinct commuting conjugate for
all nonidentity involutions of S₆. Lean's kernel checks this finite calculation.
The product of the two commuting involutions is an involution fixed by the
original actor. Its expression a(q)q⁻¹ transports through a genuine A₆ model
and the actual permutation implementing the action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.6,
printed p.1172, and the paragraph after (+) in 16.4.9(2), printed p.1190.
-/

public section

open Equiv Equiv.Perm Subgroup
open AlternatingSix.ShadowLocal

namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.CommutingGeometry

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

private def candidates (i : Fin 8) : Perm (Fin 6) :=
  ![swap 0 1 * (swap 2 3 * swap 3 4 * swap 4 5),
    swap 2 4 * swap 3 5,
    swap 3 4 * swap 4 5,
    swap 1 2 * swap 2 3,
    swap 0 2 * swap 2 5,
    swap 1 4 * swap 4 5,
    swap 0 3 * swap 3 4,
    swap 0 2 * swap 1 3] i

private theorem candidates_even : ∀ i, candidates i ∈ alternatingGroup (Fin 6) := by
  simp only [mem_alternatingGroup]
  decide +kernel

private theorem witness_check : ∀ σ : Perm (Fin 6), σ * σ = 1 → σ ≠ 1 →
    ∃ i : Fin 8, let τ := candidates i * σ * (candidates i)⁻¹
      τ ≠ σ ∧ σ * τ = τ * σ := by
  decide +kernel


/-- Every involution of the actual symmetric group on six letters has a
nontrivial fixed involutory displacement in its alternating subgroup. -/
theorem exists_fixed_displacement_of_six_permutation (σ : Perm (Fin 6)) (hσ : orderOf σ = 2) :
    ∃ q : A6, orderOf (permutationAction σ q * q⁻¹) = 2 ∧
      permutationAction σ (permutationAction σ q * q⁻¹) =
        permutationAction σ q * q⁻¹ := by
  have hsq : σ * σ = 1 := by simpa only [pow_two, hσ] using pow_orderOf_eq_one σ
  have hne : σ ≠ 1 := by intro he; simp [he] at hσ
  obtain ⟨i, ht, hc⟩ := witness_check σ hsq hne
  let q : A6 := ⟨candidates i, candidates_even i⟩
  let τ := candidates i * σ * (candidates i)⁻¹
  have ht2 : τ * τ = 1 := by
    change (MulAut.conj (candidates i) σ) * MulAut.conj (candidates i) σ = 1
    rw [← map_mul, hsq, map_one]
  have hsi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hsq
  have hv : ((permutationAction σ q * q⁻¹ : A6) : Perm (Fin 6)) = σ * τ := by
    change σ * candidates i * σ⁻¹ * (candidates i)⁻¹ = _
    rw [hsi]; dsimp [τ]; group
  refine ⟨q, ?_, ?_⟩
  · apply orderOf_eq_prime
    · apply Subtype.ext
      change (((permutationAction σ q * q⁻¹ : A6) : Perm (Fin 6))) ^ 2 = 1
      have hcomm : Commute σ τ := hc
      rw [hv, hcomm.mul_pow]
      simp only [pow_two, hsq, ht2, one_mul]
    · intro he
      have he' := congrArg Subtype.val he
      rw [hv] at he'
      exact ht (mul_left_cancel (he'.trans hsq.symm))
  · apply Subtype.ext
    change σ * ((permutationAction σ q * q⁻¹ : A6) : Perm (Fin 6)) * σ⁻¹ = _
    rw [hv, hsi]
    calc
      σ * (σ * τ) * σ = τ * σ := by rw [← mul_assoc, hsq, one_mul]
      _ = σ * τ := hc.symm

/-- Transport the permutation witness through the actual component model and
its pointwise intertwining equation. -/
theorem exists_fixed_displacement_of_alternatingSix {H : Type*} [Group H] (a : MulAut H)
    (ha : orderOf a = 2) (e : H ≃* A6) (σ : Perm (Fin 6))
    (he : ∀ x, e (a x) = permutationAction σ (e x)) :
    ∃ q : H, orderOf (a q * q⁻¹) = 2 ∧ a (a q * q⁻¹) = a q * q⁻¹ := by
  have hact : MulAut.congr e a = permutationAction σ := by
    apply MulEquiv.ext
    intro x
    change e (a (e.symm x)) = permutationAction σ x
    simpa only [e.apply_symm_apply] using he (e.symm x)
  have hσ : orderOf σ = 2 :=
    (orderOf_injective permutationAction permutationAction_injective σ).symm.trans
      (hact ▸ (MulAut.congr e).orderOf_eq a |>.trans ha)
  obtain ⟨q, hq, hf⟩ := exists_fixed_displacement_of_six_permutation σ hσ
  have hm : e (a (e.symm q) * (e.symm q)⁻¹) = permutationAction σ q * q⁻¹ := by
    rw [map_mul, map_inv, he, e.apply_symm_apply]
  refine ⟨e.symm q, ((e.orderOf_eq _).symm.trans (hm ▸ hq)), ?_⟩
  apply e.injective
  rw [he, hm, hf]
end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.CommutingGeometry
