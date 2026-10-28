module

public import Theory.SpecificGroups.SL2.Affine.Core
public import Theory.GroupTheory.NormalCentralQuotientAction.KernelCriterion

/-!
# The affine two-core obstructs identification of central quotients

The translation by (0,1) lies in O₂(F² ⋊ SL₂(F)) and fails to commute with
the upper unipotent matrix with parameter one. Thus O₂ is not central,
and the natural map from the central quotient to the quotient by the
preimage of Z(L/O₂(L)) is not injective. This holds over every finite field
of characteristic two, including F₄, where the two-core quotient is SL₂(4).

This tests the quotient identification proposed in Corollary A.2.6 of
Aschbacher–Smith, printed p.34 of `refs/quasithin.pdf`. It does not assert
that the full source corollary is false, nor assume an identification of
these two different quotients.
-/

public section
open Subgroup

namespace Matrix.SL2
open Matrix
open scoped MatrixGroups
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

theorem affine_twoCore_not_le_center : ¬ pCore 2 (Affine F) ≤ center (Affine F) := by
  intro hc
  let v : Multiplicative (Fin 2 → F) := Multiplicative.ofAdd ![0, 1]
  let u : SL(2, F) := ⟨!![1,1;0,1], by simp [det_fin_two]⟩
  have hv : (SemidirectProduct.inl v : Affine F) ∈ pCore 2 (Affine F) := by
    rw [affine_twoCore_eq, ← range_inl_eq_translations]
    exact ⟨v, rfl⟩
  have h := mem_center_iff.mp (hc hv) (SemidirectProduct.inr u)
  have he := congrArg (fun z : Affine F => Multiplicative.toAdd z.left 0) h
  simp [SemidirectProduct.mul_left, naturalAction_apply, u, v,
    mulVec, dotProduct, Fin.sum_univ_two] at he
  exact one_ne_zero he

theorem affine_centralQuotientProjection_not_injective :
    ¬ Function.Injective (centralQuotientProjection (pCore 2 (Affine F))) := by
  intro h
  apply affine_twoCore_not_le_center F
  rw [(centralQuotientProjection_injective_iff _).mp h]
  exact le_centralPreimage _

end Matrix.SL2

