module

public import Theory.GroupTheory.PResidual.Quotient
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Residual centralization from a pointwise automorphism fixer

If M normalizes H and centralizes D ≤ H, its action on H lands in the
pointwise fixer of the literal D inside Aut(H). A p-group fixer kills
Oᵖ(M); a trivial fixer kills all of M. No faithfulness of the M-action
or identification of D with an abstract model is presumed.

Source application: Aschbacher–Smith, proof of 13.9.1, printed p.974,
where D = O²(M₂) ≃ A₄ and H is recognized as PSL₃(2) or A₆.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The actual conjugation action with codomain restricted to its pointwise fixer. -/
def normalizerFixerAction (M H D : Subgroup G)
    (hMH : M ≤ normalizer (H : Set G))
    (hMC : M ≤ centralizer (D : Set G)) :
    M →* fixingSubgroup (MulAut H) (D.subgroupOf H : Set H) :=
  (H.normalizerMonoidHom.comp (inclusion hMH)).codRestrict _ (by
    intro m
    apply (mem_fixingSubgroup_iff _).mpr
    intro d hd
    apply Subtype.ext
    change (m : G) * (d : G) * (m : G)⁻¹ = d
    rw [← mem_centralizer_iff.mp (hMC m.property) d hd, mul_inv_cancel_right])

private theorem centralizes_of_normalizerFixerAction_eq_one
    (M H D : Subgroup G) (hMH : M ≤ normalizer (H : Set G))
    (hMC : M ≤ centralizer (D : Set G)) (m : M)
    (hm : normalizerFixerAction M H D hMH hMC m = 1) :
    (m : G) ∈ centralizer (H : Set G) := by
  intro h hh
  have he := congrArg (fun a : fixingSubgroup (MulAut H) (D.subgroupOf H : Set H) =>
    ((a : MulAut H) ⟨h, hh⟩ : G)) hm
  change (m : G) * h * (m : G)⁻¹ = h at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- A p-group pointwise fixer makes the embedded p-residual act trivially. -/
theorem embedded_pResidual_le_centralizer_of_isPGroup_fixer (p : ℕ)
    (M H D : Subgroup G) (hMH : M ≤ normalizer (H : Set G))
    (hMC : M ≤ centralizer (D : Set G))
    (hfix : IsPGroup p (fixingSubgroup (MulAut H) (D.subgroupOf H : Set H))) :
    (pResidual p M).map M.subtype ≤ centralizer (H : Set G) := by
  rintro x ⟨m, hm, rfl⟩
  exact centralizes_of_normalizerFixerAction_eq_one M H D hMH hMC m
    (pResidual_le_ker_of_isPGroup p (normalizerFixerAction M H D hMH hMC) hfix hm)

/-- A trivial pointwise fixer makes the entire normalizing subgroup act trivially. -/
theorem le_centralizer_of_fixer_eq_bot
    (M H D : Subgroup G) (hMH : M ≤ normalizer (H : Set G))
    (hMC : M ≤ centralizer (D : Set G))
    (hfix : fixingSubgroup (MulAut H) (D.subgroupOf H : Set H) = ⊥) :
    M ≤ centralizer (H : Set G) := by
  intro m hm
  apply centralizes_of_normalizerFixerAction_eq_one M H D hMH hMC ⟨m, hm⟩
  apply Subtype.ext
  change ((normalizerFixerAction M H D hMH hMC ⟨m, hm⟩) : MulAut H) = 1
  have h := (normalizerFixerAction M H D hMH hMC ⟨m, hm⟩).property
  simpa only [hfix, mem_bot] using h

end Subgroup
