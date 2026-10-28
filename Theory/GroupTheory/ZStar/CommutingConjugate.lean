module

public import Theory.GroupTheory.ZStar.CoreFree
public import FeitThompson.FinalTheorem

/-!
# A distinct commuting conjugate when the solvable radical is trivial

An isolated involution has all its commutators of odd order. The proved
Z-star theorem places these in a normal odd-order subgroup. The odd-order
theorem and trivial solvable radical make that subgroup trivial, forcing
the involution into the center, which is also trivial.

Thus every involution has a distinct commuting conjugate. Ambient simplicity
and Sylow centrality are unnecessary. This is the application of Glauberman's
Z-star theorem in GLS, Volume 4, Chapter 2, equation (4F).
-/

namespace Theory.GroupTheory
open BenderSuzuki

/-- Isolation contradicts the trivial solvable radical, without simplicity. -/
public theorem exists_distinct_commuting_conjugate_of_no_solvable_normal
    {G : Type*} [Group G] [Finite G] {u : G} (hu : PFAppendixIII.IsInvolution u)
    (hsol : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) :
    ∃ v : G, u ≠ v ∧ IsConj u v ∧ Commute u v := by
  classical
  by_contra hnot
  have hiso : ∀ g : G, Commute (g * u * g⁻¹) u → g * u * g⁻¹ = u := by
    intro g hg
    by_contra hne
    exact hnot ⟨g * u * g⁻¹, Ne.symm hne, isConj_iff.mpr ⟨g, rfl⟩, hg.symm⟩
  have hodd := Glauberman.ZStar.orderOf_commutator_odd_of_isolated_involution hu hiso
  obtain ⟨N, hN, hNodd, hcomm⟩ :=
    Glauberman.ZStar.oddOrderZStarConclusion_of_exists_principalTwoBlockData
      Glauberman.ZStar.PrincipalBlockFactory.principalTwoBlockData_factory u hu hodd
  have hNb : N = ⊥ := hsol N hN (odd_order_theorem N hNodd)
  have huC : u ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have he := hcomm g
    rw [hNb, Subgroup.mem_bot] at he
    have he' := mul_inv_eq_one.mp he
    exact (mul_inv_eq_iff_eq_mul.mp he')
  have hcenter : Subgroup.center G = ⊥ := hsol _ inferInstance
    (Group.isSolvable_of_comm (fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp b.property a)))
  rw [hcenter, Subgroup.mem_bot] at huC
  exact hu.ne_one huC

end Theory.GroupTheory
