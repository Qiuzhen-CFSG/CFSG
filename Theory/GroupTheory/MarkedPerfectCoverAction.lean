module

public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Actions on a marked perfect central cover

A marking of a perfect central cover preserves an automorphism whenever
its given quotient action agrees with the action of the proposed lift.
Uniqueness of maps from a perfect group through a central extension proves
the equality on the original covering group. No choice of lifted outer
automorphism is required.

Source: Aschbacher--Smith I.1.1--I.1.4, pp.407--408; the marked graph
action on the degree-three cover in F.6.18(11), p.310.
-/

public section
open Subgroup
namespace PerfectCentralCovering
variable {K E B : Type*} [Group K] [Group E] [Group B] [Group.IsPerfect K]

theorem equiv_symm_intertwines_of_marked_cover (q : E →* B) (hq : q.ker ≤ center E) (f : K →* B)
    (a : E ≃* K) (ha : f.comp a.toMonoidHom = q)
    (α : MulAut K) (β : MulAut E) (γ : MulAut B)
    (hα : ∀ x, f (α x) = γ (f x))
    (hβ : ∀ x, q (β x) = γ (q x)) :
    ∀ x, a.symm (α x) = β (a.symm x) := by
  have he (x : K) : q (a.symm x) = f x := by
    have h := DFunLike.congr_fun ha (a.symm x)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, a.apply_symm_apply] using h.symm
  have hmap : a.symm.toMonoidHom.comp α.toMonoidHom = β.toMonoidHom.comp a.symm.toMonoidHom := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq q hq
    ext x
    change q (a.symm (α x)) = q (β (a.symm x))
    rw [he, hα, hβ, he]
  intro x
  exact DFunLike.congr_fun hmap x

end PerfectCentralCovering
