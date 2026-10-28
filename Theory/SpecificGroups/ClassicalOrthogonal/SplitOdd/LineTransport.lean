/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd

/-!
# Elementary orthogonal containment from singular-vector transport

An isometry subgroup containing all Siegel transformations at one singular
vector and transporting that vector to every nonzero singular vector contains
the elementary group. Conjugation covariance transports the parameters as
well as the singular vector; the zero-vector transformations are the identity.

Adapted from `Atlas/LinearGroups/Orthogonal/RootGenerationFromLineTransport.lean`.
This exact-vector variant is sufficient over the binary field and is applied
to the Co₁ local matrix image. It makes no order or recognition assumption.
-/

@[expose] public section
open Theory.AlgebraicGroup
namespace ClassicalOrthogonal
open Quadratic
universe u
variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
variable (Q : QuadraticForm F V)

theorem elementary_le_of_siegel_and_transport
    (H : Subgroup (quadraticIsometrySubgroup Q)) (e : V) (he : Q e = 0)
    (hr : ∀ v (hv : Q.polarBilin e v = 0), siegelElement Q e v he hv ∈ H)
    (ht : ∀ u : V, u ≠ 0 → Q u = 0 →
      ∃ g : quadraticIsometrySubgroup Q, g ∈ H ∧ g.val e = u) :
    elementarySubgroup Q ≤ H := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨u, v, hu, huv, rfl⟩
  by_cases hun : u = 0
  · subst u
    have hid : siegelElement Q 0 v hu huv = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change siegel Q 0 v x = x
      simp [siegel]
    rw [hid]
    exact H.one_mem
  · obtain ⟨g, hg, hgu⟩ := ht u hun hu
    let gi : Q.IsometryEquiv Q :=
      { g.val with map_app' := (mem_quadraticIsometrySubgroup Q _).mp g.prop }
    have hp : Q.polarBilin e (g.val.symm v) = 0 := by
      have h := isometry_polar Q gi e (g.val.symm v)
      change Q.polarBilin (g.val e) (g.val (g.val.symm v)) = _ at h
      rw [hgu, g.val.apply_symm_apply] at h
      exact h.symm.trans huv
    have hm := H.mul_mem (H.mul_mem hg (hr (g.val.symm v) hp)) (H.inv_mem hg)
    suffices heq : siegelElement Q u v hu huv =
        g * siegelElement Q e (g.val.symm v) he hp * g⁻¹ by
      rw [heq]
      exact hm
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change siegel Q u v x = gi (siegel Q e (g.val.symm v) (g.val.symm x))
    rw [siegel_covariant Q gi]
    change siegel Q u v x = siegel Q (g.val e) (g.val (g.val.symm v))
      (g.val (g.val.symm x))
    rw [hgu, g.val.apply_symm_apply, g.val.apply_symm_apply]

end ClassicalOrthogonal
