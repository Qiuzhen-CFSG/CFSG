module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.Basic
public import Theory.SpecificGroups.PSL3.UniversalProjection
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound

/-!+# The degree-three cover exclusions in 1.1.5

For a quasisimple group with central quotient PSL₃(3), universality lifts
the actual SL₃ projection through the original central quotient cover.
Perfectness makes this lift surjective, so the original center order divides
the scalar kernel order gcd(3, 2) = 1.

For PSU₃(3), the original center order divides the constructed universal
kernel order. The proved odd-parameter upper bound is gcd(3, 4) = 1.
This uses the full universal-kernel bound, including its two-primary
exclusion; no trivial-two-core hypothesis is imposed on the original group.
Both arguments preserve the arbitrary field and Hermitian-form witnesses.

These center exclusions discharge the final cover premises in the odd-family
assembly, which retains the original marked action.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503, and I.1.3(2).
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
variable {L : Type*} [Group L] [IsQuasisimple L]

/-- The actual universal SL₃ projection excludes every nontrivial central
cover above PSL₃(3). -/
theorem linear_three_three_center_eq_bot
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 3) : center L = ⊥ := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let c := centralQuotientCover e
  obtain ⟨a, ha, _⟩ := Matrix.PSL3.UniversalProjection.existsUnique_projection_lift
    c.toMonoidHom c.surjective c.ker_le_center (by omega) (by omega)
  have hs : Function.Surjective a :=
    Matrix.PSL3.projection_lift_surjective F c.toMonoidHom c.ker_le_center a ha
  have hd : Nat.card (center L) ∣ Nat.card (Matrix.PSL3.projection F).ker := by
    simpa only [c, centralQuotientCover_ker] using
      kernel_card_dvd_of_surjective_factor (Matrix.PSL3.projection F)
        c.toMonoidHom a hs ha
  rw [Matrix.PSL3.card_projectionKernel, hcard] at hd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hd)

/-- The genuine odd-parameter multiplier bound excludes every nontrivial
central cover above PSU₃(3), for the original Hermitian-form model. -/
theorem unitary_three_three_center_eq_bot
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 3 3) : center L = ⊥ := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := h
  have hb := BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.universal_kernel_bound
    J (p := 3) (e := 1) Nat.prime_three (by decide) (by decide) (by decide)
    (by simpa only [pow_one] using hcard) (by simpa only [pow_one] using hconj)
  change Nat.card (universalProjection
    (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)).ker ≤ 1 at hb
  have hk := Nat.le_antisymm hb Nat.card_pos
  have hd := center_card_dvd_universal_kernel e
  rw [hk] at hd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hd)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
