module
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Transferring centralization along a full actor

Let Q and Z be normal subgroups of G. If Q centralizes U modulo Z
and E equals its commutator with U, then Q centralizes E modulo Z.
Neither finiteness nor normality of E or U is required.

Pass to G/Z. The image of Q is normal, so its centralizer is normal.
That centralizer contains the image of U and therefore its commutator
with the image of E. The full-commutator equation places the entire
image of E in the centralizer. Pulling back gives the stated bound.

This is the generic transfer used in Stellmacher (9.1), Journal of
Algebra 190 (1997), p.48, after bounding [Q_alpha,V₁] by Z_alpha.
The actual vertex-group normality and full-actor equation belong to
the application.
-/

namespace Subgroup

/-- A normal subgroup centralizing a full actor modulo a normal layer also
centralizes its full commutator modulo that layer. -/
public theorem commutator_le_of_full_actor
    {G : Type*} [Group G] (Q E U Z : Subgroup G) [Q.Normal] [Z.Normal]
    (hQU : ⁅Q, U⁆ ≤ Z) (hEU : ⁅E, U⁆ = E) : ⁅Q, E⁆ ≤ Z := by
  let π := QuotientGroup.mk' Z
  let Qbar := Q.map π
  let Ebar := E.map π
  let Ubar := U.map π
  let _ : Qbar.Normal := (inferInstance : Q.Normal).map π (QuotientGroup.mk'_surjective Z)
  have hQUbar : ⁅Qbar, Ubar⁆ = ⊥ := by
    rw [← map_commutator]
    exact (map_eq_bot_iff _).mpr (by simpa [π] using hQU)
  have hEUbar : ⁅Ebar, Ubar⁆ = Ebar := by rw [← map_commutator, hEU]
  have hUcent : Ubar ≤ centralizer (Qbar : Set (G ⧸ Z)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hQUbar)
  have hEcent : Ebar ≤ centralizer (Qbar : Set (G ⧸ Z)) := by
    rw [← hEUbar]
    exact (commutator_mono le_rfl hUcent).trans (commutator_le_right _ _)
  have hQEbar : ⁅Qbar, Ebar⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hEcent)
  rw [← map_commutator] at hQEbar
  simpa [π] using (map_eq_bot_iff _).mp hQEbar

end Subgroup
