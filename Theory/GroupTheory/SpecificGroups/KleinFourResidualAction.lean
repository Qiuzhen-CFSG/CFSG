module

public import Theory.GroupTheory.SpecificGroups.KleinFourFixedAut
public import Theory.GroupTheory.PResidual.Defs

/-!
# Two-residuals in actions on a Klein four

An action on a Klein four with a nonidentity fixed point has two-group
image. Its kernel therefore contains the two-residual of the acting group.
In particular, a two-perfect group with such a fixed point acts trivially.

The proof uses the faithful action of the point stabilizer on the two
remaining nonidentity elements, and the first isomorphism theorem.
This is the small-module argument used on each invariant four-group in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Lemma 13.2.14, printed p.883.
The application must establish invariance and a nonidentity fixed point
on each summand; these are not consequences of this lemma.
-/

namespace IsKleinFour

open Subgroup

variable {H V : Type*} [Group H] [Group V] [IsKleinFour V]

/-- A fixed nonidentity point forces the two-residual into the action kernel. -/
public theorem twoResidual_le_ker_of_fixed_ne_one
    (ρ : H →* MulAut V) {v : V} (hv : v ≠ 1)
    (hfix : ∀ h : H, ρ h v = v) : pResidual 2 H ≤ ρ.ker := by
  have hp : IsPGroup 2 ρ.range :=
    isPGroup_aut_subgroup_of_fixed_ne_one ρ.range hv (by
      rintro f ⟨h, rfl⟩
      exact hfix h)
  have hquot : IsPGroup 2 (H ⧸ ρ.ker) :=
    hp.of_equiv (QuotientGroup.quotientKerEquivRange ρ).symm
  exact sInf_le ⟨inferInstance, hquot⟩

/-- A two-perfect group acting on a Klein four with a nonidentity fixed point
acts trivially. No finiteness assumption on the acting group is needed. -/
public theorem action_eq_one_of_twoPerfect_of_fixed_ne_one
    (ρ : H →* MulAut V) (hH : IsPPerfect 2 H) {v : V} (hv : v ≠ 1)
    (hfix : ∀ h : H, ρ h v = v) : ρ = 1 := by
  have hk := twoResidual_le_ker_of_fixed_ne_one ρ hv hfix
  rw [(pResidual_eq_top_iff 2 H).mpr hH] at hk
  apply MonoidHom.ext
  intro h
  exact MonoidHom.mem_ker.mp (hk (mem_top h))

end IsKleinFour
