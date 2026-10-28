module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A moved prime subgroup vanishes in a coprime normal image

If U = [U,R] is a q-group and the image of R lies in a normal p-group
under a homomorphism, with p and q coprime, the image of U is trivial.
The commutator image lies in both the image of U and that normal p-group.
Source application: Aschbacher--Smith 12.2.21, printed p.802.
-/

public section
open Subgroup
namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

theorem pgroup_le_ker_of_commutator_eq_self
    (f : G →* K) {p q : ℕ} (U R : Subgroup G)
    (J : Subgroup K) [J.Normal]
    (hU : IsPGroup q U) (hJ : IsPGroup p J) (hpq : Nat.Coprime q p)
    (hmove : ⁅U, R⁆ = U) (hRJ : R.map f ≤ J) : U ≤ f.ker := by
  apply (map_eq_bot_iff U).mp
  have hd := (hU.map f).disjoint_of_coprime hJ hpq
  apply le_bot_iff.mp
  apply le_trans _ hd.le_bot
  refine le_inf le_rfl ?_
  rw [← hmove, map_commutator]
  exact (commutator_mono le_top hRJ).trans
    (le_normalizer_iff_commutator_le_right.mp le_normalizer_of_normal)

end Subgroup
