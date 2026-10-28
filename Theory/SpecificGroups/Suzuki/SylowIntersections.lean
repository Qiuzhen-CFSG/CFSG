module

public import Theory.SpecificGroups.Suzuki.AbelianSubgroups
public import Theory.GroupTheory.SylowCentralizerTransport

/-!
# Suzuki Sylow intersections

The actual root Sylow subgroup contains the centralizer of each of its
nonidentity elements. Sylow conjugacy transports that bound, proving that
distinct Sylow two-subgroups intersect trivially.

Source: Huppert--Blackburn III, XI.3.1 and XI.3.10; the Bender-group
step in Aschbacher--Smith 2.5.3(3), printed p.552.
-/

public section
namespace BenderSuzuki.MatrixGroups
open Subgroup

theorem suzuki_sylow_eq_of_inf_ne_bot (m : ℕ) (hm : 0 < m)
    (P Q : Sylow 2 (SuzukiMatrixGroup m))
    (hi : (P : Subgroup (SuzukiMatrixGroup m)) ⊓ (Q : Subgroup (SuzukiMatrixGroup m)) ≠ ⊥) : P = Q := by
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow m hm
  apply Sylow.eq_of_inf_ne_bot_of_one_sylow R P Q _ hi
  rw [hR]
  exact fun _ hx hn => suzukiRootSubgroup_centralizer_le m hm hx hn

end BenderSuzuki.MatrixGroups
