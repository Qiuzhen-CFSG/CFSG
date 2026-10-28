module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.PGroupCore

/-!
# The ambient two-core of PSL₃(2)

A normal two-subgroup lies in the upper triangular Sylow subgroup. Conjugating
by the permutation reversing the coordinates puts it in the lower triangular
subgroup as well. The intersection is trivial over the binary field.
This is the faithful ambient linear model used in Aschbacher–Smith I.5.4.
-/

namespace Matrix.PSL3Two

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem opposite_upper_intersection : ∀ g : SL,
    (g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0) →
    ((Bruhat.perm 5 * g * (Bruhat.perm 5)⁻¹).val 1 0 = 0 ∧
     (Bruhat.perm 5 * g * (Bruhat.perm 5)⁻¹).val 2 0 = 0 ∧
     (Bruhat.perm 5 * g * (Bruhat.perm 5)⁻¹).val 2 1 = 0) → g = 1 := by
  decide +kernel

public theorem pCore_two_PSL_eq_bot : pCore 2 PSL = ⊥ := by
  have hB : pCore 2 PSL ≤ borel := pCore_isPGroup.le_sylow_of_normal borelSylow
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨g, rfl⟩ := project_surjective x
  have hg := (mem_borel_project g).mp (hB hx)
  have hc := hB (Subgroup.Normal.conj_mem (pCore_normal (p := 2) (G := PSL))
    (project g) hx (project (Bruhat.perm 5)))
  have hc' : project (Bruhat.perm 5 * g * (Bruhat.perm 5)⁻¹) ∈ borel := by
    simpa only [map_mul, map_inv] using hc
  have he := opposite_upper_intersection g hg (mem_borel_project _ |>.mp hc')
  simpa only [he, map_one] using (Subgroup.one_mem (⊥ : Subgroup PSL))

end Matrix.PSL3Two
