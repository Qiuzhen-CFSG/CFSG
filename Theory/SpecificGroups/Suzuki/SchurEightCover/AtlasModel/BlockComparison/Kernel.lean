module
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockComparison.Action
public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.BlockComparison.GraphData

/-!
# Exhaustion of the block-action kernel

An element fixing every block and fixing zero fixes the graph's neighbors,
since their block labels are distinct. Induction along the checked spanning
tree makes it the identity. The local neighbor signature restricts the image
of zero under any block-kernel element to its four central translates.
Cancelling the appropriate central element therefore proves that the kernel
is exactly the already constructed central Klein four subgroup.

All numerical premises come from `GraphData`. This argument does not use an
order assertion or the separate native Suzuki matrix comparison. Source context:
Aschbacher--Smith I.1.1 and I.1.3(5), printed p.407; numerical provenance and
reproducible graph discovery are in `BlockComparison/source/README.md`.
-/

namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockComparison
open Data Graph

private def Preserves (g : Equiv.Perm Point) : Prop :=
  ∀ p i, ∃ j, g (neighbor p i) = neighbor (g p) j

private theorem preserves_one : Preserves 1 := fun _ i => ⟨i, rfl⟩

private theorem preserves_mul {g h : Equiv.Perm Point}
    (hg : Preserves g) (hh : Preserves h) : Preserves (g * h) := by
  intro p i
  obtain ⟨j, hj⟩ := hh p i
  obtain ⟨k, hk⟩ := hg (h p) j
  exact ⟨k, (congrArg g hj).trans hk⟩

private theorem preserves (g : E) : Preserves g.val := by
  have ha : Preserves a := neighbor_a
  have hb : Preserves b := neighbor_b
  have hai : Preserves a⁻¹ := ha
  have hbi : Preserves b⁻¹ := preserves_mul hb (preserves_mul hb hb)
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction_left with
  | one => exact preserves_one
  | mul_left x hx y hy ih =>
    rcases hx with rfl | rfl
    · exact preserves_mul ha ih
    · exact preserves_mul hb ih
  | inv_mul_cancel x hx y hy ih =>
    rcases hx with rfl | rfl
    · exact preserves_mul hai ih
    · exact preserves_mul hbi ih

private theorem fixes_blocks {g : E} (hg : g ∈ action.ker) (p : Point) :
    blockOf (g.val p) = blockOf p := by
  have h : action g = 1 := hg
  simpa only [h, Subgroup.coe_one, Equiv.Perm.one_apply] using action_spec g p

/-- A block-kernel element fixing one point fixes the connected graph. -/
public theorem eq_one_of_mem_action_ker_of_fix_zero {g : E}
    (hg : g ∈ action.ker) (h0 : g.val 0 = 0) : g = 1 := by
  have fixed (n : ℕ) : ∀ p, rank p = n → g.val p = p := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hp : p = 0
      · simpa only [hp] using h0
      obtain ⟨i, hi⟩ := parent_neighbor p hp
      have hparent : g.val (parent p) = parent p :=
        ih (rank (parent p)) (hn ▸ parent_rank_lt p hp) (parent p) rfl
      obtain ⟨j, hj⟩ := preserves g (parent p) i
      rw [hi, hparent] at hj
      have hjblock : blockOf (neighbor (parent p) j) =
          blockOf (neighbor (parent p) i) := by
        rw [← hj, hi]
        exact fixes_blocks hg p
      have hji := neighbor_blocks_injective (parent p) hjblock
      simpa only [hji, hi] using hj
  apply Subtype.ext
  apply Equiv.ext
  intro p
  exact fixed (rank p) p rfl

private theorem eq_of_mem_action_ker_of_same_zero {g k : E}
    (hg : g ∈ action.ker) (hk : k ∈ action.ker) (h : g.val 0 = k.val 0) : g = k := by
  have hi : k⁻¹ * g = 1 := eq_one_of_mem_action_ker_of_fix_zero
    (action.ker.mul_mem (action.ker.inv_mem hk) hg) (by
      change k.val⁻¹ (g.val 0) = 0
      rw [h]
      exact k.val.symm_apply_apply 0)
  exact (inv_mul_eq_one.mp hi).symm

/-- The graph restricts the block kernel to the actual central four-group. -/
public theorem action_ker_eq_kernel : action.ker = kernel := by
  apply le_antisymm _ kernel_le_action_ker
  intro g hg
  have hz : centralZ ∈ kernel := Subgroup.subset_closure (by simp)
  have hw : centralW ∈ kernel := Subgroup.subset_closure (by simp)
  have hzw : centralZ * centralW ∈ kernel := kernel.mul_mem hz hw
  obtain ⟨i, hi⟩ := preserves g 0 0
  have hblocks : blockOf (neighbor (g.val 0) i) = blockOf (neighbor 0 0) := by
    rw [← hi]
    exact fixes_blocks hg _
  rcases base_candidates (g.val 0) (fixes_blocks hg 0) i hblocks with h | h | h | h
  · exact (eq_one_of_mem_action_ker_of_fix_zero hg h) ▸ kernel.one_mem
  · have he : g = centralZ := eq_of_mem_action_ker_of_same_zero hg
      (kernel_le_action_ker hz) (by rw [coe_centralZ]; exact h)
    exact he ▸ hz
  · have he : g = centralW := eq_of_mem_action_ker_of_same_zero hg
      (kernel_le_action_ker hw) (by rw [coe_centralW]; exact h)
    exact he ▸ hw
  · have he : g = centralZ * centralW := eq_of_mem_action_ker_of_same_zero hg
      (kernel_le_action_ker hzw) (by
        rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, coe_centralZ, coe_centralW]
        exact h)
    exact he ▸ hzw

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.BlockComparison
