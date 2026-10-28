module
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.Action
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.GraphChecks

/-!
# Faithfulness of the action of the central quotient on 252 blocks

A block-kernel element fixing points 0 and 1 fixes every point: each graph
neighbor has a different block label, so fixation propagates down the checked
spanning forest. The displayed central subgroup realizes every possible pair
of images of those roots. Cancelling the matching central element exhausts
the kernel, without computing the order of the generated permutation group.
The resulting equivalence retains the original quotient map and both generators.
Source context: Aschbacher–Smith I.1.4(5), p.408; numerical provenance is in
`BlockData` and `GraphData`. The forest proof adapts the repository's Suzuki
`AtlasModel/BlockComparison/Kernel.lean` argument to two components.
-/

public section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.BlockAction
open Graph

private def Preserves (g : Perm) : Prop :=
  ∀ p i, ∃ j, g (neighbor p i) = neighbor (g p) j

private theorem preserves_one : Preserves 1 := fun _ i => ⟨i, rfl⟩

private theorem preserves_mul {g h : Perm}
    (hg : Preserves g) (hh : Preserves h) : Preserves (g * h) := by
  intro p i
  obtain ⟨j, hj⟩ := hh p i
  obtain ⟨k, hk⟩ := hg (h p) j
  exact ⟨k, (congrArg g hj).trans hk⟩

private theorem preserves_pow {g : Perm} (hg : Preserves g) (n : ℕ) :
    Preserves (g ^ n) := by
  induction n with
  | zero => exact preserves_one
  | succ n ih => simpa only [pow_succ] using preserves_mul ih hg

private theorem preserves (g : Carrier) : Preserves g.val := by
  have ha : Preserves a := neighbor_a
  have hb : Preserves b := neighbor_b
  have hai : Preserves a⁻¹ := by
    have h : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using a_sq)
    rw [h]
    exact ha
  have hbi : Preserves b⁻¹ := by
    have h : b⁻¹ = b ^ 5 := inv_eq_of_mul_eq_one_left (by
      simpa only [← pow_succ] using b_six)
    rw [h]
    exact preserves_pow hb 5
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

private theorem fixes_blocks {g : Carrier} (hg : g ∈ action.ker) (p : Point) :
    blockOf (g.val p) = blockOf p := (action_eq_one_iff g).mp hg p

/-- Two fixed roots force a block-kernel element to be the identity. -/
theorem eq_one_of_mem_ker_of_fix_roots {g : Carrier}
    (hg : g ∈ action.ker) (h0 : g.val 0 = 0) (h1 : g.val 1 = 1) : g = 1 := by
  have fixed (n : ℕ) : ∀ p, rank p = n → g.val p = p := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn
      by_cases hp : p = 0
      · simpa only [hp] using h0
      by_cases hp' : p = 1
      · simpa only [hp'] using h1
      obtain ⟨i, hi⟩ := parent_neighbor p hp hp'
      have hparent : g.val (parent p) = parent p :=
        ih (rank (parent p)) (hn ▸ parent_rank_lt p hp hp') (parent p) rfl
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

/-- No additional elements are lost on passage to the central blocks. -/
theorem action_ker_eq_centralSubgroup : action.ker = centralSubgroup := by
  apply le_antisymm _ centralSubgroup_le_action_ker
  intro g hg
  obtain ⟨t, h0, h1⟩ := central_base_images (g.val 0) (g.val 1)
    (fixes_blocks hg 0) (fixes_blocks hg 1)
  have ht : kernelEmbedding t ∈ action.ker := action_kernelEmbedding t
  have he : (kernelEmbedding t)⁻¹ * g = 1 := eq_one_of_mem_ker_of_fix_roots
    (action.ker.mul_mem (action.ker.inv_mem ht) hg)
    (by
      change (kernelEmbedding t).val⁻¹ (g.val 0) = 0
      rw [← h0]
      exact (kernelEmbedding t).val.symm_apply_apply 0)
    (by
      change (kernelEmbedding t).val⁻¹ (g.val 1) = 1
      rw [← h1]
      exact (kernelEmbedding t).val.symm_apply_apply 1)
  exact ⟨t, inv_mul_eq_one.mp he⟩

theorem quotientAction_injective : Function.Injective quotientAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  induction x using QuotientGroup.induction_on with | H g =>
    change quotientAction (QuotientGroup.mk g) = 1 at hx
    rw [quotientAction_mk] at hx
    have hg : g ∈ centralSubgroup := action_ker_eq_centralSubgroup ▸ hx
    exact (QuotientGroup.eq_one_iff g).mpr hg

/-- The original quotient is the actual generated group on 252 central blocks. -/
noncomputable def quotientEquiv : Projective ≃* Model :=
  MulEquiv.ofBijective quotientAction ⟨quotientAction_injective, quotientAction_surjective⟩

@[simp] theorem quotientEquiv_mk (g : Carrier) :
    quotientEquiv (QuotientGroup.mk g) = action g := by
  change quotientAction (QuotientGroup.mk g) = action g
  exact quotientAction_mk g

@[simp] theorem quotientEquiv_sourceA :
    quotientEquiv (QuotientGroup.mk sourceA) = generatorA := by
  rw [quotientEquiv_mk, action_generatorA]

@[simp] theorem quotientEquiv_sourceB :
    quotientEquiv (QuotientGroup.mk sourceB) = generatorB := by
  rw [quotientEquiv_mk, action_generatorB]

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.BlockAction
