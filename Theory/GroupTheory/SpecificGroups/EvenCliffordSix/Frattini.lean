module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Basic
public import Theory.Frattini.BinarySquares

/-!
# Frattini subgroup and generation lifting

Every square in the coordinate group belongs to the sign kernel, and the
nontrivial sign is the square of the volume element. The finite two-group
Frattini theorem therefore identifies the entire Frattini subgroup with this
kernel. Generation of the actual augmentation quotient lifts to generation
of the group. This supplies the lifting step for the signed A₆ action.

Source: Aschbacher–Smith I.2.2(6), printed pp.410 and 412, combined manuscript
of 1 March 2004; the Frattini calculation uses the standard square description
for finite two-groups.
-/

@[expose] public section
namespace EvenCliffordSix

/-- The coordinate group has order a power of two. -/
theorem isPGroup : IsPGroup 2 Model :=
  IsPGroup.of_card (n := 6) (by rw [card]; norm_num)

/-- The actual Frattini subgroup is the central sign kernel. -/
theorem frattini_eq_signKernel : frattini Model = signKernel := by
  rw [isPGroup.frattini_eq_closure_squares]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    change x ^ 2 ∈ signKernel
    rw [square]
    rfl
  · rw [signKernel_eq_zpowers]
    apply Subgroup.zpowers_le.mpr
    rw [← volume_sq]
    exact Subgroup.subset_closure ⟨volume, rfl⟩

theorem frattini_card : Nat.card (frattini Model) = 2 := by
  rw [frattini_eq_signKernel, signKernel_card]

/-- In particular, its generator is the specified volume square. -/
theorem frattini_eq_zpowers : frattini Model = Subgroup.zpowers involution :=
  frattini_eq_signKernel.trans signKernel_eq_zpowers

/-- First isomorphism theorem on the literal Frattini quotient. -/
noncomputable def frattiniQuotientEquiv :
    (Model ⧸ frattini Model) ≃* Multiplicative V :=
  (QuotientGroup.quotientMulEquivOfEq frattini_eq_signKernel).trans quotientEquiv

@[simp] theorem frattiniQuotientEquiv_mk (x : Model) :
    frattiniQuotientEquiv (QuotientGroup.mk' (frattini Model) x) =
      Multiplicative.ofAdd x.vector := rfl

/-- A subgroup surjecting onto the actual augmentation quotient is the whole
coordinate group. This is the consumer of the Frattini identification. -/
theorem eq_top_of_projection (H : Subgroup Model) (h : H.map projection = ⊤) : H = ⊤ := by
  apply frattini_nongenerating
  rw [frattini_eq_signKernel]
  apply top_unique
  intro x _
  have hx : projection x ∈ H.map projection := h ▸ Subgroup.mem_top _
  obtain ⟨y, hy, he⟩ := hx
  have hk : y⁻¹ * x ∈ signKernel := by
    change projection (y⁻¹ * x) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hm : y * (y⁻¹ * x) ∈ H ⊔ signKernel :=
    (H ⊔ signKernel).mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hm

end EvenCliffordSix
