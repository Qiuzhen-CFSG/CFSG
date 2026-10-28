module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Setup

/-!
# The local two-point stabilizer

For `t ∉ M`, the group `D = M ∩ Mᵗ` contains no distinguished involution:
such an involution would lie in two distinct conjugates of `M`, contrary
to product disconnection. Thus its local distinguished closure is trivial,
as required when applying GLS, Volume 4, Chapter 2, Corollary 16.6(e).
The internal version below keeps subsequent normality relative to `M`.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFchapter1section1

variable {G : Type*} [Group G]

/-- The two-point stabilizer regarded as a subgroup of the local group `M`. -/
@[expose] public def residualPairIn (M : Subgroup G) (t : G) : Subgroup M :=
  (residualPairStabilizer M t).subgroupOf M

/-- Passing to the internal subgroup does not change the two-point group. -/
public def residualPairInEquiv (M : Subgroup G) (t : G) :
    residualPairIn M t ≃* residualPairStabilizer M t :=
  Subgroup.subgroupOfEquivOfLe inf_le_left

public theorem not_mem_Z_of_mem_residualPairStabilizer
    {Z : Set G} {M : Subgroup G} (h : IsProductDisconnected Z M)
    {t x : G} (ht : t ∉ M) (hx : x ∈ residualPairStabilizer M t) : x ∉ Z := by
  intro hxZ
  apply ht
  apply (h.conjugate_mem_iff x hxZ hx.1 t).mp
  obtain ⟨y, hy, heq⟩ := hx.2
  simpa only [← heq, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left,
    inv_mul_cancel_left, mul_inv_cancel, mul_one, SetLike.mem_coe] using hy

/-- Here the local circle is generation by `Z ∩ D`, not a residual. -/
public theorem residualPairStabilizer_localClosure_eq_bot
    {Z : Set G} {M : Subgroup G} (h : IsProductDisconnected Z M)
    {t : G} (ht : t ∉ M) :
    Subgroup.closure ((residualPairStabilizer M t).subtype ⁻¹' Z) = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [Subgroup.closure_le]
  intro x hx
  exact False.elim (not_mem_Z_of_mem_residualPairStabilizer h ht x.property hx)

end BenderSuzuki.ZD
