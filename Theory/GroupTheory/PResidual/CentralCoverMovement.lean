module
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Removing a central attachment from core-residual movement

Suppose [O_p(G),G] lies in a normal layer V, and W covers V modulo its
central part. Then [O_p(G),O^p(G)] lies in W itself: p-perfect commutator
idempotence applies a second commutator, which removes the central part.
This retains the actual prime residual and every original subgroup.

Source application: DGS, Groups and Graphs (1985), 6.5, printed p.122,
with V the Baumann module and W the neighboring center.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A normal subgroup covering the central quotient contains all core-residual movement. -/
theorem core_residual_le_of_central_cover (V W : Subgroup G) [W.Normal]
    (hcomm : ⁅pCore p G,(⊤ : Subgroup G)⁆ ≤ V)
    (hcover : W ⊔ (V ⊓ center G) = V) :
    ⁅pCore p G,pResidual p G⁆ ≤ W := by
  rw [←commutator_isPPerfect_idempotent (pResidual p G) (pCore p G)
    (isPPerfect_pResidual p) pCore_isPGroup le_normalizer_of_normal]
  apply le_trans (commutator_mono
    ((commutator_mono le_rfl le_top).trans hcomm) le_rfl)
  conv_lhs => rw [←hcover]
  apply commutator_sup_le_of_relative_normal ⊤ W (V ⊓ center G) (pResidual p G) W
    le_normalizer_of_normal le_top le_top (commutator_le_left _ _)
  exact (commutator_eq_bot_iff_le_centralizer.mpr
    (inf_le_right.trans (center_le_centralizer _))).le.trans bot_le
end Subgroup
