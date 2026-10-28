module
public import Theory.Representation.Suzuki.TwoGroupFixedIndex
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
/-!
# Small two-groups under Suzuki residual actions

If a finite group maps onto Sz(q), q > 2, with two-group kernel, its
two-residual acts trivially on every two-group of order below q².
Otherwise a Sylow two-subgroup with nontrivial Suzuki image has fixed
index at least q², contradicting the order of the acted-on group.
The action is the given homomorphism, without a faithfulness assumption.

Source: the residual displacement bound in DGS, Groups and Graphs (1985),
5.7 and 8.4, pp.108,138; applied to the small neighboring-kernel quotient
in the proof of (12.9), printed p.188.
-/
public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace Representation.Suzuki
variable {D X : Type*} [Group D] [Finite D] [Group X] [Finite X]
/-- A two-group of order below q² is centralized by the two-residual of
any Suzuki extension with a two-group kernel. -/
theorem residual_le_action_kernel_of_small_card {m : ℕ} (hm : 0 < m)
    (π : D →* SuzukiMatrixGroup m) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (hp : IsPGroup 2 X)
    (hsmall : Nat.card X < (2^(2*m+1))^2) (α : D →* MulAut X) :
    pResidual 2 D ≤ α.ker := by
  by_contra hr
  let T : Sylow 2 (SuzukiMatrixGroup m) := Classical.arbitrary _
  obtain ⟨P,hP⟩ := Sylow.mapSurjective_surjective hπ 2 T
  have he : (P : Subgroup D).map π = (T : Subgroup (SuzukiMatrixGroup m)) :=
    congrArg (fun U : Sylow 2 (SuzukiMatrixGroup m) => (U : Subgroup (SuzukiMatrixGroup m))) hP
  have hne : (P : Subgroup D).map π ≠ ⊥ := by
    rw [he]
    intro hh
    have hcard := suzukiSylow_card hm (MulEquiv.refl _) T
    rw [hh,card_bot] at hcard
    have hq : 1 < 2^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
    nlinarith
  have hl := twoGroup_fixedIndex_lower_of_residual_moves hm π hπ hk hp α hr
    (P : Subgroup D) P.isPGroup' hne
  let _ := MulDistribMulAction.compHom X (α.comp (P : Subgroup D).subtype)
  have hu : (FixedPoints.subgroup (P : Subgroup D) X).index ≤ Nat.card X :=
    Nat.le_of_dvd Nat.card_pos (index_dvd_card _)
  exact (not_le_of_gt hsmall) (hl.trans hu)
end Representation.Suzuki
