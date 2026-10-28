module
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Faithful normalizer action on a fully moved central quotient

Suppose a subgroup A acts faithfully modulo its original action kernel on
W/Z, Z centralizes A, and W=[W,A]. An overgroup H normalizing A, W and Z
has the same action kernel on W/Z and W. Its quotient-action kernel K is
normal in H; [K,A] lies in the original A-kernel and therefore centralizes
W, while [K,W] lies in Z and centralizes A. The three-subgroups lemma then
makes K centralize [W,A]=W.

Source application: Aschbacher–Smith, 10.2.12, printed p.754,
the equality C_T(V/V₂)=C_T(V₁).
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A fully moved group has the same normalizer-action kernel as its central
quotient, provided the acting subgroup already has this kernel property. -/
theorem commutatorPreimage_le_centralizer_of_fully_moved
    (H A W Z : Subgroup G) (hAH : A ≤ H)
    (hHA : H ≤ normalizer (A : Set G))
    (hHW : H ≤ normalizer (W : Set G))
    (hHZ : H ≤ normalizer (Z : Set G))
    (hZA : Z ≤ centralizer (A : Set G))
    (hgen : ⁅W,A⁆ = W)
    (hker : commutatorPreimage A W Z ≤ centralizer (W : Set G)) :
    commutatorPreimage H W Z ≤ centralizer (W : Set G) := by
  let K := commutatorPreimage H W Z
  have hKH : K ≤ H := commutatorPreimage_le _ _ _
  have hKW : ⁅K,W⁆ ≤ Z := commutator_commutatorPreimage_le _ _ _ hHZ
  have hAK : A ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized H W Z A hHZ
      (hAH.trans H.le_normalizer) (hAH.trans hHW) (hAH.trans hHZ)
  have hc : ⁅K,A⁆ ≤ commutatorPreimage A W Z := by
    apply le_commutatorPreimage
      (le_normalizer_iff_commutator_le_right.mp (hKH.trans hHA))
    exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp hAK) le_rfl).trans hKW
  have h1 : ⁅⁅A,K⁆,W⁆ = ⊥ := by
    rw [commutator_comm A K]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans hker)
  have h2 : ⁅⁅K,W⁆,A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hKW.trans hZA)
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hgen,commutator_comm W K] at h3
  exact commutator_eq_bot_iff_le_centralizer.mp h3
end Subgroup
