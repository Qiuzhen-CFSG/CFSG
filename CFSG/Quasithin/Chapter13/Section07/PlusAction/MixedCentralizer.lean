module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Kernel
public import Theory.ThreeSubgroups

/-!
# A seed-centralizer test for the mixed plus-kernel action

If the point residual acts nontrivially throughout the seed, but its
mixed commutator with a two-perfect subgroup of the plus kernel is trivial,
then two rotations of the three-subgroups lemma make the whole seed central
for that subgroup. The final step uses coprime commutator idempotence.

This is the group-theoretic step in the nonzero mixed commutator argument of
Aschbacher--Smith 13.7.4(1), printed p.938. The actual seed generation and
ambient seed-centralizer bound are supplied by the original-data consumer.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
variable {G : Type*} [Group G] [Finite G]

/-- Vanishing of the mixed commutator forces the selected kernel actor to
centralize the original seed. -/
theorem kernel_seed_centralization_of_mixed_trivial
    {F : ChapterF.Section09.Setup G} (h : F.Hypothesis)
    {A K : Subgroup G} (hAH : A ≤ F.H)
    (hKC : K ≤ kernel F) (hp : IsPPerfect 2 K)
    (hKA : ⁅K,A⁆ ≤ F.QH)
    (hseed : ⁅F.Vplus,A⁆ = F.Vplus)
    (hmix : ⁅⁅fixedLayer F,A⁆,K⁆ = ⊥) :
    K ≤ centralizer (F.Vplus : Set G) := by
  have hKH : K ≤ F.H := hKC.trans kernel_le_H
  have hrot : ⁅⁅K,A⁆,fixedLayer F⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hKA.trans (le_centralizer_iff.mp (show fixedLayer F ≤ centralizer (F.QH : Set G) from inf_le_right))
  have hUKA : ⁅⁅F.UH,K⁆,A⁆ = ⊥ := by
    rw [residual_kernel_commutator h hKC hp]
    apply commutator_commutator_eq_bot_of_rotate hrot
    rwa [commutator_comm A (fixedLayer F)]
  have hAKU : ⁅⁅A,K⁆,F.UH⁆ ≤ F.V₁ := by
    rw [commutator_comm A K]
    exact (commutator_mono hKA le_rfl).trans (by
      rw [commutator_comm F.QH F.UH]
      exact h.commutator_UH_QH_le_point)
  have hnorm : F.H ≤ normalizer (F.V₁ : Set G) :=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hUAK : ⁅⁅F.UH,A⁆,K⁆ ≤ F.V₁ := by
    apply commutator_commutator_le_of_rotate_of_le_normalizer
      (h.UH_le_H.trans hnorm) (hAH.trans hnorm) (hKH.trans hnorm) hAKU
    rw [commutator_comm K F.UH,hUKA]
    exact bot_le
  have hseedK : ⁅F.Vplus,K⁆ ≤ F.V₁ := by
    rw [← hseed]
    exact (commutator_mono (commutator_mono
      (le_conjugateSpanBy F.Vplus F.H) le_rfl) le_rfl).trans hUAK
  have hKn : K ≤ normalizer (F.Vplus : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hseedK.trans h.point_lt.le)
  have hpoint : ⁅F.V₁,K⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hKH.trans h.H_centralizes)
  have hid := commutator_isPPerfect_idempotent K F.Vplus hp
    (h.g2_hypothesis.U_isPGroup.to_le (le_conjugateSpanBy F.Vplus F.H)) hKn
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply eq_bot_iff.mpr
  rw [← hid]
  exact (commutator_mono hseedK le_rfl).trans hpoint.le

end CFSG.Quasithin.Chapter13.Section07.PlusAction
