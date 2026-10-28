module
public import Theory.GroupTheory.Commutator.FixedSeedKernel

/-!
# The moved subgroup of a conjugate span from its generating actors

A supplement fixing the seed contributes no extra displacement. Bounds on
the other seed commutators propagate through the conjugate span by the normal
centralizer modulo the proposed moved subgroup. This yields the full moved
sum in the completion of Aschbacher--Smith 12.3.1, printed p.812.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A fixed supplement contributes no additional moved group to a conjugate span. -/
theorem conjugateSpan_commutator_le_of_fixed_generators
    (Z H K B T W : Subgroup G) (hZD : Z ≤ H) (hgen : K ⊔ B ⊔ T = H)
    (hHW : H ≤ normalizer (W : Set G))
    (hZK : ⁅Z,K⁆ ≤ W) (hZB : ⁅Z,B⁆ ≤ W) (hTZ : T ≤ centralizer (Z : Set G)) :
    ⁅conjugateSpanBy Z H,H⁆ ≤ W := by
  have hKH : K ≤ H := hgen ▸ (le_sup_left.trans le_sup_left)
  have hBH : B ≤ H := hgen ▸ (le_sup_right.trans le_sup_left)
  have hTH : T ≤ H := hgen ▸ le_sup_right
  have hactors : H ≤ commutatorPreimage H Z W := by
    conv_lhs => rw [←hgen]
    apply sup_le (sup_le (le_commutatorPreimage hKH ?_)
      (le_commutatorPreimage hBH ?_)) (le_commutatorPreimage hTH ?_)
    · rwa [commutator_comm]
    · rwa [commutator_comm]
    · rw [commutator_eq_bot_iff_le_centralizer.mpr hTZ]
      exact bot_le
  have hZH : ⁅Z,H⁆ ≤ W := by
    rw [commutator_comm]
    exact (commutator_mono hactors le_rfl).trans
      (commutator_commutatorPreimage_le H Z W hHW)
  have hspan : conjugateSpanBy Z H ≤ commutatorPreimage H H W :=
    conjugateSpanBy_le (le_commutatorPreimage hZD hZH)
      (commutatorPreimage_normalized H H W H hHW H.le_normalizer H.le_normalizer hHW)
  exact (commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le H H W hHW)
end Subgroup
