module

public import Theory.SpecificGroups.PSL3.UniversalProjection
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.CoveringComparisonKernelCard

/-!
# Recognizing ordinary degree-three central covers

The proved Steinberg relations and presentation faithfulness construct a
map from SL₃ onto a perfect group with marked quotient PSL₃. Comparing
the kernels bounds its center by gcd(3,|F|−1). If that center is nontrivial,
the scalar map is injective as well, identifying the supplied group with
SL₃ and preserving the given projective marking.

The exceptional coefficient-field orders two and four are excluded here.
Source: Aschbacher–Smith A.2.12(I), A.2.18 and I.1.3(2), printed pp.36,
40 and 407; the Steinberg proofs are in the imported modules.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups

namespace Matrix.PSL3.OrdinaryCenterRecognition

variable {F : Type*} [Field F] [Finite F]
variable {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]

omit [Finite L] in
/-- The actual scalar-cover lift, with the prescribed projective marking. -/
theorem exists_scalar_lift (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4)
    (e : L ⧸ center L ≃* PSL(3,F)) :
    ∃ k : SL(3,F) →* L, Function.Surjective k ∧
      (centralQuotientCover e).toMonoidHom.comp k = projection F := by
  let f := centralQuotientCover e
  obtain ⟨k, hk, _⟩ := UniversalProjection.existsUnique_lift_of_faithful
    f.toMonoidHom f.surjective f.ker_le_center h2 h4
    (UniversalProjection.matrixMap_injective h2 h4)
  exact ⟨k, projection_lift_surjective F f.toMonoidHom f.ker_le_center k hk, hk⟩

omit [Finite L] in
/-- The original covering center divides the scalar center, with no
universality or matrix-presentation hypothesis remaining. -/
theorem center_card_dvd (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4)
    (e : L ⧸ center L ≃* PSL(3,F)) :
    Nat.card (center L) ∣ Nat.gcd 3 (Nat.card F - 1) := by
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift h2 h4 e
  have hd := kernel_card_dvd_of_surjective_factor (projection F)
    (centralQuotientCover e).toMonoidHom k hks hk
  simpa only [centralQuotientCover_ker, card_projectionKernel] using hd

/-- A nontrivial ordinary cover is the actual SL₃ group, with cyclic center
of order three and a commuting projective triangle. -/
theorem nontrivial_center_recognition (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4)
    (e : L ⧸ center L ≃* PSL(3,F)) (hz : center L ≠ ⊥) :
    Nat.card (center L) = 3 ∧ Nat.card F % 3 = 1 ∧
      Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧
      ∃ j : SL(3,F) ≃* L,
        (centralQuotientCover e).toMonoidHom.comp j.toMonoidHom = projection F := by
  have hd := center_card_dvd h2 h4 e
  have h3 : Nat.card (center L) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _
      (hd.trans (Nat.gcd_dvd_left 3 (Nat.card F - 1))) with h1 | h3
    · exact (hz ((center L).eq_bot_of_card_eq h1)).elim
    · exact h3
  have hg : Nat.gcd 3 (Nat.card F - 1) = 3 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (h3 ▸ hd)
  have hm : Nat.card F % 3 = 1 := by
    have hdiv : 3 ∣ Nat.card F - 1 := hg ▸ Nat.gcd_dvd_right 3 (Nat.card F - 1)
    have := Nat.mod_eq_zero_of_dvd hdiv
    have : 0 < Nat.card F := Nat.card_pos
    omega
  obtain ⟨k, hks, hk⟩ := exists_scalar_lift h2 h4 e
  have hcount := kernel_card_eq_mul_of_surjective_factor (projection F)
    (centralQuotientCover e).toMonoidHom k (centralQuotientCover e).surjective hks hk
  have hker : Nat.card k.ker = 1 := by
    rw [card_projectionKernel, hg, centralQuotientCover_ker, h3] at hcount
    omega
  let j : SL(3,F) ≃* L := MulEquiv.ofBijective k
    ⟨k.ker_eq_bot_iff.mp (k.ker.eq_bot_of_card_eq hker), hks⟩
  exact ⟨h3, hm, ⟨mulEquivOfPrimeCardEq h3 (by simp)⟩, j, hk⟩

end Matrix.PSL3.OrdinaryCenterRecognition
