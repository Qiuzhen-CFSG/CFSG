module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.LocalSplitting
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.LocalOrder
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.OrthogonalMap
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.InvolutionFusion
public import Theory.SpecificGroups.G2.FiniteUniversalCover

/-!
# The two-primary ordinary G₂ multiplier exclusion

The local covering argument proves the desired exclusion from an actual
orthogonal subgroup and two actual involution conjugacies. The subgroup
map must have the diagonal scalar kernel; its odd index is proved from
the checked group orders. The SL₂ splitting theorem, descent through the
diagonal kernel, prime-order quotient reduction, and transfer are all
discharged, including their application to the literal universal projection.

The quaternion-coordinate subgroup map and the split-octonion involution
fusion theorem discharge both geometric inputs. Consequently two does not
divide the kernel order of the literal universal projection for G₂(p), p > 3.
The conditional interfaces are retained for other local realizations. This
proves the two-primary part of the ordinary multiplier entry; the other
prime exclusions are separate. No multiplier bound, centerlessness argument,
or table omission is used as a proof substitute.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408 (PDF pp.418–419),
and GLS III §6.1. The prime-field range is p > 3.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

/-- Application of the proved local-cover argument to the literal canonical
projection. The local model and its two fusion identities remain explicit. -/
theorem universal_not_two_dvd_kernel_of_local_model
    (hF : Nat.card F = p) (hp : 3 < p) (m : LocalModel p (Model F))
    (houter : IsConj (m.inclusion m.scalar) (m.inclusion m.outer))
    (hpair : IsConj (m.inclusion m.scalar) (m.inclusion m.paired)) :
    ¬ 2 ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact m.not_two_dvd_kernel hp houter hpair (universalCover (Model F))

/-- A concrete local map with diagonal kernel and involution fusion suffice.
The image index, all three element orders, and all central-cover inputs are
proved here; construction of the map and fusion remain source obligations. -/
theorem universal_not_two_dvd_kernel_of_diagonal_map_and_fusion
    (hF : Nat.card F = p) (hp : 3 < p)
    (φ : C2 →* MulAut (RankOne p × RankOne p))
    (j : (RankOne p × RankOne p) ⋊[φ] C2 →* Model F)
    (hj : ∀ x, j x = 1 ↔ x = 1 ∨ x = SemidirectProduct.inl (-1, -1))
    (hfusion : ∀ x y : Model F, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ¬ 2 ∣ Nat.card (universalProjection (Model F)).ker := by
  let m : LocalModel p (Model F) := {
    action := φ
    inclusion := j
    kernel := hj
    odd_index := odd_index_of_diagonal_kernel hF hp φ j hj }
  exact universal_not_two_dvd_kernel_of_local_model hF hp m
    (hfusion _ _ (m.scalar_image_order hp) m.outer_image_order)
    (hfusion _ _ (m.scalar_image_order hp) m.paired_image_order)

/-- The ordinary odd-prime G₂ universal kernel has odd order. The actual
orthogonal subgroup map and octonion involution fusion discharge all local
geometric premises in the canonical-projection calculation. -/
theorem universal_not_two_dvd_kernel (hF : Nat.card F = p) (hp : 3 < p) :
    ¬ 2 ∣ Nat.card (universalProjection (Model F)).ker := by
  obtain ⟨φ, j, hj⟩ := exists_orthogonal_diagonal_map hF hp
  exact universal_not_two_dvd_kernel_of_diagonal_map_and_fusion hF hp φ j hj
    (InvolutionFusion.involutions_isConj hF hp)

end Atlas.G2.MultiplierOrdinary.OddTwoPrimary

end
