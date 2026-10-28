module
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.ThreeSubgroups

/-!
# Fixed points of a reciprocal conjugation layer

Suppose Q acts on V with kernel Q ∩ N, the commutator [V,Q] is fixed
by A, and [V,A] = V. If [C,A] lies in N for C ≤ Q, then three-subgroups
rotation makes [V,A] centralize C. Thus C lies in the action kernel.
The fixed preimage of A on Q/(Q ∩ N) is exactly Q ∩ N.

All normality is relative to the displayed actors; N need not be normal
in the ambient group, nor need it lie in Q. The source application is the
literal second-kernel layer in DGS85 (12.6), printed p.183, implemented in
CommutingThreeProfile.SecondKernelFixedPoints.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Full reciprocal movement removes every fixed coset of the action kernel. -/
theorem fixed_preimage_eq_of_reciprocal_centralizer (A V Q N Z : Subgroup G)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hAN : A ≤ normalizer (N : Set G))
    (hQN : Q ≤ normalizer (N : Set G))
    (hkernel : Q ⊓ N = Q ⊓ centralizer (V : Set G))
    (hcomm : ⁅V,Q⁆ ≤ Z) (hcentral : Z ≤ centralizer (A : Set G))
    (hfull : ⁅V,A⁆ = V) : commutatorPreimage Q A N = Q ⊓ N := by
  let C := commutatorPreimage Q A N
  have hCQ : C ≤ Q := commutatorPreimage_le _ _ _
  have h1 : ⁅⁅C,A⁆,V⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    have hCA : ⁅C,A⁆ ≤ Q ⊓ N := le_inf
      ((commutator_mono hCQ le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hAQ))
      (commutator_commutatorPreimage_le Q A N hQN)
    exact hCA.trans (hkernel.le.trans inf_le_right)
  have h2 : ⁅⁅V,C⁆,A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono le_rfl hCQ).trans hcomm).trans hcentral)
  have h3 : ⁅⁅A,V⁆,C⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h2 h1
  rw [commutator_comm A V,hfull,commutator_comm V C] at h3
  apply le_antisymm
  · exact (le_inf hCQ (commutator_eq_bot_iff_le_centralizer.mp h3)).trans hkernel.ge
  · exact le_commutatorPreimage inf_le_left
      ((commutator_mono inf_le_right le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hAN))

end Subgroup

