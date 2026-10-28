module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.MetacyclicTransfer.Stabilizer
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.ScalarQuotients
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The scalar supplement obstruction

If N is normal and NK = X, then [X:K] = [N:N ∩ K]. A Sylow subgroup R
meets N in a Sylow subgroup of N. Consequently R ∩ N ≤ K makes [X:K]
prime to p. For the literal semilinear scalars this contradicts p dividing
[B:K] = |Γ|. Taking N = [X,X] contradicts scalar normal generation.

The private index calculation only assumes normality of N. In particular,
K is never treated as normal in X. The public application supplies the
actual scalar subgroup and coefficient-group order.

Source: GLS, Volume 4, Chapter 1, Lemma 3.9, the last two sentences of
the Q < R branch, `refs/KGroup/GLS4/Chapter1.tex`, lines 437–443.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem index_eq_relIndex_of_normal_supplement
    (N K : Subgroup G) [N.Normal] (hNK : N ⊔ K = ⊤) :
    K.index = K.relIndex N := by
  have hNrel : N.relIndex K = N.index := by
    rw [← Subgroup.relIndex_sup_left K N, hNK, Subgroup.relIndex_top_right]
  have hleft := Subgroup.relIndex_mul_index (H := K ⊓ N) (K := K) inf_le_left
  have hright := Subgroup.relIndex_mul_index (H := K ⊓ N) (K := N) inf_le_right
  rw [Subgroup.inf_relIndex_left, hNrel] at hleft
  rw [Subgroup.inf_relIndex_right] at hright
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero N.index_ne_zero_of_finite)
  exact hleft.trans (hright.symm.trans (Nat.mul_comm _ _))

private theorem not_normal_sup_eq_top_of_sylow_inf_le
    {p : ℕ} [Fact p.Prime] (R : Sylow p G)
    (N K : Subgroup G) [N.Normal]
    (hRK : (R : Subgroup G) ⊓ N ≤ K) (hpK : p ∣ K.index) :
    N ⊔ K ≠ ⊤ := by
  intro hsup
  obtain ⟨S, hS⟩ := R.exists_subgroupOf_eq_of_normal N
  have hrel : ¬ p ∣ (R : Subgroup G).relIndex N := by
    change ¬ p ∣ ((R : Subgroup G).subgroupOf N).index
    rw [← hS]
    exact S.not_dvd_index
  apply hrel
  have hd : K.relIndex N ∣ (R : Subgroup G).relIndex N := by
    have h := Subgroup.relIndex_dvd_of_le_left N hRK
    rwa [Subgroup.inf_relIndex_right] at h
  exact (index_eq_relIndex_of_normal_supplement N K hsup ▸ hpK).trans hd
end Subgroup

namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
variable [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)

/-- Scalar normal generation contradicts focal containment when p divides |Γ|. -/
public theorem scalarClosure_ne_top_of_focal_containment
    {p : ℕ} [Fact p.Prime] (R : Sylow p X)
    (hpΓ : p ∣ Nat.card (twoPoint (X := X) (F := F)))
    (hfocal : commutator X ⊓ (R : Subgroup X) ≤ c.scalarSubgroup) :
    c.scalarClosure ≠ ⊤ := by
  intro hgen
  have hpidx : p ∣ c.scalarSubgroup.index := by
    have hd : p ∣ c.scalarSubgroup.relIndex (stabilizer X (0 : F)) := by
      rw [c.scalar_relIndex_stabilizer]
      exact hpΓ
    exact hd.trans (Subgroup.relIndex_dvd_index_of_le c.scalarSubgroup_le_stabilizer)
  exact Subgroup.not_normal_sup_eq_top_of_sylow_inf_le R (commutator X) c.scalarSubgroup
    (by simpa only [inf_comm] using hfocal) hpidx
    (c.commutator_sup_scalar_eq_top hgen)
end MulAction.SemilinearPointStabilizer.Coordinates
