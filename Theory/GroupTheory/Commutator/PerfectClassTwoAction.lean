module

public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Perfect actors with abelian displacement on a class-two group

Suppose a perfect subgroup acts on Q, centralizes Z(Q), and its commutator
with Q is abelian. The three-subgroup lemma puts the second displacement
in Z(Q). Perfectness then kills successively the second and first
displacements. No coprimality, subnormality, or finiteness is required.

This is the elementary commutator reduction used for the special radical
in Aschbacher--Smith F.1.12(I)(4), with the short-group square condition
from C.1.7 (`refs/quasithin.pdf`, pp.123 and 263).
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A perfect actor fixing the center of a class-two subgroup cannot have
a nontrivial abelian commutator with it. The subgroup Z is the embedded
center, specified by the two containments actually needed in the proof. -/
theorem commutator_eq_bot_of_perfect_abelian_classTwo_action
    (Q Z X : Subgroup G) [Group.IsPerfect X]
    (hnorm : X ≤ normalizer Q)
    (hclass : ⁅Q, Q⁆ ≤ Z)
    (hcenter : Q ⊓ centralizer (Q : Set G) ≤ Z)
    (hfix : ⁅Z, X⁆ = ⊥)
    (hab : ⁅⁅Q, X⁆, ⁅Q, X⁆⁆ = ⊥) : ⁅Q, X⁆ = ⊥ := by
  let N := ⁅Q, X⁆
  have hNQ : N ≤ Q := le_normalizer_iff_commutator_le_left.mp hnorm
  have hNRX : ⁅⁅Q, N⁆, X⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (commutator_mono ((commutator_mono le_rfl hNQ).trans hclass)
      le_rfl).trans_eq hfix
  have hNXR : ⁅⁅N, X⁆, Q⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by simpa only [commutator_comm X Q] using hab) hNRX
  have hNXZ : ⁅N, X⁆ ≤ Z := by
    apply le_trans (le_inf ?_ (commutator_eq_bot_iff_le_centralizer.mp hNXR)) hcenter
    exact (commutator_mono hNQ le_rfl).trans hNQ
  have hNXX : ⁅⁅N, X⁆, X⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hNXZ le_rfl).trans_eq hfix)
  exact commutator_eq_bot_of_iterated_eq_bot Q X
    (commutator_eq_bot_of_iterated_eq_bot N X hNXX)

end Subgroup

open scoped commutatorElement

/-- In a class-two group with elementary derived subgroup, multiplying an
actor by an element of that group does not change displacement squares.
The hypotheses are pointwise so this also applies to relative subgroups. -/
public theorem commutator_square_mul_actor
    {G : Type*} [Group G] (Q : Subgroup G)
    (hcentral : ∀ a ∈ Q, ∀ b ∈ Q, ∀ z ∈ Q, Commute ⁅a, b⁆ z)
    (hexp : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ^ 2 = 1)
    (r u g : G) (hr : r ∈ Q) (hu : u ∈ Q)
    (hv : ⁅r, g⁆ ∈ Q) : ⁅r, u * g⁆ ^ 2 = ⁅r, g⁆ ^ 2 := by
  let c := ⁅r, u⁆
  let d := ⁅u, ⁅r, g⁆⁆
  let v := ⁅r, g⁆
  have hd : d ∈ Q := (Subgroup.commutator_le_self Q)
    (Subgroup.commutator_mem_commutator hu hv)
  have hcv : Commute c v := hcentral r hr u hu _ hv
  have hcd : Commute c d := hcentral r hr u hu _ hd
  have hdv : Commute d v := hcentral u hu _ hv _ hv
  have hc2 : c ^ 2 = 1 := hexp r hr u hu
  have hd2 : d ^ 2 = 1 := hexp u hu _ hv
  have he : ⁅r, u * g⁆ = c * (d * v) := by
    dsimp only [c, d, v]
    simp only [commutatorElement_def]
    group
  rw [he, (hcd.mul_right hcv).mul_pow, hdv.mul_pow, hc2, hd2, one_mul, one_mul]
