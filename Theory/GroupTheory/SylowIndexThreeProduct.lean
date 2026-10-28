module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Sylow overgroups and an index-three subgroup

If H and N contain the same Sylow two-subgroup of a finite group M, and
N has index three in M, then either H lies in N or HN is all of M.
The relative index of N in H is odd, greater than one, and at most three.
Equal coset counts then give the literal product, without assuming normality.

This is the finite-group step in Aschbacher--Smith15.2.5, printed p.1107.
-/

public section
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Equal relative coset counts give the literal subgroup product. -/
theorem coe_mul_eq_of_relIndex_eq {H N M : Subgroup G}
    (hHM : H ≤ M) (hNM : N ≤ M) (hi : N.relIndex H = N.relIndex M) :
    (H : Set G) * (N : Set G) = (M : Set G) := by
  ext g
  constructor
  · rintro ⟨h,hh,n,hn,rfl⟩
    exact M.mul_mem (hHM hh) (hNM hn)
  · intro hg
    let e := quotientSubgroupOfEmbeddingOfLE N hHM
    have he : Function.Surjective e :=
      (e.injective.bijective_of_nat_card_le hi.ge).2
    obtain ⟨q,hq⟩ := he (QuotientGroup.mk (⟨g,hg⟩ : M))
    induction q using Quotient.inductionOn with
    | h q =>
      have hn : (inclusion hHM q)⁻¹ * (⟨g,hg⟩ : M) ∈ N.subgroupOf M :=
        QuotientGroup.eq.mp hq
      exact ⟨q,q.property,(q : G)⁻¹ * g,hn,by simp⟩

/-- An escaping Sylow overgroup supplements an index-three subgroup. -/
theorem coe_mul_eq_of_index_three_sylow {H N M : Subgroup G}
    (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H) (hTN : (T : Subgroup G) ≤ N)
    (hHM : H ≤ M) (hNM : N ≤ M) (hi : N.relIndex M = 3) (hout : ¬ H ≤ N) :
    (H : Set G) * (N : Set G) = (M : Set G) := by
  apply coe_mul_eq_of_relIndex_eq hHM hNM
  have hnot : ¬ 2 ∣ N.relIndex H := by
    intro hd
    exact (T.subtype hTH).not_dvd_index (hd.trans (index_dvd_of_le
      (show (T.subtype hTH : Subgroup H) ≤ N.subgroupOf H from fun _ hx => hTN hx)))
  have hpos : 0 < N.relIndex H := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hbound : N.relIndex H ≤ 3 := by
    simpa only [hi] using relIndex_le_of_le_right (H := N) hHM (by rw [hi]; decide)
  have hne1 : N.relIndex H ≠ 1 := fun he => hout (relIndex_eq_one.mp he)
  have hne2 : N.relIndex H ≠ 2 := by
    intro he
    apply hnot
    rw [he]
  omega

end Subgroup
