module
public import Theory.GroupTheory.InvolutionFixedLineFour
public import Theory.GroupTheory.InvolutionFixedLineDihedral
public import Mathlib.Algebra.Group.Conj

/-!
# A central involution fixed line and nonfusion

Let Q be a normal two-subgroup, let i be a central involution, and suppose
that the fixed subgroup of an involution t on Q is exactly ⟨i⟩. If t and ti
are not conjugate, then Q itself is ⟨i⟩.

When t lies outside Q and Q is larger than ⟨i⟩, the normalizer condition
constructs a t-invariant subgroup of order four in Q. The fixed-line
calculation in that subgroup conjugates t to it, contradicting nonfusion.
If t lies in Q, it belongs to the central fixed line and fixes all of Q.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
manuscript of 1 March 2004, proof of 2.5.19, printed p.562, applied to
Q = O₂(Kᵢ C_S(i)).
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem mem_zpowers_of_order_two {i x : G} (hi : orderOf i = 2)
    (hx : x ∈ zpowers i) : x = 1 ∨ x = i := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hi] at hx
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

/-- Nonfusion with the product by the central fixed involution collapses
an invariant normal two-subgroup to its fixed line. -/
public theorem eq_zpowers_of_fixed_central_involution_of_nonfusion
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (t i : G) (ht : t ^ 2 = 1) (hi : orderOf i = 2)
    (hiZ : i ∈ center G)
    (hfixed : Q ⊓ centralizer ({t} : Set G) = zpowers i)
    (hnonfusion : ¬ IsConj t (t * i)) : Q = zpowers i := by
  have hiQ : i ∈ Q := (show i ∈ Q ⊓ centralizer ({t} : Set G) from
    hfixed.symm ▸ mem_zpowers i).1
  have hiC : i ∈ centralizer ({t} : Set G) :=
    (show i ∈ Q ⊓ centralizer ({t} : Set G) from
      hfixed.symm ▸ mem_zpowers i).2
  have hlineQ : zpowers i ≤ Q := zpowers_le.mpr hiQ
  by_cases htQ : t ∈ Q
  · have htline : t ∈ zpowers i := hfixed ▸
      (show t ∈ Q ⊓ centralizer ({t} : Set G) from
        ⟨htQ, mem_centralizer_singleton_iff.mpr rfl⟩)
    have htZ : t ∈ center G := by
      rcases mem_zpowers_of_order_two hi htline with rfl | rfl
      · exact one_mem _
      · exact hiZ
    have hQC : Q ≤ centralizer ({t} : Set G) := by
      intro q _
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp htZ q)
    simpa only [inf_eq_left.mpr hQC] using hfixed
  · by_contra hneq
    have hQcard : 2 < Nat.card Q := by
      by_contra hsmall
      apply hneq
      exact (eq_of_le_of_card_ge hlineQ (by
        rw [Nat.card_zpowers, hi]
        omega)).symm
    have htorder : orderOf t = 2 := orderOf_eq_prime ht
      (fun h => htQ (h ▸ Q.one_mem))
    have hit : Commute i t := mem_centralizer_singleton_iff.mp hiC
    have htN : t ∈ normalizer (Q : Set G) := by
      rw [normalizer_eq_top]
      trivial
    obtain ⟨X, hXQ, hXcard, hiX, htX⟩ :=
      exists_invariant_order_four_subgroup Q hQ hQcard hiQ hi htorder hit htQ htN hfixed
    have hXfixed : X ⊓ centralizer ({t} : Set G) = zpowers i := by
      apply le_antisymm
      · exact (inf_le_inf_right _ hXQ).trans hfixed.le
      · exact zpowers_le.mpr ⟨hiX, hiC⟩
    obtain ⟨_, x, _, hconj, _⟩ :=
      exists_marked_dihedral_extension_of_involution_fixed_line X hXcard i t hiX hi
        htorder (fun h => htQ (hXQ h)) htX hXfixed
    apply hnonfusion
    apply isConj_iff.mpr
    exact ⟨x, hconj.trans hit.eq⟩
end Subgroup
