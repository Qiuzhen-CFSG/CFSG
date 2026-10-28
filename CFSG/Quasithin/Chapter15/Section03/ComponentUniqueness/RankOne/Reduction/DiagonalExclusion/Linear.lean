module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.DiagonalExclusion.Linear.Borel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.CubicBorelFixer
public import Theory.NumberTheory.BinaryTorusParity

/-!
# Excluding the linear diagonal branches of 15.3.43

The Borel over S ∩ L is invariant under Y₊S and has characteristic two, hence
lies in M ∩ I by 15.3.33(1). Lift an order-three element of its projective
image through the two-core. The theta identity puts this lift in Y₊ ∩ L.

Here is an equivalent contradiction to the source's three-rank argument,
using the full index-three assertion in (a). Since |Y₊:O₂(Y₊)| = 3, a normal
subgroup of Y₊ containing an order-three element has index a power of two.
The subgroup Y₊ ∩ L is normal in Y₊, so it contains every order-three element
of Y₊, including the supplied diagonal actor. An element of L acts innerly
on its quotient, contradicting the compatible outer GL₃ action.

This retains both the actual quotient equivalence and its compatible matrix.
In particular, no splitting of a central two-cover of PSL₃(4) is needed, nor
is any rank-two hypothesis on Y₊ used. The intrinsic cubic-Borel rigidity
calculation supplies a cubic element; it uses no Chapter 15 conclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the paragraph
between 15.3.43(d) and (e), printed p.1139; compare 15.3.37 on p.1135.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
variable {H : Type*} [Group H] [Finite H]

/-- The index version of Sylow conjugacy in a group of order 2ᵏ · 3. -/
private theorem cubic_mem_normal_of_twoCore_index_three
    (hindex : (pCore 2 H).index = 3) (N : Subgroup H) [N.Normal]
    {x : H} (hx : x ∈ N) (hx3 : orderOf x = 3)
    {y : H} (hy3 : orderOf y = 3) : y ∈ N := by
  have hd : 3 ∣ Nat.card N := by
    have ho : orderOf (⟨x, hx⟩ : N) = 3 := (Subgroup.orderOf_mk _ _).trans hx3
    exact ho ▸ orderOf_dvd_natCard (⟨x, hx⟩ : N)
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hcard : Nat.card H = 2 ^ k * 3 := by
    rw [← (pCore 2 H).card_mul_index, hk, hindex]
  obtain ⟨a, ha⟩ := hd
  have hi : N.index ∣ 2 ^ k := by
    refine ⟨a, ?_⟩
    have hh := N.card_mul_index
    rw [ha, hcard] at hh
    nlinarith only [hh]
  have hcop : Nat.Coprime 3 N.index :=
    ((by decide : Nat.Coprime 3 2).pow_right k).of_dvd_right hi
  let q := QuotientGroup.mk' N
  have hd3 : orderOf (q y) ∣ 3 := by
    rw [← hy3]
    exact orderOf_map_dvd q y
  have hdi : orderOf (q y) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard (q y)
  exact (QuotientGroup.eq_one_iff y).mp
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd3 hdi))

open Candidates.LinearCore Candidates.LinearCore.MatrixImage
variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L : Subgroup G}

/-- Exclude the even-degree linear quotient with its actual compatible actor.
The statement also allows a nontrivial two-core in L. -/
theorem LocalSetup.not_linear_diagonal_even (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S) {n : ℕ} (hn : 0 < n) (heven : Even n)
    {y : G} (hy : y ∈ Yplus) (hy3 : orderOf y = 3) :
    ¬ Candidates.LinearDiagonalOnTwoQuotient L y (2 ^ n) := by
  intro hdiag
  obtain ⟨F, hF, hfin, hcard, e, α, d₀, hc, ho, he⟩ := hdiag
  obtain ⟨Q, hQ⟩ := h.sylow
  obtain ⟨P, hP⟩ := quotient_sylow h.component_le h.component.1 Q hQ e
  obtain ⟨_, _, hBM⟩ := h.linear_borel horbit hn heven hcard e
  have hex : ∃ z : PSL(3,F), z ∈ normalizer (P : Set PSL(3,F)) ∧ orderOf z = 3 := by
    classical
    by_contra hnone
    have hfix : Matrix.PSL3.OuterSolvable.linearConj F d₀ = 1 := by
      apply Matrix.PSL3.LinearThree.CubicBorel.eq_one_of_fixes_sylowNormalizer_cubics
        hn heven hcard P
      intro z hz hz3
      exact (hnone ⟨z, hz, hz3⟩).elim
    exact ho (hfix ▸ (MulAut.innerSubgroup PSL(3,F)).one_mem)
  obtain ⟨z, hz, hz3⟩ := hex
  obtain ⟨l, hl, hl3⟩ := order_three_lift e z hz3
  have hlB : (l : G) ∈ L ⊓ normalizer (S ⊓ L : Subgroup G) := by
    rw [← h.linear_borel_preimage e P hP]
    exact mem_map_of_mem L.subtype (show quotientMap e l ∈ normalizer
      (P : Set PSL(3,F)) from hl ▸ hz)
  have hlG3 : orderOf (l : G) = 3 := (Subgroup.orderOf_coe l).trans hl3
  have hlY : (l : G) ∈ Yplus :=
    h.theta_eq ▸ subset_closure ⟨hBM hlB, hlG3⟩
  let N := L.subgroupOf Yplus
  let : N.Normal := normal_subgroupOf_of_le_normalizer h.yplus_normalizes
  have hyL : y ∈ L := cubic_mem_normal_of_twoCore_index_three h.index N
    (x := (⟨l, hlY⟩ : Yplus)) l.property
    ((Subgroup.orderOf_mk _ _).trans hlG3)
    (y := (⟨y, hy⟩ : Yplus)) ((Subgroup.orderOf_mk _ _).trans hy3)
  have hinner : Matrix.PSL3.OuterSolvable.linearConj F d₀ =
      MulAut.conj (quotientMap e ⟨y, hyL⟩) := by
    rw [← quotientAction_eq_of_compatible h.yplus_normalizes e (⟨y, hy⟩ : Yplus)
      α _ hc he, quotientAction_on_component h.yplus_normalizes e _ hyL]
  exact ho (hinner ▸ ⟨_, rfl⟩)

/-- The PSL₃(4) quotient branch, retaining its entire central two-cover. -/
theorem LocalSetup.not_linear_diagonal_four (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S) {y : G} (hy : y ∈ Yplus) (hy3 : orderOf y = 3) :
    ¬ Candidates.LinearDiagonalOnTwoQuotient L y 4 :=
  h.not_linear_diagonal_even horbit (n := 2) (by decide) (by decide) hy hy3

/-- Both literal linear alternatives between source 15.3.43(d) and (e) are impossible. -/
theorem LocalSetup.linear_diagonal_impossible (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S) {y : G} (hy : y ∈ Yplus) (hy3 : orderOf y = 3)
    (halt : (∃ n : ℕ, 0 < n ∧ 2 ^ n % 3 = 1 ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      Candidates.LinearDiagonalOnTwoQuotient L y (2 ^ n)) ∨
      Candidates.LinearDiagonalOnTwoQuotient L y 4) : False := by
  rcases halt with ⟨n, hn, hmod, _, hdiag⟩ | hdiag
  · have heven : Even n := by
      rw [Nat.even_iff]
      have hp := Nat.BinaryTorusParity.two_pow_mod_three n
      split_ifs at hp <;> omega
    exact h.not_linear_diagonal_even horbit hn heven hy hy3 hdiag
  · exact h.not_linear_diagonal_four horbit hy hy3 hdiag

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
