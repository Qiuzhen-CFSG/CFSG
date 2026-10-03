module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Card

/-!
# Exchange of two moved hyperplanes in a small two-module

Let a finite two-group `S` normalize an elementary abelian subgroup `A` of
order at most four contained in `S`. Two disjoint index-two subgroups of
`A`, each moved by `S`, are conjugate by an element of `S`. The conclusion
is equality of their literal ambient images under conjugation.

The index and movement assumptions force `A` to have order four and each
hyperplane to have order two. Restrict the normalizer conjugation action to
`S` on the actual subgroup `A`. Orbit parity gives a nonidentity fixed point.
A fixed nonidentity generator of an order-two subgroup would normalize that
subgroup, so the two moved generators are nonfixed. Together with the
identity and the nonidentity fixed point, they exhaust `A`. Any actor moving
the second generator must therefore send it to the first. Mapping their
order-two subgroups gives the required conjugacy.

This elementary orbit argument supplies the two-hyperplane exchange in
Stellmacher (6.3), journal p31, refs/latex/stellmacher-n-group.tex. The
source-specific normality and noncentrality inputs are handled by consumers;
this theorem retains only the displayed finite-group hypotheses.
-/

namespace Stellmacher

private theorem moved_points_conjugate_card_four
    {S A : Type*} [Group S] [Group A] [Finite S] [Finite A]
    [MulDistribMulAction S A] (hS : IsPGroup 2 S) (hA : Nat.card A = 4)
    (a b : A) (hab : a ≠ b)
    (ha : ¬ a ∈ FixedPoints.subgroup S A)
    (hb : ¬ b ∈ FixedPoints.subgroup S A) : ∃ s : S, s • b = a := by
  classical
  let _ := Fintype.ofFinite A
  have hfge : 2 ≤ Nat.card (FixedPoints.subgroup S A) := by
    have hp := hS.card_modEq_card_fixedPoints A
    change Nat.card A % 2 = Nat.card (FixedPoints.subgroup S A) % 2 at hp
    rw [hA] at hp
    have hpos : 0 < Nat.card (FixedPoints.subgroup S A) := Nat.card_pos
    omega
  have hfne : FixedPoints.subgroup S A ≠ ⊥ := by
    intro hbot
    have hc := Subgroup.card_eq_one.mpr hbot
    omega
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfne
  have hz1 : (z : A) ≠ 1 := fun he => hzne (Subtype.ext he)
  have ha1 : a ≠ 1 := by intro he; apply ha; rw [he]; exact Subgroup.one_mem _
  have hb1 : b ≠ 1 := by intro he; apply hb; rw [he]; exact Subgroup.one_mem _
  have haz : a ≠ (z : A) := by intro he; exact ha (he ▸ z.property)
  have hbz : b ≠ (z : A) := by intro he; exact hb (he ▸ z.property)
  have hcover : ({1, (z : A), a, b} : Finset A) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    have hAc : Fintype.card A = 4 := by simpa only [Nat.card_eq_fintype_card] using hA
    simp [hAc, hab, Ne.symm hz1,
      Ne.symm ha1, Ne.symm hb1, Ne.symm haz, Ne.symm hbz]
  obtain ⟨s, hs⟩ : ∃ s : S, s • b ≠ b := not_forall.mp hb
  have hs1 : s • b ≠ 1 := by
    intro he
    exact hb1 ((MulAction.injective s) (he.trans (smul_one s).symm))
  have hsz : s • b ≠ (z : A) := by
    intro he
    have hzfix : s • (z : A) = z := z.property s
    exact hbz ((MulAction.injective s) (he.trans hzfix.symm))
  have hi : s • b ∈ ({1, (z : A), a, b} : Finset A) := by
    rw [hcover]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  exact ⟨s, hi.resolve_left hs1 |>.resolve_left hsz |>.resolve_right hs⟩

private theorem normalizes_order_two_of_fixes_generator
    {G : Type*} [Group G] [Finite G] (N : Subgroup G)
    (hN : Nat.card N = 2) (n : N) (hne : n ≠ 1)
    (s : G) (hfix : s * (n : G) * s⁻¹ = n) :
    s ∈ Subgroup.normalizer (N : Set G) := by
  obtain ⟨t, _, ht⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro x ⟨m, hm, rfl⟩
    by_cases hm1 : m = 1
    · simp [hm1]
    have hmN : (⟨m, hm⟩ : N) ≠ 1 := fun he => hm1 (congrArg Subtype.val he)
    have hmn : m = (n : G) := congrArg Subtype.val ((ht ⟨m, hm⟩ hmN).trans (ht n hne).symm)
    change s * m * s⁻¹ ∈ N
    rw [hmn, hfix]
    exact n.property
  · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective]

/-- Two disjoint, moved index-two subgroups of the small module are conjugate in `S`. -/
public theorem two_moved_hyperplanes_conjugate
    {G : Type*} [Group G] [Finite G]
    (S A N1 N2 : Subgroup G) (hS : IsPGroup 2 S) [IsElementaryAbelian 2 A]
    (_hAS : A ≤ S) (hSA : S ≤ Subgroup.normalizer (A : Set G))
    (hcard : Nat.card A ≤ 4) (hN1 : N1 ≤ A) (hN2 : N2 ≤ A)
    (hidx1 : N1.relIndex A = 2) (hidx2 : N2.relIndex A = 2)
    (hinf : N1 ⊓ N2 = ⊥)
    (hmove1 : ¬ S ≤ Subgroup.normalizer (N1 : Set G))
    (hmove2 : ¬ S ≤ Subgroup.normalizer (N2 : Set G)) :
    ∃ s : G, s ∈ S ∧ N2.map (MulAut.conj s).toMonoidHom = N1 := by
  classical
  have hN2ne : N2 ≠ ⊥ := by
    intro he
    apply hmove2
    rw [he, Subgroup.normalizer_eq_top]
    exact le_top
  have hN2ge : 2 ≤ Nat.card N2 := by
    have hh := (Subgroup.one_lt_card_iff_ne_bot N2).mpr hN2ne
    omega
  have hmul2 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) N2 A bot_le hN2
  simp only [Subgroup.relIndex_bot_left, hidx2] at hmul2
  have hA4 : Nat.card A = 4 := by omega
  have hN2card : Nat.card N2 = 2 := by omega
  have hmul1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) N1 A bot_le hN1
  simp only [Subgroup.relIndex_bot_left, hidx1] at hmul1
  have hN1card : Nat.card N1 = 2 := by omega
  obtain ⟨n1, hn1, _⟩ := (Nat.card_eq_two_iff' (1 : N1)).mp hN1card
  obtain ⟨n2, hn2, hn2unique⟩ := (Nat.card_eq_two_iff' (1 : N2)).mp hN2card
  let a : A := ⟨n1, hN1 n1.property⟩
  let b : A := ⟨n2, hN2 n2.property⟩
  let ρ : S →* MulAut A := A.normalizerMonoidHom.comp (Subgroup.inclusion hSA)
  let _ : MulDistribMulAction S A := MulDistribMulAction.compHom A ρ
  have hab : a ≠ b := by
    intro he
    have hn : (n1 : G) ∈ N1 ⊓ N2 := ⟨n1.property, by
      rw [show (n1 : G) = (n2 : G) from congrArg Subtype.val he]
      exact n2.property⟩
    rw [hinf] at hn
    exact hn1 (Subtype.ext hn)
  have ha : ¬ a ∈ FixedPoints.subgroup S A := by
    intro hfix
    apply hmove1
    intro s hs
    apply normalizes_order_two_of_fixes_generator N1 hN1card n1 hn1 s
    exact congrArg Subtype.val (hfix (⟨s, hs⟩ : S))
  have hb : ¬ b ∈ FixedPoints.subgroup S A := by
    intro hfix
    apply hmove2
    intro s hs
    apply normalizes_order_two_of_fixes_generator N2 hN2card n2 hn2 s
    exact congrArg Subtype.val (hfix (⟨s, hs⟩ : S))
  obtain ⟨s, hs⟩ := moved_points_conjugate_card_four hS hA4 a b hab ha hb
  refine ⟨s, s.property, ?_⟩
  apply Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro x ⟨n, hn, rfl⟩
    by_cases hn1' : n = 1
    · simp [hn1']
    have hnN : (⟨n, hn⟩ : N2) ≠ 1 := fun he => hn1' (congrArg Subtype.val he)
    have hnn2 : n = (n2 : G) := congrArg Subtype.val (hn2unique ⟨n, hn⟩ hnN)
    change (s : G) * n * (s : G)⁻¹ ∈ N1
    rw [hnn2]
    have hconj : (s : G) * (n2 : G) * (s : G)⁻¹ = n1 := congrArg Subtype.val hs
    rw [hconj]
    exact n1.property
  · rw [Subgroup.card_map_of_injective (MulAut.conj (s : G)).injective, hN1card, hN2card]

end Stellmacher
