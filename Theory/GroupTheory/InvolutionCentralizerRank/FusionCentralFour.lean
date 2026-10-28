module
public import Theory.GroupTheory.PGroup.RankTwoFour
public import Theory.GroupTheory.WeaklyClosedInvolutionSimple
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.InvolutionCentralizerRank

/-!
# Involution fusion when the Sylow center contains a four-group

In a finite simple centerless group, suppose every elementary binary subgroup
of a Sylow two-subgroup has order less than eight, and first omega of its
center has order four. Every Sylow involution is then central, and there are
exactly three. The Z-star theorem excludes an isolated ambient conjugacy
class among those three. An equivalence relation on three elements with no
singleton class has one class; Sylow conjugacy gives the ambient conclusion.

The final theorem supplies this branch directly from the original marked
involution-centralizer rank bound. This is the central-four branch of GLS,
*The Classification of the Finite Simple Groups*, volume 4, Chapter 1,
Lemma 4.10, with simplicity and trivial center discharging its Z-star premise.
The general rank reduction is GLS volume 2, Chapter D, Lemma 15.17(i).
-/

private theorem three_relation {X : Type*} [Finite X]
    (hcard : Nat.card X = 3) (R : X → X → Prop)
    (hrefl : ∀ x, R x x) (hsymm : ∀ {x y}, R x y → R y x)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hmate : ∀ x, ∃ y, R x y ∧ y ≠ x) (a b : X) : R a b := by
  classical
  let : Fintype X := Fintype.ofFinite X
  by_contra habR
  have hab : a ≠ b := fun h => habR (h ▸ hrefl a)
  obtain ⟨c, hacR, hca⟩ := hmate a
  obtain ⟨d, hbdR, hdb⟩ := hmate b
  have hac : a ≠ c := Ne.symm hca
  have hbc : b ≠ c := by
    intro h
    exact habR (h.symm ▸ hacR)
  have had : a ≠ d := by
    intro h
    exact habR (hsymm (h.symm ▸ hbdR))
  have hbd : b ≠ d := Ne.symm hdb
  have hcd : c ≠ d := by
    intro h
    exact habR (htrans (h ▸ hacR) (hsymm hbdR))
  have hle := Finset.card_le_card (Finset.subset_univ ({a, b, c, d} : Finset X))
  have hc : Fintype.card X = 3 := by rwa [← Nat.card_eq_fintype_card]
  simp [hab, hac, had, hbc, hbd, hcd, hc] at hle

namespace Sylow
open Subgroup

/-- All ambient involutions fuse in the central-four Sylow branch. -/
public theorem isConj_involutions_of_omega_center_card_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hZ : center G = ⊥)
    (hrank : ∀ A : Subgroup S, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  classical
  let I := {z : S // orderOf z = 2}
  have hI : Nat.card I = 3 := card_involutions_of_omega_center_card_four hrank hfour
  have hmate (z : I) : ∃ t : I, IsConj ((z : S) : G) ((t : S) : G) ∧ t ≠ z := by
    by_contra! h
    have hweak : ∀ t : S, IsConj ((z : S) : G) (t : G) → t = (z : S) := by
      intro t ht
      have htorder : orderOf t = 2 := by
        obtain ⟨g, hg⟩ := isConj_iff.mp ht
        rw [← Subgroup.orderOf_coe t, ← hg, ← MulAut.conj_apply,
          MulEquiv.orderOf_eq, Subgroup.orderOf_coe, z.property]
      exact congrArg Subtype.val (h ⟨t, htorder⟩ ht)
    have hzC : (z : S) ∈ center S :=
      mem_center_of_square_eq_one_of_omega_center_card_four hrank hfour
        (by simpa only [z.property] using pow_orderOf_eq_one (z : S))
    have hzG := S.weakly_closed_involution_mem_center_of_simple (z : S) z.property hzC hweak
    have hz1 : ((z : S) : G) = 1 := by simpa only [hZ, mem_bot] using hzG
    have horder : orderOf ((z : S) : G) = 2 := (Subgroup.orderOf_coe _).trans z.property
    simp [hz1] at horder
  obtain ⟨a, hxa⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  obtain ⟨b, hyb⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hy)
  have horder {w : G} {v : S} (hw : orderOf w = 2) (hwv : IsConj w (v : G)) :
      orderOf v = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hwv
    rw [← Subgroup.orderOf_coe v, ← hg, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hw]
  have hab := three_relation hI
    (fun v w : I => IsConj ((v : S) : G) ((w : S) : G))
    (fun _ => IsConj.refl _) (fun h => h.symm) (fun h₁ h₂ => h₁.trans h₂)
    hmate ⟨a, horder hx hxa⟩ ⟨b, horder hy hyb⟩
  exact hxa.trans (hab.trans hyb.symm)

/-- The central-four branch of the rank-two involution-centralizer theorem. -/
public theorem isConj_involutions_of_rank_two_centralizer_of_omega_center_card_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hZ : center G = ⊥)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (u : G) (hu : orderOf u = 2)
    (hC : primeRank 2 (centralizer {u}) ≤ 2)
    (hfour : Nat.card (omega₁ (center S) (p := 2)) = 4)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hrank := S.primeRank_two_le_two_of_involution_centralizer hno u hu hC
  apply S.isConj_involutions_of_omega_center_card_four hZ ?_ hfour hx hy
  intro A hA
  have hc := (primeRank_le_iff_elementary_card_le S).mp hrank A hA
  change Nat.card A ≤ 2 ^ 2 at hc
  omega

end Sylow
