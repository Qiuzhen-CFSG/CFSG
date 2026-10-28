module
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Coprime permutable subgroups and normal intersections

For subgroups X and Y of coprime orders in a finite group, equality of their
ordered set products survives replacing Y by its intersection with a normal
subgroup N. If X also meets N trivially, X normalizes that intersection.
This is ABG Chapter II, Section 8, Lemma 3(i),(ii), article p63 / PDF64,
and supplies a general group-theoretic tool for the later ABG arguments.

Starting with xy = y'x', project to G/N. The images of X and Y have coprime
orders, by divisibility of image orders, and hence are disjoint. As y maps
to one, the image of y' lies in both images, so y' belongs to N. This proves
one inclusion of ordered products; inversion proves the other. Under the
trivial-intersection hypothesis, equality of the images of x and x' implies
x = x', giving conjugation stability and thus the normalizer containment.
No mutual normalization or identification of a set product with a join is used.
-/

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

private theorem reorder_inf_normal (X Y N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime (Nat.card X) (Nat.card Y))
    (hperm : (X : Set G) * (Y : Set G) = (Y : Set G) * (X : Set G))
    {left right : G} (hleft : left ∈ X) (hright : right ∈ Y ⊓ N) :
    ∃ nextRight ∈ Y ⊓ N, ∃ nextLeft ∈ X, left * right = nextRight * nextLeft := by
  obtain ⟨nextRight, hnextRight, nextLeft, hnextLeft, heq⟩ :=
    Set.mem_mul.mp (hperm ▸ Set.mul_mem_mul hleft hright.1)
  let quotient := QuotientGroup.mk' N
  have hdisjoint : Disjoint (X.map quotient) (Y.map quotient) :=
    disjoint_of_coprime_natCard
      (hcop.of_dvd (X.card_map_dvd quotient) (Y.card_map_dvd quotient))
  have hright_one : quotient right = 1 := (QuotientGroup.eq_one_iff right).mpr hright.2
  have himage : quotient nextRight = quotient left * (quotient nextLeft)⁻¹ := by
    have hmapped := congrArg quotient heq
    simp only [map_mul, hright_one, mul_one] at hmapped
    exact eq_mul_inv_iff_mul_eq.mpr hmapped
  have hnextRight_one : quotient nextRight = 1 := by
    apply mem_bot.mp
    apply (disjoint_iff.mp hdisjoint).le
    refine ⟨?_, mem_map_of_mem quotient hnextRight⟩
    rw [himage]
    exact (X.map quotient).mul_mem (mem_map_of_mem quotient hleft)
      ((X.map quotient).inv_mem (mem_map_of_mem quotient hnextLeft))
  exact ⟨nextRight, ⟨hnextRight, (QuotientGroup.eq_one_iff nextRight).mp hnextRight_one⟩,
    nextLeft, hnextLeft, heq.symm⟩

public theorem permutable_inf_normal_and_normalizes [Finite G] (X Y N : Subgroup G) [N.Normal]
    (hcop : Nat.Coprime (Nat.card X) (Nat.card Y))
    (hperm : (X : Set G) * (Y : Set G) = (Y : Set G) * (X : Set G)) :
    (X : Set G) * (↑(Y ⊓ N) : Set G) = (↑(Y ⊓ N) : Set G) * (X : Set G) ∧
      (X ⊓ N = ⊥ → X ≤ normalizer (Y ⊓ N : Subgroup G)) := by
  have hreorder {left right : G} (hleft : left ∈ X) (hright : right ∈ Y ⊓ N) :=
    reorder_inf_normal X Y N hcop hperm hleft hright
  constructor
  · apply Set.Subset.antisymm
    · rintro element ⟨left, hleft, right, hright, rfl⟩
      obtain ⟨nextRight, hnextRight, nextLeft, hnextLeft, heq⟩ := hreorder hleft hright
      exact Set.mem_mul.mpr ⟨nextRight, hnextRight, nextLeft, hnextLeft, heq.symm⟩
    · rintro element ⟨right, hright, left, hleft, rfl⟩
      obtain ⟨nextRight, hnextRight, nextLeft, hnextLeft, heq⟩ :=
        hreorder (X.inv_mem hleft) ((Y ⊓ N).inv_mem hright)
      refine Set.mem_mul.mpr ⟨nextLeft⁻¹, X.inv_mem hnextLeft,
        nextRight⁻¹, (Y ⊓ N).inv_mem hnextRight, ?_⟩
      simpa only [mul_inv_rev, inv_inv] using (congrArg Inv.inv heq).symm
  · intro hinter
    apply le_normalizer_iff.mpr
    intro left hleft right hright
    obtain ⟨nextRight, hnextRight, nextLeft, hnextLeft, heq⟩ := hreorder hleft hright
    have hquot : QuotientGroup.mk' N left = QuotientGroup.mk' N nextLeft := by
      have hmapped := congrArg (QuotientGroup.mk' N) heq
      simpa only [map_mul,
        show QuotientGroup.mk' N right = 1 from (QuotientGroup.eq_one_iff right).mpr hright.2,
        show QuotientGroup.mk' N nextRight = 1 from
          (QuotientGroup.eq_one_iff nextRight).mpr hnextRight.2,
        mul_one, one_mul] using hmapped
    have hdiff : left * nextLeft⁻¹ ∈ X ⊓ N := by
      refine ⟨X.mul_mem hleft (X.inv_mem hnextLeft), ?_⟩
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (left * nextLeft⁻¹) = 1
      simp only [map_mul, map_inv, hquot, mul_inv_cancel]
    have hequal : left = nextLeft := mul_inv_eq_one.mp (mem_bot.mp (hinter ▸ hdiff))
    rw [heq, ← hequal, mul_inv_cancel_right]
    exact hnextRight

end Subgroup
