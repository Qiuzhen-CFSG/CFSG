module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.Commuting
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# The central sum root for equal-length F4 inputs

If r and s have equal squared length and t = r+s is a root, then
|r+t|² = |r|² + 2|t|² ≥ 3, and likewise for s+t. These are outside the
F4 root system, whose squared lengths are one and two. Consequently both
integral operators commute with the sum-root operator. The short orthogonal
case is retained: its sum is long and its lower-string coefficient is one.

Source: F4 root geometry in the Chevalley collection underlying
Aschbacher–Smith F.1.12(I)(5), printed p.263 of `refs/quasithin.pdf`.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
open scoped Matrix
namespace ReeF4.Parabolics.RadicalCoordinates.EqualLength
noncomputable section

private lemma root_norm_bounds (r : F4Chevalley.Root) :
    1 ≤ dot r.val r.val ∧ dot r.val r.val ≤ 2 := by
  by_cases hr : IsLongRoot r
  · rw [isLongRoot_norm r hr]; norm_num
  · rw [isShortRoot_norm r hr]; norm_num

private lemma norm_eq_of_same_length (r s : F4Chevalley.Root)
    (h : IsLongRoot r ↔ IsLongRoot s) : dot r.val r.val = dot s.val s.val := by
  by_cases hr : IsLongRoot r
  · rw [isLongRoot_norm r hr, isLongRoot_norm s (h.mp hr)]
  · rw [isShortRoot_norm r hr, isShortRoot_norm s (mt h.mpr hr)]

private lemma dot_add_self (x y : Vec 4) :
    dot (x + y) (x + y) = dot x x + 2 * dot x y + dot y y := by
  change (x + y) ⬝ᵥ (x + y) = x ⬝ᵥ x + 2 * (x ⬝ᵥ y) + y ⬝ᵥ y
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm y x]
  ring

private lemma norm_add_sum (r s t : F4Chevalley.Root)
    (hlen : IsLongRoot r ↔ IsLongRoot s)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    2 < dot (r.val + t.val) (r.val + t.val) := by
  change t.val = r.val + s.val at ht
  have heq := norm_eq_of_same_length r s hlen
  have hs := dot_add_self r.val s.val
  rw [← ht] at hs
  have hrt : dot r.val t.val = dot r.val r.val + dot r.val s.val := by
    rw [ht]
    exact dotProduct_add _ _ _
  rw [dot_add_self, hrt]
  linarith [(root_norm_bounds r).1, (root_norm_bounds t).1]

private lemma absent_of_large_norm (x : Vec 4) (hx : 2 < dot x x) :
    x ≠ 0 ∧ x ∉ Set.range typeF4RootPairing.root := by
  constructor
  · intro h
    subst x
    norm_num [dot] at hx
  · rintro ⟨t, ht⟩
    have hb := (root_norm_bounds t).2
    change t.val = x at ht
    rw [ht] at hb
    linarith

/-- Equal-length inputs have no further root sums with their sum root. -/
theorem no_further_sum (r s t : F4Chevalley.Root)
    (hlen : IsLongRoot r ↔ IsLongRoot s)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    (typeF4RootPairing.root r + typeF4RootPairing.root t ≠ 0 ∧
      typeF4RootPairing.root r + typeF4RootPairing.root t ∉ Set.range typeF4RootPairing.root) ∧
    (typeF4RootPairing.root s + typeF4RootPairing.root t ≠ 0 ∧
      typeF4RootPairing.root s + typeF4RootPairing.root t ∉ Set.range typeF4RootPairing.root) :=
  ⟨absent_of_large_norm _ (norm_add_sum r s t hlen ht),
    absent_of_large_norm _ (norm_add_sum s r t hlen.symm (ht.trans (add_comm _ _)))⟩

/-- Both positive integral operators commute with the sum-root operator. -/
theorem integralOperators_commute_with_sum (r s t : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hlen : IsLongRoot r ↔ IsLongRoot s)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    Commute (F4Chevalley.integralOperators.rootOperator r)
      (F4Chevalley.integralOperators.rootOperator t) ∧
    Commute (F4Chevalley.integralOperators.rootOperator s)
      (F4Chevalley.integralOperators.rootOperator t) := by
  obtain ⟨hrn, hsn⟩ := no_further_sum r s t hlen ht
  exact ⟨integralOperators_commute_of_no_sum r t hr (hr.add hs ht) hrn.1 hrn.2,
    integralOperators_commute_of_no_sum s t hs (hr.add hs ht) hsn.1 hsn.2⟩

/-- The correction coefficient vanishes for short roots with a long sum. -/
theorem coefficient_eq_zero_of_short_long_sum (m : ℕ) (r s t : F4Chevalley.Root)
    (hr : IsShortRoot r) (htl : IsLongRoot t)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s) :
    (typeF4RootPairing.chainBotCoeff r s + 1 : CoefficientField m) = 0 := by
  rw [WordRelations.ShortOperators.short_add_long_chainBot r s t hr htl ht]
  exact CharTwo.add_self_eq_zero (1 : CoefficientField m)

end
end ReeF4.Parabolics.RadicalCoordinates.EqualLength
