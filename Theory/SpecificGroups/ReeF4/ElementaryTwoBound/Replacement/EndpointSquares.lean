module

public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.Replacement.EndpointSquares.Collection
public import Theory.SpecificGroups.ReeF4.ElementaryTwoBound.RootCalculations.Support

/-!
# Endpoint squares in the Ree replacement section

For a positive word with no X₈ parameter, the split coordinates numbered 3
and 21 in its square are a·titsEnd(a) and b·titsEnd(b), where a and b are its
X₁ and X₇ main parameters. Here `halfFrobenius` is the source's θ, and
`titsEnd(a) = halfFrobenius(a)²`. Hence a square-one word has a = b = 0.
Its remaining factors lie in the literal subgroup D = Y₁X₂X₃X₄X₅X₆Y₇.

The calculation is uniform in the coefficient field, including m = 0. It
proves the square step in the first paragraph of GLS3 Lemma 3.3.9 without
assuming the source quotient decomposition C/C₀ ≅ X₁ × X₇.

Source: GLS3 Table 2.4, 2.4.5(d), 2.4.6 and Lemma 3.3.9,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex:645–658`.
-/

public section
noncomputable section
namespace ReeF4.ElementaryTwoBound.Replacement
open Parabolics.RadicalCoordinates.FixedCoordinates
open NormalizedRootCentralizers.CenterExponent
open NormalizedRootCentralizers.CenterExponent.OuterElimination

/-- The endpoint Suzuki square parameters vanish for a square-one C-word. -/
theorem endpoint_products_eq_zero (m : ℕ) (p : PositiveParameters m)
    (hp0 : p.pair 0 = 0) (hsquare : positiveWord m p ^ 2 = 1) :
    p.main 0 * titsEnd m (p.main 0) = 0 ∧
      p.main 2 * titsEnd m (p.main 2) = 0 := by
  have hs : splitWord m (parameters m p) ^ 2 = 1 := by
    simpa only [positiveWord_split] using hsquare
  have he := EndpointSquares.Collection.equations m (parameters m p)
    (by simp [parameters, hp0]) (by simp [parameters, hp0]) hs
  change p.main 0 * halfFrobenius m (p.main 0) ^ 2 = 0 ∧
    p.main 2 * halfFrobenius m (p.main 2) ^ 2 = 0 at he
  simpa only [halfFrobenius_sq] using he

private theorem eq_zero_of_tits_product (m : ℕ) (a : CoefficientField m)
    (h : a * titsEnd m a = 0) : a = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact (titsEnd m).injective (by simpa only [map_zero] using h)

/-- Both noncentral endpoint parameters vanish; the central parameters remain free. -/
theorem endpoint_main_eq_zero (m : ℕ) (p : PositiveParameters m)
    (hp0 : p.pair 0 = 0) (hsquare : positiveWord m p ^ 2 = 1) :
    p.main 0 = 0 ∧ p.main 2 = 0 := by
  obtain ⟨h₀, h₂⟩ := endpoint_products_eq_zero m p hp0 hsquare
  exact ⟨eq_zero_of_tits_product m _ h₀, eq_zero_of_tits_product m _ h₂⟩

/-- The square calculation in the actual fixed group, for the replacement
consumer. Only the absence of X₈ and the literal factorization are inputs. -/
theorem mem_D_of_positiveWord_sq (m : ℕ) (p : PositiveParameters m)
    (hp0 : p.pair 0 = 0) (x : Model m)
    (hx : toSplitGroup m x = positiveWord m p) (hsquare : x ^ 2 = 1) :
    x ∈ D m := by
  have hs : positiveWord m p ^ 2 = 1 := by
    simpa only [map_pow, map_one, hx] using congrArg (toSplitGroup m) hsquare
  obtain ⟨h₀, h₂⟩ := endpoint_main_eq_zero m p hp0 hs
  have he : RootCalculations.wordElement m p = x := by
    apply toSplitGroup_injective m
    rw [RootCalculations.wordElement_coe, hx]
  rw [← he]
  exact RootCalculations.wordElement_mem_D m p ⟨hp0, h₀, h₂⟩

end ReeF4.ElementaryTwoBound.Replacement
