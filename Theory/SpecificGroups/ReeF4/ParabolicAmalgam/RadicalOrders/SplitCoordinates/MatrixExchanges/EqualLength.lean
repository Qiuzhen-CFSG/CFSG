module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.RootSums
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength.Geometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength.OperatorLine
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength.Exponential

/-!
# Equal-length root-sum exchanges for the actual F4 matrices

For positive equal-length roots r and s, put t = r+s. Root geometry makes
the integral t-operator commute with both inputs. The integral commutator
lies in its t-root line, and Cartan columns recover the lower-string
coefficient after specialization. The quadratic exponential identity over
an integer polynomial ring therefore proves the full root-curve exchange.

The correction word consists of the single root t. This also includes
short orthogonal inputs with a long sum: their coefficient is two and the
correction curve is the identity in characteristic two, including m=0.

Source: Chevalley collection underlying Aschbacher–Smith F.1.12(I)(5),
printed p.263 (PDF p.274) of `refs/quasithin.pdf`.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.Parabolics.RadicalCoordinates
noncomputable section

/-- The exact equal-length exchange, with the lower-string coefficient. -/
theorem rootCurve_exchange_of_equal_length_sum (m : ℕ) (r s t : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hlen : IsLongRoot r ↔ IsLongRoot s)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s)
    (a b : CoefficientField m) :
    (F4Chevalley.rootCurve r a).val * (F4Chevalley.rootCurve s b).val =
      (F4Chevalley.rootCurve s b).val * (F4Chevalley.rootCurve r a).val *
        (F4Chevalley.rootCurve t
          ((typeF4RootPairing.chainBotCoeff r s + 1 : CoefficientField m)*a*b)).val := by
  obtain ⟨n, hn⟩ := EqualLength.integralOperators_bracket_mem_sum_line r s t hr hs ht
  obtain ⟨hrt, hst⟩ := EqualLength.integralOperators_commute_with_sum r s t hr hs hlen ht
  have he := EqualLength.rootCurve_exchange_of_central_integral_bracket r s t n hn hrt hst a b
  rw [EqualLength.bracket_scalar_cast m r s t n ht hn] at he
  exact he

/-- The short orthogonal case has zero correction coefficient in characteristic two. -/
theorem rootCurve_commute_of_short_long_sum (m : ℕ) (r s t : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hrshort : IsShortRoot r) (htlong : IsLongRoot t)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s)
    (a b : CoefficientField m) :
    Commute (F4Chevalley.rootCurve r a) (F4Chevalley.rootCurve s b) := by
  have hsshort := (WordRelations.ShortOperators.short_add_long r s t hrshort htlong ht).1
  have hlen : IsLongRoot r ↔ IsLongRoot s := iff_of_false hrshort hsshort
  have he := rootCurve_exchange_of_equal_length_sum m r s t hr hs hlen ht a b
  rw [EqualLength.coefficient_eq_zero_of_short_long_sum m r s t hrshort htlong ht,
    zero_mul, zero_mul, F4Chevalley.rootCurve_zero, Units.val_one, mul_one] at he
  apply Units.ext
  exact he

/-- Equal-length positive roots with a root sum admit the required actual matrix
exchange, with a singleton correction word in their positive cone. -/
theorem matrixExchange_of_equal_length_sum (m : ℕ) (r s : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (_hne : r ≠ s) (hlen : IsLongRoot r ↔ IsLongRoot s)
    (hsum : typeF4RootPairing.root r + typeF4RootPairing.root s ∈
      Set.range typeF4RootPairing.root) :
    ∀ a b : CoefficientField m, MatrixExchange r s a b := by
  intro a b
  obtain ⟨t, ht⟩ := hsum
  refine ⟨[(t, (typeF4RootPairing.chainBotCoeff r s + 1 : CoefficientField m)*a*b)], ?_, ?_⟩
  · intro z hz
    obtain rfl := List.mem_singleton.mp hz
    exact positiveCone_of_add ht
  · simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      using rootCurve_exchange_of_equal_length_sum m r s t hr hs hlen ht a b

end
end ReeF4.Parabolics.RadicalCoordinates
