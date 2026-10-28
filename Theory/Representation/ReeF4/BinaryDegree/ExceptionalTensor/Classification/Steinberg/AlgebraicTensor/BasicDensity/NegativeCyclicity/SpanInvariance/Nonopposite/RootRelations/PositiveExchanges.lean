module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.PolynomialTransfer
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.RootRelations.IntegralB2BaseChange
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.FixedCoordinates.MatrixRelations.SignedBrackets

/-!
# Positive characteristic-two F₄ exchanges over the algebraically closed field

Integral operator brackets and polynomial descent give the actual root-curve
identities over the coefficient field. The closed carrier's injective inclusion
then gives these identities inside the algebraic group. For equal short roots
the lower-string coefficient is one for a short sum and two for a long sum;
the latter therefore commutes. A mixed pair has the two B₂ correction roots.

Source: Steinberg, Representations of Algebraic Groups (1963), §§2,4,10 and
11.1(1). The integral calculations extend the positive-root matrix exchanges
in ReeF4.Parabolics.RadicalCoordinates, without using finite-field evaluation
to assert a polynomial identity.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
noncomputable section
open ReeF4.Parabolics.RadicalCoordinates
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates.MatrixRelations
variable {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]

private def matrixToAmbient :
    (Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F)ˣ →*
      Variety.Point (F4Chevalley.Ambient F) where
  toFun A := generalLinearRepresentationPoint
    (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base))
    (Matrix.GeneralLinearGroup.toLin A)
  map_one' := by rw [map_one, generalLinearRepresentationPoint_one]
  map_mul' A B := by rw [map_mul, generalLinearRepresentationPoint_mul]

omit [CharP F 2] in
private lemma inclusion_root (r : F4Chevalley.Root) (a : F) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
      (algebraicRootElement r a) = matrixToAmbient (F4Chevalley.rootCurve r a) := by
  rw [algebraicRootElement, F4Chevalley.rootMorphism_inclusion_apply,
    F4Chevalley.ambientRootMorphism_apply]
  rfl

omit [CharP F 2] in
private lemma carrier_commute (r s : F4Chevalley.Root) (a b : F)
    (h : Commute (F4Chevalley.rootCurve r a) (F4Chevalley.rootCurve s b)) :
    Commute (algebraicRootElement r a) (algebraicRootElement s b) := by
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  simpa only [map_mul, inclusion_root] using
    congrArg (matrixToAmbient (F := F)) h.eq

omit [CharP F 2] in
private lemma carrier_exchange (r s t d : F4Chevalley.Root) (a b c q : F)
    (h : F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b =
      F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r a *
        F4Chevalley.rootCurve t c * F4Chevalley.rootCurve d q) :
    algebraicRootElement r a * algebraicRootElement s b =
      algebraicRootElement s b * algebraicRootElement r a *
        algebraicRootElement t c * algebraicRootElement d q := by
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  simpa only [map_mul, inclusion_root] using
    congrArg (matrixToAmbient (F := F)) h

private lemma short_short_chainBot (r s t : F4Chevalley.Root)
    (hr : IsShortRoot r) (hs : IsShortRoot s) (ht : IsShortRoot t)
    (he : t.val = r.val + s.val) : typeF4RootPairing.chainBotCoeff r s = 0 := by
  apply typeF4RootPairing.chainBotCoeff_eq_zero_iff.mpr
  right
  rintro ⟨u, hu⟩
  have hnorm : dot (s.val - r.val) (s.val - r.val) = 3 := by
    have hn := isShortRoot_norm t ht
    rw [he] at hn
    change (r.val + s.val) ⬝ᵥ (r.val + s.val) = 1 at hn
    simp only [add_dotProduct, dotProduct_add] at hn
    change (s.val - r.val) ⬝ᵥ (s.val - r.val) = 3
    simp only [sub_dotProduct, dotProduct_sub]
    change dot s.val s.val - dot r.val s.val -
      (dot s.val r.val - dot r.val r.val) = 3
    change dot r.val r.val + dot s.val r.val +
      (dot r.val s.val + dot s.val s.val) = 1 at hn
    rw [isShortRoot_norm r hr, isShortRoot_norm s hs] at hn ⊢
    linarith
  have hb : dot u.val u.val ≤ 2 := by
    by_cases h : IsLongRoot u
    · rw [isLongRoot_norm u h]
    · rw [isShortRoot_norm u h]; norm_num
  change u.val = s.val - r.val at hu
  rw [hu, hnorm] at hb
  norm_num at hb

omit [IsAlgClosed F] in
private lemma equal_exchange (r s t : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hrs : IsShortRoot r) (hss : IsShortRoot s)
    (ht : typeF4RootPairing.root t = typeF4RootPairing.root r + typeF4RootPairing.root s)
    (a b : F) :
    F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b =
      F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r a *
        F4Chevalley.rootCurve t ((typeF4RootPairing.chainBotCoeff r s + 1 : F)*a*b) := by
  obtain ⟨n, hn⟩ := EqualLength.integralOperators_bracket_mem_sum_line r s t hr hs ht
  obtain ⟨hrt, hst⟩ := EqualLength.integralOperators_commute_with_sum r s t hr hs
    (iff_of_false hrs hss) ht
  have hc : (n : F) = (typeF4RootPairing.chainBotCoeff r s + 1 : F) := by
    have hc := EqualLength.bracket_scalar_cast 0 r s t n ht hn
    have hi : (n : CoefficientField 0) =
        ((typeF4RootPairing.chainBotCoeff r s : ℤ) + 1 : ℤ) := by exact_mod_cast hc
    have hh := (CharP.intCast_eq_intCast (CoefficientField 0) 2).mp hi
    have hh' := (CharP.intCast_eq_intCast F 2).mpr hh
    exact_mod_cast hh'
  apply Units.ext
  simpa only [Units.val_mul, hc] using
    EqualLength.rootCurve_exchange_of_central_integral_bracket r s t n hn hrt hst a b

private lemma mixed_sum_dot_eq_neg_one (r s c : F4Chevalley.Root)
    (hr : IsLongRoot r) (hs : IsShortRoot s)
    (hc : c.val = r.val + s.val) : dot r.val s.val = -1 := by
  have hsr : dot s.val r.val = dot r.val s.val := by simp only [dot, mul_comm]
  have hn : dot c.val c.val = 3 + 2 * dot r.val s.val := by
    rw [hc]
    change (r.val + s.val) ⬝ᵥ (r.val + s.val) = _
    simp only [add_dotProduct, dotProduct_add]
    change dot r.val r.val + dot s.val r.val +
      (dot r.val s.val + dot s.val s.val) = _
    rw [isLongRoot_norm r hr, isShortRoot_norm s hs, hsr]
    ring
  have hp : (typeF4RootPairing.pairingIn ℤ s r : ℝ) = dot r.val s.val := by
    change algebraMap ℤ ℝ (typeF4RootPairing.pairingIn ℤ s r) = _
    rw [typeF4RootPairing.algebraMap_pairingIn,
      typeF4RootPairing_pairing, typeF4CorootScale_of_pair r hr, one_mul, hsr]
  by_cases hl : IsLongRoot c
  · rw [isLongRoot_norm c hl, ← hp] at hn
    have hi : 2 * typeF4RootPairing.pairingIn ℤ s r = (-1 : ℤ) := by
      exact_mod_cast (show 2 * (typeF4RootPairing.pairingIn ℤ s r : ℝ) = -1 by linarith)
    omega
  · rw [isShortRoot_norm c hl] at hn
    linarith

private lemma exists_second_mixed_root (r s : F4Chevalley.Root) (hs : IsShortRoot s)
    (hdot : dot r.val s.val = -1) :
    ∃ d : F4Chevalley.Root, d.val = r.val + (2 : ℝ) • s.val := by
  refine ⟨typeF4RootPairing.reflectionPerm s r, ?_⟩
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm s r) = _
  rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_of_not_pair s hs, hdot]
  simp only [typeF4RootPairing_root]
  module

omit [IsAlgClosed F] in
private lemma mixed_length_rootCurve_swaps (r s c d : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hl : IsLongRoot r) (hshort : IsShortRoot s)
    (hdot : dot r.val s.val = -1)
    (hc : c.val = r.val + s.val)
    (hd : d.val = r.val + (2 : ℝ) • s.val) (a b : F) :
    (F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r a =
      F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b *
        F4Chevalley.rootCurve c (a * b) * F4Chevalley.rootCurve d (a * b ^ 2)) ∧
    (F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b =
      F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r a *
        F4Chevalley.rootCurve c (a * b) * F4Chevalley.rootCurve d (a * b ^ 2)) := by
  have h := integralB2Relations_of_brackets r s c d hr hs hl hshort hdot hc hd
    (b2BracketRelations r s c d hr hs hl hshort hdot hc hd)
  have he := NonoppositeBaseChange.rootCurve_swap_of_integralB2 r s c d h a b
  refine ⟨he, ?_⟩
  have he' := congrArg (fun U => U * (F4Chevalley.rootCurve d (a * b ^ 2))⁻¹ *
    (F4Chevalley.rootCurve c (a * b))⁻¹) he
  simp only [mul_inv_cancel_right] at he'
  rw [F4Chevalley.rootCurve_inv, F4Chevalley.rootCurve_inv,
    CharTwo.neg_eq, CharTwo.neg_eq] at he'
  have hcomm := rootCurves_commute_of_operators_commute c d h.sum_top (a * b) (a * b ^ 2)
  simpa only [mul_assoc, hcomm.symm.eq] using he'.symm


/-- Positive root collection in the actual algebraic carrier, with a short
second root and with every correction parameter retained. -/
theorem positive_short_root_exchange (r s : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hss : IsShortRoot s) : ShortRootExchange (F := F) r s := by
  classical
  by_cases hsum : typeF4RootPairing.root r + typeF4RootPairing.root s ∈
      Set.range typeF4RootPairing.root
  · obtain ⟨t, ht⟩ := hsum
    by_cases hrl : IsLongRoot r
    · have htt : IsShortRoot t := by
        intro htl
        exact (WordRelations.ShortOperators.short_add_long s r t hss htl
          (ht.trans (add_comm _ _))).1 hrl
      have hd := mixed_sum_dot_eq_neg_one r s t hrl hss ht
      obtain ⟨d, hde⟩ := exists_second_mixed_root r s hss hd
      refine Or.inr ⟨t, d, 1, htt, ht, Or.inr ?_, ?_⟩
      · simpa only [typeF4RootPairing_root, two_smul] using hde
      · intro a b
        apply carrier_exchange
        simpa only [one_mul] using
          (mixed_length_rootCurve_swaps r s t d hr hs hrl hss hd ht hde a b).2
    · by_cases htl : IsLongRoot t
      · left
        intro a b
        apply carrier_commute
        have he := equal_exchange r s t hr hs hrl hss ht a b
        rw [WordRelations.ShortOperators.short_add_long_chainBot r s t hrl htl ht,
          Nat.cast_one, show (1 : F) + 1 = 0 from CharTwo.add_self_eq_zero _, zero_mul, zero_mul,
          F4Chevalley.rootCurve_zero, mul_one] at he
        exact he
      · refine Or.inr ⟨t, t, 0, htl, ht, Or.inl rfl, ?_⟩
        intro a b
        apply carrier_exchange
        simpa only [short_short_chainBot r s t hrl hss htl ht, Nat.cast_zero,
          zero_add, one_mul, zero_mul, F4Chevalley.rootCurve_zero, mul_one] using
          equal_exchange r s t hr hs hrl hss ht a b
  · left
    intro a b
    apply carrier_commute
    apply rootCurves_commute_of_operators_commute
    apply positive_operators_commute r s hr hs
    · intro he
      have hneg : typeF4RootPairing.root s = -typeF4RootPairing.root r := by
        change r.val + s.val = 0 at he
        exact eq_neg_of_add_eq_zero_right he
      have hheight := typeF4RootPairing_base.height_add_zsmul
        (i := r) (j := r) (k := s) (z := -2) (by rw [hneg]; module)
      have hp := (RootPairing.Base.isPos_iff _).mp hr
      have hq := (RootPairing.Base.isPos_iff _).mp hs
      norm_num [zsmul_eq_mul] at hheight
      omega
    · exact hsum

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.SpanInvariance.Nonopposite
