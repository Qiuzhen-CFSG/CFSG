module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.RootGeometry
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.SignedBrackets
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat.PositiveCollection.B2Exponential

/-!
# Mixed-length F4 root-sum matrix exchanges

If a long root `r` and a short root `s` have a root sum, their inner product
is -1: the norm of the sum and integrality of its pairing exclude -1/2.
Reflection in `s` then constructs the second root `r + 2s`. The proved signed
integral brackets and finite-exponential calculation give the actual B₂ swap,
with correction factors `x_{r+s}(ab)` and `x_{r+2s}(ab²)`.

The correction factors commute. In characteristic two each is an involution,
so the same correction word also swaps the opposite input order. The quadratic
identity comes from integral polynomial descent, and is valid over any field of characteristic two.
Both correction roots are strictly positive integral combinations of the inputs,
which gives precisely the `MatrixExchange` contract.

Adapted from `SplitCoordinates.MatrixExchanges.MixedLength`, without a
finite-carrier import.

Source: the Chevalley collection underlying Aschbacher–Smith F.1.12(I)(5),
`refs/quasithin.pdf`, printed p.263 (PDF p.274). This module supplies the
mixed-length matrix calculation used in that collection.
-/

public section

open ReeF4 Theory.AlgebraicGroup StandardRootSystem
open scoped Matrix
namespace Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices

noncomputable section

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

private lemma mixed_length_rootCurve_swaps {K : Type*} [Field K] [CharP K 2] (r s c d : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hl : IsLongRoot r) (hshort : IsShortRoot s)
    (hdot : dot r.val s.val = -1)
    (hc : c.val = r.val + s.val)
    (hd : d.val = r.val + (2 : ℝ) • s.val) (a b : K) :
    (F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r a =
      F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b *
        F4Chevalley.rootCurve c (a * b) * F4Chevalley.rootCurve d (a * b ^ 2)) ∧
    (F4Chevalley.rootCurve r a * F4Chevalley.rootCurve s b =
      F4Chevalley.rootCurve s b * F4Chevalley.rootCurve r a *
        F4Chevalley.rootCurve c (a * b) * F4Chevalley.rootCurve d (a * b ^ 2)) := by
  have h := integralB2Relations_of_brackets r s c d hr hs hl hshort hdot hc hd
    (b2BracketRelations r s c d hr hs hl hshort hdot hc hd)
  have he := rootCurve_swap_of_integralB2 r s c d h a b
  refine ⟨he, ?_⟩
  have he' := congrArg (fun U => U * (F4Chevalley.rootCurve d (a * b ^ 2))⁻¹ *
    (F4Chevalley.rootCurve c (a * b))⁻¹) he
  simp only [mul_inv_cancel_right] at he'
  rw [F4Chevalley.rootCurve_inv, F4Chevalley.rootCurve_inv,
    CharTwo.neg_eq, CharTwo.neg_eq] at he'
  have hcomm := rootCurve_commute_of_integralOperators c d h.sum_top (a * b) (a * b ^ 2)
  simpa only [mul_assoc, hcomm.symm.eq] using he'.symm

/-- Positive F4 roots of different geometric lengths whose sum is a root admit
an actual matrix exchange with two correction roots in their positive cone.
The formula holds over every Ree coefficient field, over any field of characteristic two. -/
theorem matrixExchange_of_mixed_length_sum {K : Type*} [Field K] [CharP K 2] (r s : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (_hrs : r ≠ s) (hlen : ¬(IsLongRoot r ↔ IsLongRoot s))
    (hsum : typeF4RootPairing.root r + typeF4RootPairing.root s ∈
      Set.range typeF4RootPairing.root) :
    ∀ a b : K, MatrixExchange r s a b := by
  classical
  obtain ⟨c, hc⟩ := hsum
  change c.val = r.val + s.val at hc
  by_cases hl : IsLongRoot r
  · have hshort : IsShortRoot s := by
      intro hsl
      exact hlen ⟨fun _ => hsl, fun _ => hl⟩
    have hdot := mixed_sum_dot_eq_neg_one r s c hl hshort hc
    obtain ⟨d, hd⟩ := exists_second_mixed_root r s hshort hdot
    intro a b
    refine ⟨[(c, a * b), (d, a * b ^ 2)], ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact positiveCone_of_add hc
      · apply positiveCone_of_add_two
        simpa only [typeF4RootPairing_root, two_smul] using hd
    · simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, mul_assoc, Units.val_mul] using
        congrArg Units.val ((mixed_length_rootCurve_swaps r s c d hr hs hl hshort hdot hc hd a b).2)
  · have hsl : IsLongRoot s := by
      by_contra h
      exact hlen ⟨fun h' => (hl h').elim, fun h' => (h h').elim⟩
    have hc' : c.val = s.val + r.val := hc.trans (add_comm _ _)
    have hdot := mixed_sum_dot_eq_neg_one s r c hsl hl hc'
    obtain ⟨d, hd⟩ := exists_second_mixed_root s r hl hdot
    intro a b
    refine ⟨[(c, b * a), (d, b * a ^ 2)], ?_, ?_⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact positiveCone_of_add hc
      · apply positiveCone_of_two_add
        simpa only [typeF4RootPairing_root, two_smul, add_comm] using hd
    · simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
        mul_one, mul_assoc, Units.val_mul] using
        congrArg Units.val ((mixed_length_rootCurve_swaps s r c d hs hr hsl hl hdot hc' hd b a).1)

end
end Theory.AlgebraicGroup.F4Chevalley.DenseParameters.CarrierBruhat.CollectionMatrices
