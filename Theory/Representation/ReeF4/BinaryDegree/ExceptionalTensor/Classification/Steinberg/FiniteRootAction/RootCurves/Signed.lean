module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves.Positive
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition

/-!
# Both signs of the genuine Ree short-root curves

Conjugate the positive curves by the already proved fixed opposition element.
Its native matrix conjugation negates every root and preserves its parameter.
Thus the factor order and strict degree separation hold in both chambers.

Source: GLS3 2.3.4–8 and Table 2.4; Steinberg (1963), Section 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves

open Theory.AlgebraicGroup StandardRootSystem
open LocalBlockInput.PairNormalization
local instance rootNegSigned : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def oppositeWord {m : ℕ} (w : RootWord m) : RootWord m :=
  w.map fun p => (-p.1, p.2)

private theorem oppositeWord_split {m : ℕ} (w : RootWord m) :
    splitWord (oppositeWord w) =
      splitOpposition m * splitWord w * (splitOpposition m)⁻¹ := by
  induction w with
  | nil => simp [oppositeWord, splitWord]
  | cons p w ih =>
    simp only [oppositeWord, List.map_cons, splitWord, List.prod_cons] at ih ⊢
    rw [ih, ← splitOpposition_conj_root]
    group

private theorem oppositeWord_support {m : ℕ} {r : F4Chevalley.Root} {w : RootWord m}
    (h : HigherSupport true r w) : HigherSupport false (-r) (oppositeWord w) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  obtain ⟨hqpos, hqdeg⟩ := h q hq
  simp only [Bool.false_eq_true, if_false, neg_neg, signedDegree, rootDegree_neg,
    if_true] at hqdeg ⊢
  exact ⟨hqpos, hqdeg⟩

private def modelOpposition (m : ℕ) : Model m :=
  (canonicalLocalBlockInput m).modelEquiv (opposition (canonicalLocalBlockInput m))

private theorem modelOpposition_split (m : ℕ) :
    toSplitGroup m (modelOpposition m) = splitOpposition m := by
  rw [toSplitGroup_apply, modelOpposition, LocalBlockInput.modelEquiv_coe]
  rfl

/-- A short root in either chamber has a genuine finite Ree curve with that
root factor marked and every other factor strictly higher in signed degree. -/
theorem exists_signed_root_curve (m : ℕ) (positive : Bool) {r : F4Chevalley.Root}
    (hr : if positive then typeF4RootPairing_base.IsPos r
      else typeF4RootPairing_base.IsPos (-r))
    (hs : IsShortRoot r) (t : CoefficientField m) :
    ∃ (g : Model m) (left right : RootWord m),
      HigherSupport positive r (left ++ right) ∧
      toSplitGroup m g = splitWord left * rootGeneratorInGroup m r t * splitWord right := by
  cases positive
  · have hs' : IsShortRoot (-r) := by
      simpa only [IsShortRoot, isLongRoot_neg_iff] using hs
    obtain ⟨g, left, right, hhigh, hg⟩ := exists_positive_root_curve m hr hs' t
    refine ⟨modelOpposition m * g * (modelOpposition m)⁻¹,
      oppositeWord left, oppositeWord right, ?_, ?_⟩
    · have hh := oppositeWord_support hhigh
      simpa only [oppositeWord, List.map_append, neg_neg] using hh
    · simp only [map_mul, map_inv, modelOpposition_split, hg,
        oppositeWord_split]
      have hconj := splitOpposition_conj_root m (-r) t
      simp only [neg_neg] at hconj
      rw [← hconj]
      group
  · exact exists_positive_root_curve m hr hs t

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves
