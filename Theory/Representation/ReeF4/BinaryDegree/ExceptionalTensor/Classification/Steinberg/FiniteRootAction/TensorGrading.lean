module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.PositiveExpansion

/-!
# Actual finite Ree curves on the ordinary tensor filtration

A positive short-root curve in the original Ree group factors into its
marked short root and roots of strictly larger degree. The marked root has
ordinary Frobenius leading terms in the individual tensor factors. All the
other root factors, and all products of two nonconstant terms, lower the
unweighted tensor deficit by at least one extra integer layer.

This is the finite source action identity needed by the positive filtered
irreducibility argument. It assumes neither a finite classification nor an
abstract local action certificate.

Source: Steinberg (1963), Section 12; GLS3 Theorem 2.8.2.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup StandardRootSystem
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

private theorem higherWord_hasLeadingTerm (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ)
    (p : ∀ i : ℕ, AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (η : ℕ → EndNode.Weight) (f : CoefficientField m →+* F)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r)
    (w : RootCurves.RootWord m) (hw : RootCurves.HigherSupport true r w) :
    HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
      (ordinaryPointAction m B n (RootCurves.algebraicWord f w)) 0 := by
  induction w with
  | nil =>
    simp only [RootCurves.algebraicWord, List.map_nil, List.prod_nil, map_one,
      HasLeadingTerm, sub_self]
    exact ⟨(loweringOperators _ _).zero_mem, (loweringOperators _ _).zero_mem⟩
  | cons a w ih =>
    have ha := hw a List.mem_cons_self
    have ha' : typeF4RootPairing_base.IsPos a.1 ∧
        RootCurves.rootDegree r < RootCurves.rootDegree a.1 := by
      simpa only [RootCurves.signedDegree, if_true] using ha
    have hd : weightDegree (rootWeight r) < weightDegree (rootWeight a.1) := by
      have hd' := ha'.2
      rw [← weightDegree_rootWeight, ← weightDegree_rootWeight] at hd'
      exact_mod_cast hd'
    have hroot := (ordinaryPointAction_root_hasLeadingTerm m B n p η a.1 ha'.1 (f a.2)).sub_one
      (tensorFiltration_mono m B η n)
    have hroot' : HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
        (ordinaryPointAction m B n (algebraicRootElement a.1 (f a.2))) 0 := by
      refine ⟨(loweringOperators _ _).zero_mem, ?_⟩
      simpa only [sub_zero] using loweringOperators_antitone _ (tensorFiltration_mono m B η n)
        (show weightDegree (rootWeight r) + 1 ≤ weightDegree (rootWeight a.1) by omega) hroot
    have htail := ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))
    simpa only [RootCurves.algebraicWord, List.map_cons, List.prod_cons, map_mul, add_zero] using
      hroot'.mul (tensorFiltration_mono m B η n) (weightDegree_rootWeight_pos hr) htail

/-- A genuine positive finite Ree curve has the actual ordinary Frobenius
leading operators, with a remainder one integer layer deeper. -/
theorem exists_positive_ordinary_leading (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ)
    (p : ∀ i : ℕ, AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (η : ℕ → EndNode.Weight) (f : CoefficientField m →+* F)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r)
    (hs : IsShortRoot r) (t : CoefficientField m) :
    ∃ g : Model m, HasLeadingTerm (tensorFiltration m B η n) (weightDegree (rootWeight r))
      (ordinaryAction m B f n g)
      (((List.range n).map fun i => (f t) ^ (2 ^ i) •
        coordinateMap m B n i ((p i).coeff r 1)).sum) := by
  obtain ⟨g, left, right, hhigh, hg⟩ :=
    RootCurves.exists_algebraic_root_curve m f true hr hs t
  refine ⟨g, ?_⟩
  have hl := higherWord_hasLeadingTerm m B n p η f r hr left
    (fun a ha => hhigh a (List.mem_append_left _ ha))
  have hh := ordinaryPointAction_root_hasLeadingTerm m B n p η r hr (f t)
  have hrr := higherWord_hasLeadingTerm m B n p η f r hr right
    (fun a ha => hhigh a (List.mem_append_right _ ha))
  have h := (hl.mul (tensorFiltration_mono m B η n) (weightDegree_rootWeight_pos hr) hh).mul
    (tensorFiltration_mono m B η n) (weightDegree_rootWeight_pos hr) hrr
  have he : ordinaryAction m B f n g = ordinaryPointAction m B n (modelEmbedding f g) :=
    (DFunLike.congr_fun (ordinaryPointAction_restrict m B f n) g).symm
  rw [he, hg, map_mul, map_mul]
  simpa only [zero_add, add_zero] using h

/-- Pointwise form consumed by the finite coefficient-separation argument. -/
theorem exists_positive_ordinary_remainder (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (n : ℕ)
    (p : ∀ i : ℕ, AlgebraicTensor.RootExpansion (basicFactor m B i).action)
    (η : ℕ → EndNode.Weight) (f : CoefficientField m →+* F)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r)
    (hs : IsShortRoot r) (t : CoefficientField m) :
    ∃ g : Model m, ∀ k v, v ∈ tensorFiltration m B η n k →
      ordinaryAction m B f n g v - v -
        (((List.range n).map fun i => (f t) ^ (2 ^ i) •
          coordinateMap m B n i ((p i).coeff r 1)).sum) v ∈
          tensorFiltration m B η n (k - weightDegree (rootWeight r) - 1) := by
  obtain ⟨g, hg⟩ := exists_positive_ordinary_leading m B n p η f r hr hs t
  refine ⟨g, fun k v hv => ?_⟩
  have h := hg.2 k v hv
  simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_add_eq_sub_sub] using h

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
