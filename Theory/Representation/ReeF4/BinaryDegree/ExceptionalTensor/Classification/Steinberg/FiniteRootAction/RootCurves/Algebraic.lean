module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves.Signed
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters

/-!
# The marked Ree curves in the actual algebraic restriction action

Map the native factorization through the existing coefficient embedding into
the literal closed F4 carrier. The lists retain their root indices, parameter
images, order, and signed degree bounds. This supplies the actual finite root
curves required for the coefficient/filtration restriction argument.

Source: Steinberg (1963), Section 12; GLS3 Theorem 2.8.2.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves

open Theory.AlgebraicGroup StandardRootSystem
local instance rootNegAlgebraic : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- The ordered algebraic word with the same roots and embedded parameters. -/
@[expose] def algebraicWord {m : ℕ} (f : CoefficientField m →+* F)
    (w : RootWord m) : PointGroup F :=
  (w.map fun p => algebraicRootElement p.1 (f p.2)).prod

theorem splitEmbedding_splitWord {m : ℕ} (f : CoefficientField m →+* F)
    (w : RootWord m) : splitEmbedding f (splitWord w) = algebraicWord f w := by
  induction w with
  | nil => simp [splitWord, algebraicWord]
  | cons p w ih =>
    simpa only [splitWord, algebraicWord, List.map_cons, List.prod_cons,
      map_mul, splitEmbedding_rootGenerator] using
      congrArg (fun x => algebraicRootElement p.1 (f p.2) * x) ih

/-- The native curve factorization holds under the actual algebraic Ree
embedding, for every coefficient-field embedding and either sign. -/
theorem exists_algebraic_root_curve (m : ℕ) (f : CoefficientField m →+* F)
    (positive : Bool) {r : F4Chevalley.Root}
    (hr : if positive then typeF4RootPairing_base.IsPos r
      else typeF4RootPairing_base.IsPos (-r))
    (hs : IsShortRoot r) (t : CoefficientField m) :
    ∃ (g : Model m) (left right : RootWord m),
      HigherSupport positive r (left ++ right) ∧
      modelEmbedding f g = algebraicWord f left * algebraicRootElement r (f t) *
        algebraicWord f right := by
  obtain ⟨g, left, right, hhigh, hg⟩ := exists_signed_root_curve m positive hr hs t
  refine ⟨g, left, right, hhigh, ?_⟩
  change splitEmbedding f (toSplitGroup m g) = _
  rw [hg, map_mul, map_mul, splitEmbedding_splitWord, splitEmbedding_splitWord,
    splitEmbedding_rootGenerator]

/-- Applying any algebraic representation gives the same ordered factor
identity on its restriction to the original finite Ree group. -/
theorem exists_restricted_action_curve {V : Type v} [AddCommGroup V] [Module F V]
    (ρ : Representation F (PointGroup F) V) (m : ℕ) (f : CoefficientField m →+* F)
    (positive : Bool) {r : F4Chevalley.Root}
    (hr : if positive then typeF4RootPairing_base.IsPos r
      else typeF4RootPairing_base.IsPos (-r))
    (hs : IsShortRoot r) (t : CoefficientField m) :
    ∃ (g : Model m) (left right : RootWord m),
      HigherSupport positive r (left ++ right) ∧
      ρ (modelEmbedding f g) = ρ (algebraicWord f left) *
        ρ (algebraicRootElement r (f t)) * ρ (algebraicWord f right) := by
  obtain ⟨g, left, right, hhigh, hg⟩ := exists_algebraic_root_curve m f positive hr hs t
  exact ⟨g, left, right, hhigh, by rw [hg, map_mul, map_mul]⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.RootCurves
