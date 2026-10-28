module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges.ActorMatrices.Evaluation
public import Mathlib.Data.List.GetD

/-!
# The packed forest actors are the literal source matrices

The zero fiber uses the two original ATLAS outputs. Every other fiber uses
exactly the thirteen `LowerBound.kernelFactor` values followed by the signed
words in `actorWords`. The full-matrix certificates evaluate those words,
including inverse letters; mapping the lists then also preserves the identity
default at every out-of-range position.

Source: ATLAS of Finite Group Representations, R. A. Wilson, S. J. Nickerson,
J. N. Bray, unchanged `J4G1-max2W1` outputs. See `ActorMatrices/source/README.md`
and `Edges/source/README.md` for provenance and the separate forest-edge contract.
-/

public section
namespace Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound KernelSeparation Janko4.GeneratorCertificates KernelRows

/-- Full matrices for the complete literal actor lists, in their source order. -/
theorem sourceActors_spec (j : Fin 4) :
    (Forest.sourceActors j).map sourceMatrix = (actorRows j).map decodeRows := by
  by_cases hj : j = 0
  · subst j
    simp only [sourceActors, actorRows, ↓reduceIte, List.map_cons, List.map_nil]
    change [toMatrix w10, toMatrix w14] = [decodeRows w10Rows, decodeRows w14Rows]
    rw [eval_w10, eval_w14]
  · have hk : (List.ofFn kernelFactor).map sourceMatrix =
        (List.ofFn factorRows).map decodeRows := by
      rw [List.map_ofFn, List.map_ofFn]
      congr 1
      funext i
      exact eval_factor i
    have hw : ((actorWords j).map sourceWord).map sourceMatrix =
        (wordRows j).map decodeRows := by
      fin_cases j
      · exact (hj rfl).elim
      · exact ActorMatrices.eval_words1
      · exact ActorMatrices.eval_words2
      · exact ActorMatrices.eval_words3
    simp only [sourceActors, actorRows, if_neg hj, List.map_append, hk, hw]

/-- The comparison includes arbitrary positions and both identity defaults. -/
theorem actorRowsAt_spec (k : Fin 11) (n : ℕ) :
    sourceMatrix (Forest.actorAt k n) = Janko4.decodeRows (actorRowsAt k n) := by
  unfold actorAt actorRowsAt
  calc
    sourceMatrix ((sourceActors (fiberIndex k)).getD (actorIndexAt k n) 1) =
        ((sourceActors (fiberIndex k)).map sourceMatrix).getD (actorIndexAt k n)
          (sourceMatrix 1) := (List.getD_map _ _ sourceMatrix).symm
    _ = ((actorRows (fiberIndex k)).map decodeRows).getD (actorIndexAt k n)
          (decodeRows packedOne) := by
      rw [sourceActors_spec, map_one, decode_packedOne]
    _ = decodeRows ((actorRows (fiberIndex k)).getD (actorIndexAt k n) packedOne) :=
      List.getD_map _ _ decodeRows

end Janko4.Cardinality.LocalInvolutionCensus.FiberCensus.Forest.Edges
