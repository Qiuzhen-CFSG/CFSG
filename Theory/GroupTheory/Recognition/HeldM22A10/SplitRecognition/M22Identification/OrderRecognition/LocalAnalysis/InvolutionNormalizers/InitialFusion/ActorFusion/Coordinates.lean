module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ModelSylow

/-!
# The faithful local actors on Janko's second elementary sixteen

The points are the actual coordinates z₁, a and d in F. The local actor
is the image of conjugation by the coordinate Sylow subgroup, inside Aut(F).
These definitions fix the finite action problem used in Lemma 3.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, printed pp.4–5. Source indices are one-based.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.ActorFusion
open LocalModelDichotomy

public abbrev zF : modelF := ⟨z 0, modelF_generators.1⟩
public abbrev aF : modelF := ⟨a, modelF_generators.2.2.1⟩
public abbrev dF : modelF := ⟨d, modelF_generators.2.2.2⟩

@[expose] public def localAction : modelT →* MulAut modelF :=
  modelF.normalizerMonoidHom.comp
    (Subgroup.inclusion (show modelT ≤ normalizer (modelF : Set TwistedModel) from
      modelF_normalizer ▸ le_rfl))
@[expose] public def localActor : Subgroup (MulAut modelF) := localAction.range

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.ActorFusion
