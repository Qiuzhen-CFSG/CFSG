module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree

/-!
# The HS degree window directly from modular saturation

The actual simple models and odd-order conjugacy-class bound already leave
only dimensions one and twenty in the window at most fifty. Scalar extension
preserves the dimension, and the extraspecial-subgroup lower bound excludes
one for a faithful action. This proves the absolute degree window directly,
without the separate fixed-free degree-forty calculation.

The source application retains the original representation, central-quotient
marking, two-group center and degree-twenty trace input. The three saturation
inputs still require their existing construction proofs; no completeness
assertion is inferred from a list of candidate dimensions.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph; Aschbacher--Smith K.4, printed p.457.
-/

public section
open Subgroup Theory.GroupTheory
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims

universe u v

/-- Modular saturation supplies the full absolute degree window without
an additional degree-forty exclusion premise. -/
theorem absoluteDegreeWindow_of_saturating_models
    (hclasses : AbsoluteWindow.FixedSpace.OddClassBound)
    (hsmall : AbsoluteWindow.FixedSpace.TwentyModelExists.{v})
    (hlarge : AbsoluteWindow.FixedSpace.LargeModelsExist.{v}) :
    AbsoluteDegreeWindow.{v} := by
  intro hs K _ _ _ W _ _ _ τ hf hi hd
  let F := AlgebraicClosure K
  let := hi.irreducible_of_closure
  have hd' : Module.finrank F (F ⊗[K] W) ≤ 50 := by
    simpa only [Module.finrank_baseChange] using hd
  have h := AbsoluteWindow.FixedSpace.finrank_eq_one_or_twenty_of_models
    hclasses hsmall hlarge hs (Representation.extendScalars F τ) hd'
  simp only [Module.finrank_baseChange] at h
  have hlow := twenty_le_finrank τ hf
  omega

/-- Apply the direct window to the literal source cover and its original
binary representation. The center and trace inputs retain their own producers. -/
theorem SourceHypotheses.finrank_eq_twenty_of_saturating_models
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (h : SourceHypotheses ρ)
    (hcenter : IsPGroup 2 (Subgroup.center (generalizedFitting G)))
    (hclasses : AbsoluteWindow.FixedSpace.OddClassBound)
    (hsmall : AbsoluteWindow.FixedSpace.TwentyModelExists.{v})
    (hlarge : AbsoluteWindow.FixedSpace.LargeModelsExist.{v})
    (htrace : DegreeTwentyTraceField.{v})
    (hd : Module.finrank (ZMod 2) V ≤ 50) : Module.finrank (ZMod 2) V = 20 :=
  h.finrank_eq_twenty_of_representation_inputs hcenter
    (absoluteDegreeWindow_of_saturating_models hclasses hsmall hlarge) htrace hd

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
