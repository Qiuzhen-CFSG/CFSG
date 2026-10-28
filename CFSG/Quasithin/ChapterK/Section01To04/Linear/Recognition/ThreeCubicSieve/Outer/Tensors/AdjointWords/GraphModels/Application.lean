module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.GraphModels
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords

/-!
# Discharging the graph-model premise of the adjoint-word estimate

The graph realization now supplies the graph branch of the existing displacement
and common-fixed-space consumers. Only the independent `OuterModels` analysis
remains explicit; the parent owns its discharge and the unconditional estimate.
All operators and scalar extensions are those of the original binary action.

Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2–5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

/-- The graph input of the original-operator displacement estimate is proved. -/
theorem adjointTensorDisplacement_of_outerModels (hk : σ.ker ≤ Subgroup.center _)
    (ho : AdjointWords.OuterModels B σ) : AdjointTensorDisplacement B σ :=
  adjointTensorDisplacement_of_models (AdjointWords.graph_models hk) ho

/-- The literal actor estimate now needs only the independent outer-type models. -/
theorem adjointTensorEstimate_of_outerModels (hk : σ.ker ≤ Subgroup.center _)
    (ho : AdjointWords.OuterModels B σ) : AdjointTensorEstimate B σ :=
  adjointTensorEstimate_of_models (AdjointWords.graph_models hk) ho

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
