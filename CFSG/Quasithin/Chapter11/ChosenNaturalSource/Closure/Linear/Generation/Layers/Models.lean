module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Layers.Residual
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.RecognizedModels

/-!
# The original homogeneous SL₃ quotient models

The proved projective recognition theorem applies to the actual three-conjugate
series. The source product and the original point-radical identification supply
all its structural premises. Both multiplicities may be zero, and both models
retain the literal quotient projections and the original starred action.

Source: Aschbacher–Smith, 11.5.7, printed pp.781–782; G.2.5(4,6–7), pp.335–336.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open ChapterG.Section02.LinearThree
open Recognition Recognition.Hypothesis
open scoped IsMulCommutative
attribute [local instance] ZMod.algebra

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : Hypothesis (setup E) E.input.field.Carrier E.input.field.degree x y)
  (hUT : E.W ≤ (T : Subgroup G))
  (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)

variable [((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal]
  [((triple E x y).subgroupOf (thirdLayer E x y)).Normal]
  [IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y))]
  [IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y))]

local instance modelsUpperNormal :
    ((S₃ (setup E) x y).subgroupOf (S (setup E) x y)).Normal :=
  inferInstanceAs (((thirdLayer E x y).subgroupOf (threeCore E x y)).Normal)
local instance modelsLowerNormal :
    ((S₂ (setup E) x y).subgroupOf (S₃ (setup E) x y)).Normal :=
  inferInstanceAs (((triple E x y).subgroupOf (thirdLayer E x y)).Normal)
local instance modelsUpperElementary : IsElementaryAbelian 2 (UpperQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (threeCore E x y ⧸
    (thirdLayer E x y).subgroupOf (threeCore E x y)))
local instance modelsLowerElementary : IsElementaryAbelian 2 (LowerQuotient (setup E) x y) :=
  inferInstanceAs (IsElementaryAbelian 2 (thirdLayer E x y ⧸
    (triple E x y).subgroupOf (thirdLayer E x y)))

/-- Genuine upper natural and lower dual models, with no recognition callback. -/
theorem sourceLayerModels :
    ∃ (r s : ℕ), Nonempty (NaturalGeometry.Model d (d.sourceStarComparison hUT hf) r) ∧
      Nonempty (DualGeometry.MarkedModel.Model d (d.sourceStarComparison hUT hf) s) := by
  have hm := Recognition.Hypothesis.recognized_layers_from_projective d hUT hf (d.L_le_I hUT hf)
    (d.S_normalizes_U hUT hf) (d.S_normalizes_marked hUT hf x d.g_mem)
    (d.S_normalizes_marked hUT hf y d.h_mem) (d.S_eq_product hUT hf)
    (d.sourceStarComparison hUT hf) (sourceUpperRadicalIdentification E d hUT hf)
  obtain ⟨hn, r, s, lower, upper, _⟩ := hm
  exact ⟨r, s, ⟨upper⟩, ⟨lower⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
