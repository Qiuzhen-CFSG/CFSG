module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Residual

/-!
# Residual spans at separating backward edges

For every actual backward choice omitting the critical commutator line,
the source step-(6) bound and generation equality give the residual bound
[W,Ltilde_alpha] <= Vcirc_alpha. The same source package constructs such a
choice. This restricted interface leaves the older universal
`ResidualSpanFacts` and `StepSixFacts` unchanged.

Source: Meierfrankenfeld--Stellmacher (1993), the paragraph following
(4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.SelectedSource
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : MS93.Geometry R}

/-- An actual separating choice and residual bounds for every choice at a separating edge. -/
structure ResidualFacts (p : Counterexample geometry) : Prop where
  backward : ∃ choice : BackwardChoice p,
    ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge
  residual : ∀ choice : BackwardChoice p,
    (¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge) →
    ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a

/-- Step (6) and generation apply to the same separating choice. -/
theorem residualFacts_of_stepSix (source : LocalSource L R)
    {p : Counterexample geometry} (initial : InitialFacts p)
    (hlarge : 6 < geometry.b R) (selected : CentralizerChoice p)
    (stepSix : SeparatingStepSixFacts p) : ResidualFacts p := by
  refine ⟨stepSix.backward, ?_⟩
  intro choice hsep
  obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by omega)
  exact span_residual_le_of_step_six source choice selected initial hlarge hd
    (stepSix.bound choice hsep d hd) (stepSix.generation choice hsep)

/-- Source inputs construct the choice and discharge all span and generation premises. -/
theorem residual_facts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) (selected : CentralizerChoice p) : ResidualFacts p := by
  obtain ⟨ip⟩ := initial p
  exact residualFacts_of_stepSix source ip hlarge selected
    (step_six_separating source hb modules transfer initial facts p bad hlarge selected)

/-- The literal backward moving product is normal in the starting stabilizer. -/
theorem backward_product_normal_of_separating (source : LocalSource L R)
    {p : Counterexample geometry} (span : ResidualFacts p) (choice : BackwardChoice p)
    (hsep : ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a choice.edge) :
    ((Vcirc R p.a ⊔ Vcirc R choice.back).subgroupOf (stabilizer R p.a)).Normal :=
  backward_product_normal source choice (span.residual choice hsep)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.SelectedSource
