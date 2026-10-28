module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.SelectedSource

/-!
# MS93 (4.3.2)(6) and the local products

The endpoint moving group escapes Q_alpha. Given the geometric step-(6)
outputs, normal generation and residual idempotence bound [W,Ltilde_alpha]
by Vcirc_alpha and prove the backward moving product normal in G_alpha.

The separating-choice source package proves the R_4/R_mu span bound and
generation at the chosen edge. Its residual bound gives the backward triple
and Z-containment deductions. Transporting the entire selected configuration
and separating edge proves the forward normal product. The exported
`local_products` theorem supplies the exact product and endpoint escape
needed by Geometry's terminal-seed assembly, without extra span premises.

The older universal StepSixFacts and ResidualSpanFacts remain conditional
interfaces; the separating source theorem does not assert their stronger
universal fields.

Source: MS93 (1993), (4.3.2), printed pp.885--886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : MS93.Geometry R} {p : Counterexample geometry}

/-- Discharge the residual-span interface from the geometric step-(6) outputs. -/
theorem residualSpanFacts_of_stepSix (source : LocalSource L R)
    (initial : InitialFacts p) (hlarge : 6 < geometry.b R)
    (selected : CentralizerChoice p) (stepSix : StepSixFacts p) : ResidualSpanFacts p := by
  refine ⟨stepSix.backward, ?_⟩
  intro choice
  obtain ⟨d, hd⟩ := p.exists_before (show 4 ≤ geometry.b R by omega)
  exact span_residual_le_of_step_six source choice selected initial hlarge hd
    (stepSix.bound choice d hd) (stepSix.generation choice)

theorem ResidualSpanFacts.backward_normal (span : ResidualSpanFacts p)
    (source : LocalSource L R) (choice : BackwardChoice p) :
    ((Vcirc R p.a ⊔ Vcirc R choice.back).subgroupOf (stabilizer R p.a)).Normal :=
  backward_product_normal source choice (span.residual choice)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
