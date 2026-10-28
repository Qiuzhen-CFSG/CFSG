module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Witness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Source

/-!
# Assembly boundary for MS93 (4.3.2)(6)

The backward choices and the R_4/lambda/mu witness construction are proved
in the imported modules. Excluding that actual witness bounds the complete
P-conjugate span, including the starting radius group.

The imported source package proves existence of an actual separating choice,
and span and generation for every separating choice. Its failed-span
construction retains that separation through the actual P-conjugate and
both witness stages.

The legacy universal assembly below retains witness exclusion and generation
as explicit premises. The separating-choice package does not discharge those
stronger universal premises or construct the legacy `StepSixFacts`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Excluding the constructed R_4/lambda/mu configuration bounds every P-conjugate. -/
theorem span_bound_of_witness_exclusion (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (exclude : ∀ d, Before p.a p.a' d 4 → StepSix.EscapingWitness p d → False) :
    ∀ choice : BackwardChoice p, ∀ d, Before p.a p.a' d 4 → choice.W ≤ Q R d := by
  intro choice d hd
  by_contra h
  obtain ⟨w⟩ := StepSix.radiusWitness_of_failed_span hb p hd choice h
  obtain ⟨e⟩ := StepSix.escapingWitness_of_radius source hb modules transfer facts p bad hd w
  exact exclude d hd e

/-- The remaining source stages are explicit and must be discharged by step_six. -/
theorem step_six_of_witness_exclusion (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (transfer : NormalizationTransfer R) (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (exclude : ∀ d, Before p.a p.a' d 4 → StepSix.EscapingWitness p d → False)
    (generation : ∀ choice : BackwardChoice p, choice.P ⊔ Z R p.a' = stabilizer R p.a) :
    StepSixFacts p :=
  ⟨StepSix.backwardChoice_nonempty source hb modules transfer facts p bad,
    span_bound_of_witness_exclusion source hb modules transfer facts p bad exclude,
    generation⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts
