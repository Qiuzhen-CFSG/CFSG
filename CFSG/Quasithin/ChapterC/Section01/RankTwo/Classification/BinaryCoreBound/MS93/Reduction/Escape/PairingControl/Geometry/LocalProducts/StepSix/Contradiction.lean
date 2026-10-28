module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Witness
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Support
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.SupportSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Opposite
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.StepSix.Contradiction.Mixed

/-!
# Assembly of the two R_mu branches in MS93 (4.3.2)(6)

The nontrivial branch uses the exact natural intersection and the support
of R_4 in Z_alpha. The trivial branch uses the order and centralization
of the natural intersection at alpha-2 and alpha-4, identifying it with
the original escaping edge.

The source assembly excludes witnesses whose actual backward choice avoids
the critical commutator line. That same choice supplies the start-Z
obstruction in both support arguments. The unconditional mu/fourth
obstruction discharges the mixed calculation's remaining premise. No span
bound or local generation equality is assumed.

The earlier endpoint-target conditional assembly remains available. The
new theorem does not assert exclusion for every original backward choice;
the source step-(6) owner must retain critical avoidance when constructing
the witness from a failed span bound.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(6), printed p.885.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Conditional assembly; both displayed module premises must be discharged. -/
theorem escapingWitness_false_of_module_calculations (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) {d : Vertex R} (hd : Before p.a p.a' d 4)
    (w : EscapingWitness p d)
    (obstruction : ¬ ⁅Z R w.choice.back, Z R p.a'⁆ ≤ Z R p.a')
    (mixed : w.Rmu = ⊥ →
      Nat.card (U R w.choice.back ⊓ U R w.fourth : Subgroup (FreeAmalgam R)) = 4 ∧
      U R w.choice.back ⊓ U R w.fourth ≤
        centralizer (Z R p.a' : Set (FreeAmalgam R))) : False := by
  by_cases hz : w.Rmu = ⊥
  · obtain ⟨hcard, hC⟩ := mixed hz
    exact w.false_of_fourth_intersection source hb modules facts initial bad obstruction hcard hC
  · exact w.false_of_Rmu_ne_bot_of_Rfour_le_Z source hb modules facts initial bad hlarge hd hz
      (w.Rfour_le_Z_of_obstruction source hb modules facts initial bad hlarge hd obstruction)

/-- Both R_mu branches are impossible for the same critically avoiding
backward choice. The source witness constructor must supply this avoidance. -/
theorem escapingWitness_false_of_critical_avoidance (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (p : Counterexample geometry) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hlarge : 6 < geometry.b R) {d : Vertex R} (hd : Before p.a p.a' d 4)
    (w : EscapingWitness p d)
    (havoid : ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a w.choice.edge) : False := by
  have obstruction := backward_commutator_not_le_start_Z_of_critical_avoidance
    source hb modules facts initial p bad w.choice havoid
  by_cases hz : w.Rmu = ⊥
  · have hnon := w.mu_fourth_commutator_not_le_endpoint_Z
      source hb modules facts initial bad hd
    obtain ⟨_, hcard, hC⟩ := w.mixed_calculation
      source hb modules facts initial bad hlarge hd hz hnon
    exact w.false_of_fourth_intersection_of_start_obstruction
      source hb modules facts initial bad obstruction hcard hC
  · exact w.false_of_Rmu_ne_bot_of_Rfour_le_Z source hb modules facts initial bad hlarge hd hz
      (w.Rfour_le_Z_of_start_obstruction source hb modules facts initial bad hlarge hd obstruction)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.StepSix
