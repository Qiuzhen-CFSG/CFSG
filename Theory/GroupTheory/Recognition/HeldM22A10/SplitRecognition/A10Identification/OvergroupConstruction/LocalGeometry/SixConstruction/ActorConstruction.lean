module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.Inputs
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.Relations
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.SectionActions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.SmallNormalizer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.UConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.VConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.CommutingChoice

/-!
# Construction of Held's compatible actors

Given the explicit marked A₆ section and the source nonfusion hypotheses,
construct the normalized order-three actors with `UConstruction` and
`VConstruction`. The marked four-group and its actual automorphism normalizer
S₄ × C₂ give the ambient commuting choice through `CommutingChoice`.
Finally `Relations` replaces v by v^pi when necessary, preserving its exact
order and every earlier action. Thus `exists_compatibleActors_of_markedSection`
discharges both actor-existence obligations and the commuting-choice premise.

The marked section remains an explicit input. Its construction and the
normalized source-six assembly belong to the enclosing geometry construction.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 4.1--4.2 and 5.1, pp.232--236.
Conjugation follows the source convention x^g = g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

/-- Construct both actors from the marked section, then make Held's choice
between v and v^pi so that they commute. Every order and action in
`CompatibleActors` is preserved by this choice. -/
public theorem exists_compatibleActors_of_markedSection [Finite G] [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hlam : ¬ IsConj (pi D e) (lam D e))
    (hxi : ¬ IsConj (pi D e) (xi D e))
    (s : NoncentralAnalysis.AlternatingSixSection
      (centralizer ({D.a10NoncentralInvolution e} : Set G)))
    (m : MarkedSection D e s) : Nonempty (CompatibleActors D e) := by
  obtain ⟨a⟩ := exists_uActor_of_markedSection D e hfusion hlam hxi s m
  obtain ⟨b⟩ := exists_vActor_of_markedSection D e hfusion s m
  exact compatibleActors_of_commuting_choice D e a b (actor_commuting_choice D e s m a b)

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
