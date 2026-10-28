module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.CommutingChoice.MarkedFour
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction.ActorConstruction.CommutingChoice.NormalizerLift

/-!
# Held's commuting choice for supplied actors

For the marked A₆ section and the two actors of Sections 4.1--4.2, either u
commutes with v or it commutes with v^pi. The marked four-group lies in A₆
and is normalized by both actors and mu-prime. Its actual automorphism
normalizer is S₄ × C₂, where the dihedral square gives the commuting choice.
Centerlessness lifts that choice to the ambient group, and v centralizing mu
identifies conjugation by pi*mu with conjugation by pi.

All normalizer, model and transport premises are discharged here from the
supplied section, marking and actors. Actor existence belongs to the caller.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 5.1, printed pp.235--236.
Conjugation follows the source convention x^g = g⁻¹*x*g.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (s : NoncentralAnalysis.AlternatingSixSection
    (centralizer ({D.a10NoncentralInvolution e} : Set G)))

/-- The exact choice between the supplied v and v^pi, before the final
compatible-actor constructor. No ambient finiteness or simplicity is required. -/
public theorem actor_commuting_choice (m : MarkedSection D e s) (a : UActor D e) (b : VActor D e) :
    Commute a.u b.v ∨ Commute a.u ((pi D e)⁻¹ * b.v * pi D e) := by
  let := CommutingChoice.four_klein D e
  have h := CommutingChoice.choice_of_normalized_four
    s.ambientSubgroup s.ambientAlternatingEquiv (CommutingChoice.four D e)
    (CommutingChoice.four_le_section D e s m) a.u b.v (mu' D e)
    ⟨tau D e * lam D e, CommutingChoice.second_mem D e⟩
    ⟨pi D e * mu D e, CommutingChoice.core_mem D e⟩
    (a.normalizes_section D e s m) (b.mem_section D e s)
    (mu'_normalizes_section D e s)
    (CommutingChoice.u_normalizes_four D e a)
    (CommutingChoice.v_normalizes_four D e b)
    (CommutingChoice.mu'_normalizes_four D e)
    (a.order ▸ pow_orderOf_eq_one a.u) (b.order ▸ pow_orderOf_eq_one b.v)
    (element_square D e 2 (by decide)) (actor_second_square D e)
    (actor_core_square D e) (actor_core_ne_one D e)
    (actor_dihedral_commutator D e) a.mu'_inverts b.mu'_inverts
  rcases h with h | h
  · exact Or.inl h
  · apply Or.inr
    change Commute a.u ((pi D e * mu D e)⁻¹ * b.v * (pi D e * mu D e)) at h
    rwa [← b.conjugatePi_eq_core_conjugate D e, VActor.conjugatePi_v] at h

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SixConstruction
