module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.CyclicActor
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.IntrinsicClassification

/-!
# Exceptional A₇ actors: intrinsic witnesses and fixed spaces

Every permitted actor has zero common fixed space on the marked plane.
If its two-core is nontrivial, it contains an involution fixing that plane
pointwise. Otherwise the cubic quotient is the whole actor, and Sylow
normalization forces a single three-cycle. The faithful four-dimensional
involution and three-cycle calculations then give zero fixed space on the
entire module. These deductions need no extra actor witness or fixed-plane
hypothesis. `Catalogue.Applications` applies them to the literal source
quotient centralizers.

The coordinate candidates and their literal group structures are published by
the imported catalogue modules. `Catalogue.exists_actor_catalogue` combines
those structures with the representation-dependent diagonal marking and gives
the three distinct permitted subgroups for an arbitrary plane.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A7 W} {P : Submodule (ZMod 2) W}
  {S : Sylow 2 A7} {D : Subgroup A7}

/-- The source actor hypotheses themselves produce a structural witness. -/
theorem PermittedActor.actorWitness (h : PermittedActor ρ P S D)
    (hP : Module.finrank (ZMod 2) P = 2) : ActorWitness ρ P D := by
  by_cases hcore : pCore 2 D = ⊥
  · have hc := h.quotient_card
    rw [hcore, Nat.card_congr QuotientGroup.quotientBot.toEquiv] at hc
    exact Or.inl (threeCycle_mem_of_card_three S D hc h.normalized)
  · exact h.actorWitness_of_twoCore_ne_bot hP hcore

/-- The full actor has zero common fixed space on the original faithful
four-space, including when its cubic elements are double three-cycles. -/
theorem PermittedActor.fixed_eq_zero [FiniteDimensional (ZMod 2) W]
    (h : PermittedActor ρ P S D) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4) (hP : Module.finrank (ZMod 2) P = 2) :
    ∀ w : W, (∀ d : D, ρ d w = w) → w = 0 :=
  fixed_eq_zero_of_actorWitness ρ hρ hdim P hP D
    (h.plane_fixed_eq_zero hP) (h.actorWitness hP)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
