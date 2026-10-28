module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.Components
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Assembly.SourceAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch

/-!
# Source assembly through the natural–dual decomposition in 15.3.58

The normal reduction proves positivity, nonsolvability, the component bound,
and the full 15.3.57(2) alternative. Its actual components and the earlier
marked action supply every hypothesis of the irreducible sieve. The exhaustive
G.9.3 exclusion therefore selects the split branch. G.6.4 then recognizes both
constituents, and the original polar form pairs them for the same K*-action.
This proves s = 1 and an actual K* ≃ PSL₃(2), with natural–dual coordinates.

Only the precise universal G.6.4 and adequate G.9.3 witnesses, plus the enumerated
earlier local source inputs, remain explicit here. This is not yet all of
15.3.58: recognition of the entire actor and its two-residual, the specified
outer element, and the plus-type group isomorphism require further assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1148–1149.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction SplitBranch
universe u f
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}

/-- A recognition output on the literal quotient, not an earlier-source input.
The two module coordinates use the first model's same actor isomorphism. -/
structure NaturalPair (d : EarlierSourceInputs Z ZS V M C v s)
    (a : EarlierActionInputs d) where
  K : Subgroup (ActorQuotient Z)
  minimal : MinimalNormalConclusion C d.kernel K v s
  pair : SplitPair (actorRepresentation Z ZS d.kernel) K v s
  first_model : BinaryLinearThree.NaturalModel pair.first.toRepresentation
  second_model : BinaryLinearThree.NaturalModel pair.second.toRepresentation
  s_eq_one : s = 1
  first_singular : ∀ w ∈ pair.first.toSubmodule, a.quadratic w = 0
  second_singular : ∀ w ∈ pair.second.toSubmodule, a.quadratic w = 0
  inequivalent : ¬ Nonempty (Representation.Equiv
    pair.first.toRepresentation pair.second.toRepresentation)
  dual_pairing : Nonempty (Representation.Equiv pair.second.toRepresentation
    (BinaryLinearThree.W.dual.comp
      (first_model.actor.trans Matrix.PSL3Two.equiv.symm).toMonoidHom))

/-- Remaining actor-recognition output. This structure is a conclusion to be
constructed from `NaturalPair`; it is not an earlier source assumption.
The stabilizer equality is the action-level interface for the independent
specified-element argument. -/
structure ActorRecognition
    {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}
    (p : NaturalPair d a) where
  equiv : ActorQuotient Z ≃* MulAut Matrix.PSL3Two.PSL
  inner : p.K.map equiv.toMonoidHom = MulAut.innerSubgroup Matrix.PSL3Two.PSL
  residual : pResidual 2 (ActorQuotient Z) = p.K
  centralizer : centralizer (p.K : Set (ActorQuotient Z)) = ⊥
  permutes : ∀ h : ActorQuotient Z,
    Submodule.map (actorRepresentation Z ZS d.kernel h) p.pair.first.toSubmodule =
        p.pair.first.toSubmodule ∨
      Submodule.map (actorRepresentation Z ZS d.kernel h) p.pair.first.toSubmodule =
        p.pair.second.toSubmodule
  stabilizer : ∀ h : ActorQuotient Z,
    Submodule.map (actorRepresentation Z ZS d.kernel h) p.pair.first.toSubmodule =
        p.pair.first.toSubmodule ↔ h ∈ p.K

/-- Select the two-summand branch by discharging the entire irreducible sieve.
The component join, local prime restrictions and fixed-line dimension are all
constructed here from the earlier data and the minimal-normal reduction. -/
theorem twoSummand_of_earlier_source
    (hG93 : IrreducibleSieve.G93SourceTheorem.{u, u, f} C)
    (d : EarlierSourceInputs Z ZS V M C v s) (a : EarlierActionInputs d)
    (K : Subgroup (ActorQuotient Z))
    (hK : MinimalNormalConclusion C d.kernel K v s) :
    TwoSummandAlternative (actorRepresentation Z ZS d.kernel) K v s := by
  rcases hK.constituents.2 with hi | hs
  · exact False.elim (IrreducibleSieve.source_irreducible_false C hG93 Z ZS d.kernel
      a.sieveData (hK.componentData hi) d.sqtk)
  · exact hs

/-- Assemble the normal reduction, all irreducible exclusions, both G.6.4
recognitions and the orthogonal pairing. No recognized group, module model,
constituent alternative or model-exclusion premise is supplied by the caller. -/
theorem naturalPair_of_earlier_source
    (hG64 : G64SourceTheorem C)
    (hG93 : IrreducibleSieve.G93SourceTheorem.{u, u, f} C)
    (d : EarlierSourceInputs Z ZS V M C v s) (a : EarlierActionInputs d) :
    Nonempty (NaturalPair d a) := by
  have r := normal_reduction_of_earlier_source d
  obtain ⟨K, hK⟩ := r.normal_actor
  let := hK.minimal.1
  let p := SplitPair.ofAlternative (twoSummand_of_earlier_source hG93 d a K hK)
  obtain ⟨S, hS, hna, _, n, _, ⟨e⟩⟩ := hK.simple_power
  let := hS
  obtain ⟨⟨m₁⟩, ⟨m₂⟩⟩ := G64Natural.hasNaturalModels Z ZS d.kernel hG64
    hna K e v s r.positive p a.quadratic a.invariant a.nondegenerate
    d.actorSylow a.sieveData.marked_central r.plane_three
    (QuotientGroup.mk' (pCore 2 (centralizerH Z)))
    (QuotientGroup.mk'_surjective _) d.sqtk
  obtain ⟨hs, hsing₁, hsing₂, hne, hdual⟩ := geometry_of_natural_models
    Z ZS d.kernel K v s p a.quadratic a.invariant a.nondegenerate m₁ m₂
  exact ⟨⟨K, hK, p, m₁, m₂, hs, hsing₁, hsing₂, hne, hdual⟩⟩

/-- The parameter equality in 15.3.58(2), with both classification branches
and all recognition hypotheses discharged from the enumerated earlier source. -/
theorem s_eq_one_of_earlier_source
    (hG64 : G64SourceTheorem C)
    (hG93 : IrreducibleSieve.G93SourceTheorem.{u, u, f} C)
    (d : EarlierSourceInputs Z ZS V M C v s) (a : EarlierActionInputs d) : s = 1 := by
  obtain ⟨p⟩ := naturalPair_of_earlier_source hG64 hG93 d a
  exact p.s_eq_one

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
