module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Natural
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.ActorGeneration.Exceptional

/-!
# Assembly of the ambient A₆ actor generation bound

The proved natural and exceptional finite calculations feed the faithful
ambient lift. They exhaust all elementary actors in Aut(A₆), with conjugators
in A₆ itself, so each conjugator lifts to the given component in G. This proves
`actorGeneration` without additional premises. Applying it to the literal
cubic actor in Chapter K gives degree at most twelve.

Source: Aschbacher–Smith K.1.1, printed p.452 (PDF p.463), via the
GM02 conjugate-generation degree estimate. The subsequent degree-four gap
is independent and remains with the G.5.1 and Chapter K assembly owners.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory

namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof
universe u v

/-- Assemble the two finite calculations and lift their actual component
conjugators to every ambient group in the generation contract. -/
theorem actorGeneration_of_cases (hnatural : NaturalGeneration)
    (hexceptional : ExceptionalInvolutionGeneration) : ActorGeneration.{u} :=
  actorGeneration_of_inner_budget (inner_budget_of_cases hnatural hexceptional)

/-- Application to the original Chapter K representation: the two group
calculations discharge precisely the actor-generation premise of the degree
bound in `Reduction`. No cubic-ratio restriction to L is made. -/
theorem finrank_le_twelve_of_generation_cases
    (hnatural : NaturalGeneration) (hexceptional : ExceptionalInvolutionGeneration)
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}
    (h : Input ρ K L) (e : L ≃* alternatingGroup (Fin 6)) :
    Module.finrank (ZMod 2) V ≤ 12 :=
  finrank_le_twelve_of_actorGeneration ρ (actorGeneration_of_cases hnatural hexceptional) h e

end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction.ActorGenerationProof

namespace CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction
universe u v

/-- Every nontrivial elementary two-subgroup in an ambient group with
generalized Fitting subgroup A₆ generates over that component using conjugates
whose number times its binary rank is at most six. -/
theorem actorGeneration : ActorGeneration.{u} :=
  ActorGenerationProof.actorGeneration_of_cases
    ActorGenerationProof.naturalGeneration
    ActorGenerationProof.exceptionalInvolutionGeneration

/-- The original ambient cubic actor gives degree at most twelve for an A₆
component, with the group-generation premise discharged. -/
theorem finrank_le_twelve
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}
    (h : Input ρ K L) (e : L ≃* alternatingGroup (Fin 6)) :
    Module.finrank (ZMod 2) V ≤ 12 :=
  finrank_le_twelve_of_actorGeneration ρ actorGeneration h e

end CFSG.Quasithin.ChapterK.Alternating.SixDegreeReduction
