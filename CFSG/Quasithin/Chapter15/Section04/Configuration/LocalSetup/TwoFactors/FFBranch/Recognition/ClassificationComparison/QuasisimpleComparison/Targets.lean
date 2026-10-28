module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Reduction
/-!
# The remaining group comparisons in the quasisimple branch

The bounded branch below retains the complete corrected module conclusion
on the literal offender actor. Its constructor proves the finite-parameter
reduction from the ambient Sylow bound. The smaller actor and ambient
catalogues are targets for the remaining F.6.18 comparison, not classification
premises. Both catalogues retain the cubic cover and binary G₂ possibilities.

Separating the offender actor from its two-group overgroup allows the model
intersection and the overgroup analysis to be proved independently. Final
assembly must prove both; in particular no equality of those groups is assumed.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 15.4.18,
p.1163; F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; K.1.3, p.453.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace QuasisimpleComparison
universe u v

/-- The actual source action and the group bounds proved in `Reduction`.
These fields are intermediate conclusions; this is not a source hypothesis. -/
structure BoundedBranch {A : Type u} [Group A]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) where
  quasisimple : IsQuasisimple (generalizedFitting A)
  source : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting A)
  component : BoundedQuasisimpleModel (generalizedFitting A)
  actor : BoundedActorModel A

/-- The intended smaller offender list after the mixed-source comparison.
No theorem that this list is exhaustive is asserted here. -/
inductive SmallActorModel (A : Type*) [Group A] : Prop
  | linearThree (equiv : A ≃* SL(3,ZMod 2))
  | alternatingSix (equiv : A ≃* alternatingGroup (Fin 6))
  | symmetricSix (equiv : A ≃* Equiv.Perm (Fin 6))
  | alternatingSeven (equiv : A ≃* alternatingGroup (Fin 7))
  | symmetricSeven (equiv : A ≃* Equiv.Perm (Fin 7))
  | tripleSix (cover : GoldschmidtAlternatives.TripleAlternating A 6)
  | g2Derived (equiv : A ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | g2 (equiv : A ≃* Atlas.G2.Model (ZMod 2))

/-- The intended ambient list additionally retains the triple-symmetric
six extension. These are actual models and covering maps, not family tags. -/
def SmallAmbientModel (D : Type*) [Group D] : Prop :=
  SmallActorModel D ∨ GoldschmidtAlternatives.TripleSymmetric D 6
end QuasisimpleComparison

universe u v
/-- Construct the bounded branch on the actual offender subgroup, retaining
every corrected B.5.1 action and extension clause for later module consumers. -/
theorem ProjectiveLine.ClassifiedAction.bounded_branch {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    Nonempty (QuasisimpleComparison.BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) := by
  obtain ⟨hm, ha⟩ := h.bounded_quasisimple hq c
  exact ⟨⟨hq, c, hm, ha⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
