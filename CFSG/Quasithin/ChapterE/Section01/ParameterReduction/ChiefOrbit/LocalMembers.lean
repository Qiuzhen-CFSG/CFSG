module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Orbit
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Transport

/-!
# Assembly of the local E-member transfer

The residual orbit and quotient-lifting applications are proved in the imported
extensions. The reduction below combines three still-explicit inputs: transfer
from the literal intersection family to an ambient actor, the odd residual
quotient branch, and the component diagonal branch. It does not assert the
unconditional local containment in E.1.11. Its source assembly must discharge
all three inputs using chief minimality and the trivial ambient two-core.

The ambient Sylow subgroup lies in the target normalizer. Consequently, after
the orbit group is contained, Sylow supplementation puts the entire original
local member in the target. This avoids assuming that the local member itself
lies in the residual--tau orbit group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed p.213.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The final local-family reduction, retaining the actor-transfer and both
orbit-branch obligations. No local generation hypothesis is used. -/
theorem localEFamily_le_of_orbit_branches {n : ℕ} (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω)
    (hactors : ∀ V ∈ intersectionFamily (localGroup T J) Ω,
      V ≤ (stabilizer T J).subgroupOf (localGroup T J) →
      ∀ P, IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J)) V P →
        ¬ P.map (localGroup T J).subtype ≤ generationTarget n T Ω →
        ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧
          ∃ Q, IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
            (A.subgroupOf (localGroup T J)) Q ∧
              ¬ Q.map (localGroup T J).subtype ≤ generationTarget n T Ω)
    (hodd : ∀ A ∈ Ω, A ≤ (T : Subgroup G) →
      ∀ P, IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
        (A.subgroupOf (localGroup T J)) P →
        ECaseOdd (A.subgroupOf (localGroup T J)) P →
          memberOrbitGroup T J A P ≤ generationTarget n T Ω)
    (hcomponent : ∀ A ∈ Ω, A ≤ (T : Subgroup G) →
      ∀ P, IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
        (A.subgroupOf (localGroup T J)) P →
        ECaseComponent ((stabilizer T J).subgroupOf (localGroup T J))
          (A.subgroupOf (localGroup T J)) P →
          memberOrbitGroup T J A P ≤ generationTarget n T Ω) :
    localEFamily n T J Ω ≤ generationTarget n T Ω := by
  apply localEFamily_le_of_actor_transfer T J hactors
  intro A hA hAT P hP
  apply local_member_le_of_orbitGroup_le T J A hP
    ((sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right)
  rcases hP.2 with ⟨ho, _⟩ | ⟨hc, _⟩
  · exact hodd A hA hAT P hP ho
  · exact hcomponent A hA hAT P hP hc

end CFSG.Quasithin.ChapterE.ChiefOrbit
