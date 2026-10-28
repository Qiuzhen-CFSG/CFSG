module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Transport

/-!
# The quotient witnesses required by the component diagonal assembly

This interface records the precise finite family consumed by E.1.10(7)--(8):
actual overgroups of ambient tau inside K_A, their literal Sylow intersections,
rank-n members in their quotients by the intersection with O∞(K_A), and a
cover by the images of those members' residuals together with R_A.

This is an interface for the remaining construction, not an existence theorem.
Its producer must construct the source diagonals, lift them, and prove all
membership and cover fields. It contains no ambient generation conclusion.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed p.213.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]

/-- The still-to-be-constructed quotient members for the nonsolvable branch.
The radical is intrinsic to K_A; every smaller quotient uses its literal preimage. -/
structure ComponentQuotientCover (n : ℕ) (T : Sylow 2 G) (J A : Subgroup G)
    (P : Subgroup (localGroup T J)) (R : Sylow 2 (memberOrbitGroup T J A P)) where
  size : ℕ
  overgroup : Fin size → Subgroup G
  le_orbitGroup : ∀ i, overgroup i ≤ memberOrbitGroup T J A P
  sylow : ∀ i, Sylow 2 (overgroup i)
  sylow_eq : ∀ i, (sylow i : Subgroup (overgroup i)) =
    (T : Subgroup G).subgroupOf (overgroup i)
  tau_le : ∀ i, tau (T : Subgroup G) A ≤ overgroup i
  member : ∀ i, Subgroup ((overgroup i) ⧸
    (solvableRadical (memberOrbitGroup T J A P)).comap (inclusion (le_orbitGroup i)))
  isEMemberAt : ∀ i, IsEMemberAt n
    ((sylow i : Subgroup (overgroup i)).map (QuotientGroup.mk'
      ((solvableRadical (memberOrbitGroup T J A P)).comap (inclusion (le_orbitGroup i)))))
    ((A.subgroupOf (overgroup i)).map (QuotientGroup.mk'
      ((solvableRadical (memberOrbitGroup T J A P)).comap (inclusion (le_orbitGroup i)))))
    (member i)
  cover : (R : Subgroup (memberOrbitGroup T J A P)).map
      (QuotientGroup.mk' (solvableRadical (memberOrbitGroup T J A P))) ⊔
    (⨆ i, ((pResidual 2 (member i)).map (member i).subtype).map
      (quotientInclusion (le_orbitGroup i) (solvableRadical (memberOrbitGroup T J A P)))) = ⊤

end CFSG.Quasithin.ChapterE.ChiefOrbit
