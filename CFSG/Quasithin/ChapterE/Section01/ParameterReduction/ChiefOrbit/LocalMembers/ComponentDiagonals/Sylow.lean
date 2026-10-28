module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.LocalMembers.Orbit
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Sylow

/-!
# The prescribed Sylow subgroup of the residual-orbit group

Restrict the local member's Sylow subgroup to its normal two-residual,
then conjugate these actual Sylow subgroups along the ambient tau orbit.
The commuting-factor theorem and the normalized-supplement index formula
show that T∩K_A is Sylow in K_A. This works in both E-member branches and
does not assert P≤K_A.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.11, printed p.213.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G] [Finite G]
/-- Restrict the prescribed local Sylow to O²(P) and retain both inclusions. -/
theorem exists_localMemberResidual_sylow {n : ℕ}
    (T : Sylow 2 G) (J A : Subgroup G) {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) :
    ∃ R : Sylow 2 (localMemberResidual T J P),
      (R : Subgroup (localMemberResidual T J P)).map (localMemberResidual T J P).subtype ≤
        (T : Subgroup G) := by
  obtain ⟨S, hS⟩ := hP.1.2.2.2.2.1
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal (pResidual 2 P)
  let e : pResidual 2 P ≃* localMemberResidual T J P :=
    ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (((pResidual 2 P).map P.subtype).equivMapOfInjective (localGroup T J).subtype
        (localGroup T J).subtype_injective)
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro _ ⟨x, ⟨y, hy, rfl⟩, rfl⟩
  have hyS : y.val ∈ (S : Subgroup P) := by
    change y ∈ (S : Subgroup P).subgroupOf (pResidual 2 P)
    rw [← hR]
    exact hy
  rw [hS] at hyS
  exact hyS.1

/-- The actual intersection T∩K_A is Sylow, in either E-member branch. -/
theorem exists_memberOrbitGroup_sylow {n : ℕ}
    (T : Sylow 2 G) (J A : Subgroup G) (hcore : pCore 2 G = ⊥)
    (hJ : IsComponent G J) {P : Subgroup (localGroup T J)}
    (hP : IsEMemberAt n ((stabilizer T J).subgroupOf (localGroup T J))
      (A.subgroupOf (localGroup T J)) P) :
    ∃ R : Sylow 2 (memberOrbitGroup T J A P),
      (R : Subgroup (memberOrbitGroup T J A P)) =
        (T : Subgroup G).subgroupOf (memberOrbitGroup T J A P) := by
  obtain ⟨S, hS⟩ := exists_localMemberResidual_sylow T J A hP
  obtain ⟨R, hR⟩ := hJ.exists_sylow_local_orbit_le (localMemberResidual_le_component T J P)
    (memberResidual_stabilizer_invariant T J A hcore hP) (tau_le (T : Subgroup G) A) S hS
  exact exists_sylow_join_eq_intersection (memberResidualOrbit T J A P)
    (tau (T : Subgroup G) A) (T : Subgroup G) T.isPGroup' (tau_le _ _)
    (le_normalizer_componentOrbit _ _) R hR
end CFSG.Quasithin.ChapterE.ChiefOrbit
