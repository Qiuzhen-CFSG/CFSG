module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedActor
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderExtraction

/-!
# FF extraction on the actual moved chosen seed

The local cubic bound gives a common elementary actor on the faithful orbit.
The chosen component makes its action faithful on every homogeneous summand;
the independent-orbit calculation therefore constructs an FF offender on the
seed. Faithful-image transport uses the original conjugation action.

This discharges the FF premise of the B.4.2 consumer in
`SeedAlternativesMovedSylowOffenderAssembly`. It proves the specialized
D.3.5(2) conclusion; the later model sieve and orbit exhaustion remain separate.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.3.5(2), printed pp.195--196, and 3.2.5, printed p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The genuine D.3.5(2) FF conclusion on the actual chosen seed. All
actor, stabilizer, codimension, and faithful-image premises are discharged
from the local cubic bound and the chosen component geometry. -/
theorem seed_ff_of_moved (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : cubicRatio D.orbitRepresentation ≤ 2)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) : IsFFModule D.seedRepresentation := by
  obtain ⟨A,hA,hcu,hbound⟩ := (cubicRatio_le_nat_iff D.orbitRepresentation 2).mp hq
  let : IsElementaryAbelian 2 A := hA.2
  have hff := isFFModule_of_cubic_actor_on_independent_orbit D.orbitRepresentation
    D.orbitSeed A hA hcu (D.orbitSeed_independent hc ⊤) (D.orbitSeed_finrank_gt_two h)
    hbound (D.orbitSeed_translate_kernel_eq_bot h A (IsElementaryAbelian.isPGroup 2 A))
    (D.orbitSeed_exists_moved_of_moved hm)
  exact isFFModule_of_nested_image (reducedRepresentation (L ⊔ (T : Subgroup G)))
    D.orbitSpace D.space (orbitSpan_invariant _ ⊤ D.space) D.seed_le_orbitSpace hff

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
