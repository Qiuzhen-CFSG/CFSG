module
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Outer action on a characteristic quotient

Ambient conjugation on a characteristic quotient of a normal subgroup
induces an action of the ambient quotient by outer automorphisms. Its
inner preimage is exactly the original normal subgroup joined with the
action kernel. Thus an action kernel contained in the normal subgroup
makes the outer action faithful.

Source application: Aschbacher–Smith, 2.4.12(1), printed p.532. The faithful
outer action makes the complement of a single linear block cyclic.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] (L : Subgroup G) [L.Normal]
  (N : Subgroup L) [N.Characteristic]

/-- The original subgroup and action kernel account for every inner actor. -/
theorem normalQuotientAction_comap_inner :
    (MulAut.innerSubgroup (L ⧸ N)).comap (normalQuotientAction L N) =
      L ⊔ (normalQuotientAction L N).ker := by
  have hm : L.map (normalQuotientAction L N) = MulAut.innerSubgroup (L ⧸ N) := by
    ext a
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨QuotientGroup.mk' N ⟨g,hg⟩, (normalQuotientAction_inner L N ⟨g,hg⟩).symm⟩
    · rintro ⟨q,rfl⟩
      obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective N q
      exact ⟨l,l.property,normalQuotientAction_inner L N l⟩
  rw [←hm,comap_map_eq]

/-- The actual induced outer action on the characteristic quotient. -/
def normalQuotientOuterAction : G ⧸ L →* MulAut.Outer (L ⧸ N) :=
  QuotientGroup.map L (MulAut.innerSubgroup (L ⧸ N)) (normalQuotientAction L N) (by
    intro g hg
    exact ⟨QuotientGroup.mk' N ⟨g,hg⟩, (normalQuotientAction_inner L N ⟨g,hg⟩).symm⟩)

/-- Absorbing the action kernel makes the quotient outer action faithful. -/
theorem normalQuotientOuterAction_injective
    (hker : (normalQuotientAction L N).ker ≤ L) :
    Function.Injective (normalQuotientOuterAction L N) := by
  apply (normalQuotientOuterAction L N).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro q hq
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective L q
  change QuotientGroup.mk' (MulAut.innerSubgroup (L ⧸ N))
    (normalQuotientAction L N g) = 1 at hq
  have hg : g ∈ (MulAut.innerSubgroup (L ⧸ N)).comap (normalQuotientAction L N) :=
    (QuotientGroup.eq_one_iff (normalQuotientAction L N g)).mp hq
  rw [normalQuotientAction_comap_inner, sup_eq_left.mpr hker] at hg
  exact (QuotientGroup.eq_one_iff g).mpr hg

end Subgroup
