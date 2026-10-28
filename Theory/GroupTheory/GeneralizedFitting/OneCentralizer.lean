module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage

/-!
# A component containing an element with prime-power centralizer

If an element of a component has a p-group centralizer, every other component
would be both quasisimple and a p-group, which is impossible.  When the Fitting
subgroup is trivial, this unique component is the actual simple generalized
Fitting subgroup.

This is the final component step of Aschbacher--Smith G.4.9, printed p.342.
Only the centralizer of the specified element is required.  The geometric
construction of that element and the vanishing of the Fitting subgroup are
separate inputs.
-/

public section

open Subgroup

namespace Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G] {K : Subgroup G}

/-- One prime-power centralizer inside a component excludes every other
component.  No hypothesis on all involution centralizers is needed. -/
theorem IsComponent.unique_of_mem_prime_power_centralizer
    (hK : IsComponent G K) {p : ℕ} [Fact p.Prime] (t : G) (ht : t ∈ K)
    (hC : IsPGroup p (centralizer ({t} : Set G)))
    (D : Subgroup G) (hD : IsComponent G D) : D = K := by
  by_contra hne
  have hDK : D ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hD.commutator_eq_bot_of_ne hK hne)
  have hDt : D ≤ centralizer ({t} : Set G) :=
    hDK.trans (centralizer_le (Set.singleton_subset_iff.mpr ht))
  have hpD : IsPGroup p D := hC.to_le hDt
  let : Group.IsNilpotent D := hpD.isNilpotent
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact Group.IsPerfect.not_isSolvable D inferInstance

/-- The literal component is simple and equals F* once the Fitting subgroup
vanishes and one of its elements has prime-power centralizer. -/
theorem IsComponent.generalizedFitting_eq_and_simple_of_mem_prime_power_centralizer
    (hK : IsComponent G K) (hfit : fittingSubgroup G = ⊥)
    {p : ℕ} [Fact p.Prime] (t : G) (ht : t ∈ K)
    (hC : IsPGroup p (centralizer ({t} : Set G))) :
    generalizedFitting G = K ∧ IsSimpleGroup K := by
  have hu := hK.unique_of_mem_prime_power_centralizer t ht hC
  have hF : generalizedFitting G = K := by
    apply le_antisymm _ (component_le_generalizedFitting G K hK)
    rw [generalizedFitting, hfit, bot_sup_eq]
    exact sSup_le (fun D hD => (hu D hD).le)
  have hz : center K = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ K.subtype_injective).mp
    exact le_bot_iff.mp (hfit ▸ hK.center_map_le_fitting)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  have hs : IsSimpleGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  exact ⟨hF, hs⟩

end Theory.GroupTheory
