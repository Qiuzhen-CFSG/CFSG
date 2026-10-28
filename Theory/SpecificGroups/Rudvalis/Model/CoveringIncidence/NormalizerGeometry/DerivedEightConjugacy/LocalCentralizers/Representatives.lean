module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.NormalizerGeometry.DerivedEightConjugacy.LocalCentralizers.Representatives.Certificates

/-!
# Derived subgroups of the three Rudvalis local centralizers

The certified 256 distinct binary products generate each literal local
centralizer once its supplied order is 256. The marked eight-group is normal
inside `localP`; modulo that subgroup the certified generators commute.
Thus the derived subgroup lies in the marked group. The independent reverse
certificates express each marked basis element as a product of commutators.

This proves exactly `RepresentativeDerived`, with its authorized cardinality
premise and no additional assumptions. It supplies the representative input
to `LocalCentralizers.derived_eq_of_certificates`; the conjugacy sieve remains
an independent obligation. This is a concrete model calculation motivated by
GLS3 Table 5.3r and pp.291–292, rather than a restatement of a source theorem.
-/

namespace Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover
open RankOneEightCharacteristic
open scoped commutatorElement

namespace Representatives

private theorem generated_eq (r : Fin 3)
    (hcard : Nat.card (centralizerAt (representative r)) = 256) :
    generated r = centralizerAt (representative r) := by
  apply eq_of_le_of_card_ge (generated_le r)
  rw [hcard]
  exact generated_card r

private theorem derived_le (r : Fin 3) : ⁅generated r, generated r⁆ ≤ elementary 2 := by
  let g : Fin 8 → localP := fun i => ⟨generator r i, generator_mem r i⟩
  let H := closure (Set.range g)
  let E := (elementary 2).subgroupOf localP
  let : E.Normal := elementary_two_normal
  let q := QuotientGroup.mk' E
  have hmap : H.map localP.subtype = generated r := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hc : IsMulCommutative (H.map q) := by
    rw [MonoidHom.map_closure]
    apply isMulCommutative_closure
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩ _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact generator_commutator_mem r i j
  have hb : (⁅H, H⁆).map q = ⊥ := by
    rw [map_commutator]
    exact commutator_self_eq_bot_iff.mpr hc
  have hle : ⁅H, H⁆ ≤ E := by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hb
  calc
    ⁅generated r, generated r⁆ = (⁅H, H⁆).map localP.subtype := by
      rw [map_commutator, hmap]
    _ ≤ E.map localP.subtype := map_mono hle
    _ = elementary 2 := map_subgroupOf_eq_of_le (elementary_le_localP 2)

end Representatives

/-- The three literal local centralizers have the marked derived eight-group.
The cardinality premise is exactly the one transported by the parent consumer. -/
public theorem representativeDerived : RepresentativeDerived := by
  intro r hcard
  rw [← Representatives.generated_eq r hcard]
  exact le_antisymm (Representatives.derived_le r) (Representatives.le_derived r)

end Rudvalis.CoveringIncidence.NormalizerGeometry.LocalCentralizers
