module
public import Theory.GroupTheory.Signalizer.QPrime
public import Theory.PPrimeCore

/-!
# Local cores inside the canonical q-prime subfamily

The mapped q-prime core of an actual signalizer value is invariant under
the supplied actor, and its entire value normalizes it. Characteristic
invariance and native core normality give these two properties after mapping
along the value inclusion into the original group.

For a finite elementary binary actor and finite ambient group, the mapped
core has q-coprime order and is normalized by the common subgroup. It is
therefore a candidate in the defining supremum of the q-prime subfamily and
lies in the corresponding new value. No completeness or rank bound is used.

These are the local core containments in Kurzweil–Stellmacher, *The Theory
of Finite Groups*, §11.2.7 step(4), using the canonical subfamily of §11.1.6.
The companion properties support its actual ordered-product factorization.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

public theorem core_invariant (θ : TwoSignalizerFamily A G) (q : ℕ)
    (a : {a : A // a ≠ 1}) :
    IsInvariant A G ((pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype) := by
  let _ := θ.invariant a
  let _ := isInvariant_of_characteristic (A := A) (pPrimeCore q (θ.subgroup a))
  exact isInvariant_map_subtype (θ.subgroup a) (pPrimeCore q (θ.subgroup a))

public theorem value_le_normalizer_core (θ : TwoSignalizerFamily A G) (q : ℕ)
    (a : {a : A // a ≠ 1}) :
    θ.subgroup a ≤ Subgroup.normalizer
      ((pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype : Set G) := by
  have h := (pPrimeCore q (θ.subgroup a)).le_normalizer_map (θ.subgroup a).subtype
  rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

public theorem core_le_qPrime_subgroup [Finite A] [Finite G] [IsElementaryAbelian 2 A]
    (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) :
    (pPrimeCore q (θ.subgroup a)).map (θ.subgroup a).subtype ≤ (θ.qPrime q).subgroup a := by
  apply θ.le_qPrime_subgroup q a (Subgroup.map_subtype_le _) (θ.core_invariant q a)
    ((θ.common_le a).trans (θ.value_le_normalizer_core q a))
  rw [Subgroup.card_map_of_injective (θ.subgroup a).subtype_injective]
  exact (pPrimeCore_coprime_card (p := q) (G := θ.subgroup a)).symm

end Theory.GroupTheory.TwoSignalizerFamily
