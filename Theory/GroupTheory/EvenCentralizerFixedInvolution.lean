module
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# A two-group fixes an involution in an even centralizer

A two-group normalizing a subgroup acts on its centralizer by conjugation.
The fixed subgroup has the same cardinality modulo two. An even centralizer
therefore has a fixed involution, centralized by both the marked subgroup and
the acting two-group. The normalizer-Sylow specialization preserves the exact
actor required by the paired-block escape in Aschbacher--Smith 2.4.25,
printed p.543; evenness of that centralizer is a separate source input.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem exists_involution_centralizing_normalizing_two_group
    (A R : Subgroup G) (hR : IsPGroup 2 R)
    (hRA : R ≤ normalizer (A : Set G))
    (heven : 2 ∣ Nat.card (centralizer (A : Set G))) :
    ∃ z : G, orderOf z = 2 ∧ A ⊔ R ≤ centralizer ({z} : Set G) := by
  let C := centralizer (A : Set G)
  let _ := conjMulDistribMulActionOfLeNormalizer R C
    (hRA.trans (normalizer_le_normalizer_centralizer A))
  let F := FixedPoints.subgroup R C
  have hm := hR.card_modEq_card_fixedPoints C
  change Nat.card C % 2 = Nat.card F % 2 at hm
  have hd : 2 ∣ Nat.card F := Nat.dvd_of_mod_eq_zero (hm.symm.trans (Nat.mod_eq_zero_of_dvd heven))
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 hd
  refine ⟨z.val.val,(Subgroup.orderOf_coe z.val).trans ((Subgroup.orderOf_coe z).trans hz),sup_le ?_ ?_⟩
  · intro a ha
    exact mem_centralizer_singleton_iff.mpr (z.val.property a ha)
  · intro r hr
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (z.property (⟨r,hr⟩ : R))
    change r * z.val.val * r⁻¹ = z.val.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh

/-- In particular the marked subgroup and any Sylow two-subgroup of its
normalizer lie together in one involution centralizer. -/
theorem exists_involution_centralizing_normalizer_sylow
    (A : Subgroup G) (P : Sylow 2 (normalizer (A : Set G)))
    (heven : 2 ∣ Nat.card (centralizer (A : Set G))) :
    ∃ z : G, orderOf z = 2 ∧ A ⊔
      (P : Subgroup (normalizer (A : Set G))).map
        (normalizer (A : Set G)).subtype ≤ centralizer ({z} : Set G) := by
  apply exists_involution_centralizing_normalizing_two_group A _
    (P.isPGroup'.map (normalizer (A : Set G)).subtype) _ heven
  rintro _ ⟨x, _, rfl⟩
  exact x.property

end Theory.GroupTheory
