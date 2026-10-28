module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Sextet.Quotient
public import Mathlib.GroupTheory.Sylow

/-!
# Lifting the cubic six-point kernel

The full preimage of the order-three quotient kernel has order divisible
by three. Cauchy's theorem supplies a cubic subgroup in the actual ambient
normalizer. Its image is nontrivial, since the rectangle denominator has
order 64, and therefore is the entire cubic kernel. The full preimage is
exactly the join with the rectangle. This is the subgroup X used in the
source four-subgroup normalizer XI.

Source: Aschbacher, *Sporadic Groups* (1994), 40.4(2), p.218.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The order-three kernel has a literal order-three lift to the original
normalizer, and its full preimage is the join of that lift with the plane. -/
theorem exists_plane_cubic_lift (hc : (F.fusion F.plane).ncard = 45) :
    ∃ X : Subgroup (planeNormalizer F), Nat.card X = 3 ∧
      X.map (QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))) =
        (planeSextetAction F hc).ker ∧
      X ⊔ F.plane.subgroupOf (planeNormalizer F) =
        (planeSextetAction F hc).ker.comap
          (QuotientGroup.mk' (F.plane.subgroupOf (planeNormalizer F))) := by
  let A := F.plane.subgroupOf (planeNormalizer F)
  let q := QuotientGroup.mk' A
  let K := (planeSextetAction F hc).ker
  let C := K.comap q
  have hK : Nat.card K = 3 := (planeSextetAction_structure F hc).1
  have hr : Function.Surjective (q.subgroupComap K) :=
    q.subgroupComap_surjective_of_surjective K (QuotientGroup.mk'_surjective A)
  have hdvd : 3 ∣ Nat.card C := by
    rw [← hK]
    exact card_dvd_of_surjective (q.subgroupComap K) hr
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hdvd
  let n : planeNormalizer F := v.val
  have hn : orderOf n = 3 := (orderOf_injective C.subtype Subtype.val_injective v).trans hv
  have hA : Nat.card A = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show F.plane ≤ planeNormalizer F from le_normalizer)).toEquiv]
    exact plane_card F
  have hqn : q n ≠ 1 := by
    intro he
    have hnA : n ∈ A := (QuotientGroup.eq_one_iff n).mp he
    have hd := orderOf_dvd_natCard (⟨n,hnA⟩ : A)
    have heo : orderOf (⟨n,hnA⟩ : A) = 3 :=
      (orderOf_injective A.subtype Subtype.val_injective ⟨n,hnA⟩).symm.trans hn
    rw [heo, hA] at hd
    norm_num at hd
  have ho : orderOf (q n) = 3 := orderOf_eq_prime
    (by rw [← map_pow, ← hn, pow_orderOf_eq_one, map_one]) hqn
  have hm : (zpowers n).map q = K := by
    apply eq_of_le_of_card_ge
    · rw [MonoidHom.map_zpowers]
      exact zpowers_le.mpr v.property
    · rw [MonoidHom.map_zpowers, Nat.card_zpowers, ho, hK]
  refine ⟨zpowers n, ?_, hm, ?_⟩
  · rw [Nat.card_zpowers, hn]
  · change zpowers n ⊔ A = K.comap q
    rw [← hm, comap_map_eq, QuotientGroup.ker_mk']

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
