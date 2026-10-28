module

public import Theory.GroupAction.OddInvariantSylow
public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# Lifting a normalized odd Sylow action through an odd kernel

For a surjection with odd kernel, an involution normalizing an odd
three-subgroup in the target normalizes a three-subgroup mapping onto it.
The selected involution is unchanged. The preimage has odd order, so its
conjugation action admits an invariant Sylow three-subgroup; that Sylow
maps onto the entire target three-subgroup.

The lift can have larger order than its image because the odd kernel can
have a nontrivial three-part. This is the unbarred Sylow lift in
Janko–Thompson (1970), §4, printed p.391.
-/

open Subgroup

/-- Lift an odd three-subgroup while retaining a prescribed normalizing
involution. The kernel may have a nontrivial three-part. -/
public theorem normalized_sylow_lift_of_odd_kernel
    {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
    (f : G →* D) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker))
    (U : Subgroup D) (hU : IsPGroup 3 U) (hUodd : Odd (Nat.card U))
    (t : G) (ht : t ^ 2 = 1) (htu : f t ∈ normalizer (U : Set D)) :
    ∃ Q : Subgroup G, IsPGroup 3 Q ∧ Q.map f = U ∧
      t ∈ normalizer (Q : Set G) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let L := U.comap f
  have hLodd : Odd (Nat.card L) := by
    have hcardQ : Nat.card (L ⧸ f.ker.subgroupOf L) = Nat.card U :=
      card_quotient_subgroupOf_comap_eq f hf U
    have hcardK : Nat.card (f.ker.subgroupOf L) = Nat.card f.ker :=
      Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap f U)).toEquiv
    have hcard := card_eq_card_quotient_mul_card_subgroup (f.ker.subgroupOf L)
    rw [hcardQ, hcardK] at hcard
    rw [hcard]
    exact hUodd.mul hker
  have htn : t ∈ normalizer (L : Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    change f x ∈ U ↔ f (t * x * t⁻¹) ∈ U
    simpa only [map_mul, map_inv] using mem_normalizer_iff.mp htu (f x)
  let T := zpowers t
  have hT : IsPGroup 2 T := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one ht
  have hTn : T ≤ normalizer (L : Set G) := zpowers_le.mpr htn
  let action : T →* MulAut L := L.normalizerMonoidHom.comp (inclusion hTn)
  let : MulDistribMulAction T L := MulDistribMulAction.compHom L action
  have hbot : IsInvariant T L (⊥ : Subgroup L) := by
    constructor
    intro a x
    simp only [mem_bot]
    exact ⟨fun h => by rw [h, smul_one], fun h => by
      have hh := congrArg (fun y : L => a⁻¹ • y) h
      simpa only [inv_smul_smul, smul_one] using hh⟩
  obtain ⟨P, _, hPI⟩ := exists_invariant_sylow_le_of_isPGroup (p := 3) hT hLodd
    (⊥ : Subgroup L) IsPGroup.of_bot hbot
  let Q := (P : Subgroup L).map L.subtype
  have hPmap : (P : Subgroup L).map (f.subgroupComap U) = ⊤ := by
    let R := P.mapSurjective (f.subgroupComap_surjective_of_surjective U hf)
    exact (R.is_maximal' (hU.to_subgroup ⊤) le_top).symm
  have hmap : Q.map f = U := by
    have he : U.subtype.comp (f.subgroupComap U) = f.comp L.subtype := rfl
    rw [show Q = (P : Subgroup L).map L.subtype from rfl, map_map,
      ← he, ← map_map, hPmap, ← MonoidHom.range_eq_map, range_subtype]
  refine ⟨Q, P.isPGroup'.map L.subtype, hmap, ?_⟩
  apply mem_normalizer_iff.mpr
  intro x
  have hforward (a : T) {y : G} (hy : y ∈ Q) :
      (a : G) * y * (a : G)⁻¹ ∈ Q := by
    obtain ⟨yL, hyL, rfl⟩ := hy
    exact ⟨a • yL, (hPI.invariant a yL).mp hyL, rfl⟩
  constructor
  · exact hforward ⟨t, mem_zpowers t⟩
  · intro hx
    have hh := hforward (⟨t, mem_zpowers t⟩ : T)⁻¹ hx
    change t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ ∈ Q at hh
    simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
      inv_mul_cancel, mul_one] using hh
