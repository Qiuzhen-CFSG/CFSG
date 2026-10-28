module

public import Theory.GroupTheory.Recognition.ReeTwo.Order1024OrderProfileData
public import Theory.SpecificGroups.ReeTwo.ParityFrattiniCoordinates
public import Theory.SpecificGroups.ReeTwo.SylowTailCoordinates

/-!
# Coordinates for five rank-three residual Ree two quotients

The representatives numbered 2, 3, 4, 6 and 8 are inverse images of binary
hyperplanes under the rank-four parity projection. Their ordered bases are
respectively `(r3,r0*r1,s²*r1)`, `(r1*r3,r0,s²)`, `(r1,r0,s²)`,
`(r1,r0*r3,s²*r3)` and `(r1*r3,r0,s²*r3)`, where `rj = root j` and
`s = rootOne`. The encode maps give these subspaces in the parity coordinates.

The original generator-defined subgroups contain the common parity kernel:
its normal form uses `r2*r3` and the six tail roots. Explicit words in the
ordered lifts prove the reverse containment and surjectivity. Each quotient
fiber has seven free binary coordinates, hence 128 elements. The identification
of the kernel with Frattini and the exact order counts are separate obligations.

Source: Shinoda (1975), (2.3), pp. 81–82, as implemented in `Core`, `Sylow`
and `ParityFrattiniCoordinates`; no diagnostic group computation is assumed.
-/

@[expose] public section

namespace ReeTwo.SylowModel
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The five residual indices in the order used by these coordinates. -/
def rankThreeIndex (j : Fin 5) : Fin 15 := ![2,3,4,6,8] j

/-- Include the specified three-dimensional space in the parity quotient. -/
def rankThreeEncode (j : Fin 5) : OrderProfileQuotient 3 →* ParityQuotient where
  toFun v := Multiplicative.ofAdd
    (![![v.toAdd 2, v.toAdd 1, v.toAdd 1 + v.toAdd 2, v.toAdd 0],
      ![v.toAdd 2, v.toAdd 1, v.toAdd 0, v.toAdd 0],
      ![v.toAdd 2, v.toAdd 1, v.toAdd 0, 0],
      ![v.toAdd 2, v.toAdd 1, v.toAdd 0, v.toAdd 1 + v.toAdd 2],
      ![v.toAdd 2, v.toAdd 1, v.toAdd 0, v.toAdd 0 + v.toAdd 2]] j)
  map_one' := by revert j; decide +kernel
  map_mul' := by revert j; decide +kernel

/-- Read the three basis coefficients on the encoded subspace. -/
def rankThreeDecode (j : Fin 5) : ParityQuotient →* OrderProfileQuotient 3 where
  toFun v := Multiplicative.ofAdd ![if j = 0 then v.toAdd 3 else v.toAdd 2,
    v.toAdd 1, v.toAdd 0]
  map_one' := by revert j; decide +kernel
  map_mul' := by revert j; decide +kernel

/-- Decoding is a left inverse of encoding. -/
theorem rankThreeDecode_encode : ∀ j v, rankThreeDecode j (rankThreeEncode j v) = v := by
  decide +kernel

/-- All five representatives have even complement coordinate. -/
theorem rankThree_le_parity (j : Fin 5) : residualCandidate (rankThreeIndex j) ≤ ParityKernel := by
  apply sup_le
  · intro x hx
    apply (mem_parityKernel _).mpr
    rw [(mem_tailSubgroup x).mp hx |>.1]
    exact map_one parity
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    fin_cases j <;> rcases hx with rfl | rfl | rfl | rfl
    all_goals apply (mem_parityKernel _).mpr; decide +kernel

/-- The inclusion of a representative into the parity kernel. -/
def rankThreeToParity (j : Fin 5) : residualCandidate (rankThreeIndex j) →* ParityKernel :=
  Subgroup.inclusion (rankThree_le_parity j)

/-- The concrete binary rank-three quotient homomorphism. -/
def rankThreeProjection (j : Fin 5) :
    residualCandidate (rankThreeIndex j) →* OrderProfileQuotient 3 :=
  (rankThreeDecode j).comp (parityProjection.comp (rankThreeToParity j))

/-- The ordered ambient basis lifts fixed by the profile convention. -/
def rankThreeLift (j : Fin 5) (k : Fin 3) : SylowModel :=
  (![![root 3, root 0 * root 1, rootOne ^ 2 * root 1],
    ![root 1 * root 3, root 0, rootOne ^ 2],
    ![root 1, root 0, rootOne ^ 2],
    ![root 1, root 0 * root 3, rootOne ^ 2 * root 3],
    ![root 1 * root 3, root 0, rootOne ^ 2 * root 3]] j) k

/-- Every chosen lift belongs to the original representative. -/
theorem rankThreeLift_mem (j : Fin 5) (k : Fin 3) :
    rankThreeLift j k ∈ residualCandidate (rankThreeIndex j) := by
  apply Subgroup.mem_sup_right
  apply Subgroup.subset_closure
  fin_cases j <;> fin_cases k
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) |
    exact Or.inr (Or.inr (Or.inl rfl)) | exact Or.inr (Or.inr (Or.inr rfl))

/-- The common paired root belongs to each representative. -/
theorem rankThree_pair_mem (j : Fin 5) :
    root 2 * root 3 ∈ residualCandidate (rankThreeIndex j) := by
  fin_cases j
  · apply Subgroup.mul_mem <;> apply Subgroup.mem_sup_right <;> apply Subgroup.subset_closure
    all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
  all_goals apply Subgroup.mem_sup_right; apply Subgroup.subset_closure; exact Or.inl rfl

private theorem rankThree_parity_kernel_le_of_tail_pair (H : Subgroup SylowModel)
    (ht : tailSubgroup ≤ H) (hp : root 2 * root 3 ∈ H)
    (x : ParityKernel) (hx : parityProjection x = 1) : x.val ∈ H := by
  obtain ⟨hr, h0, h1, h23⟩ := (mem_parityProjection_ker x).mp hx
  have hpair (b : ZMod 2) :
      root 2 ^ b.val * root 3 ^ b.val = (root 2 * root 3) ^ b.val :=
    (by decide +kernel : ∀ b : ZMod 2,
      root 2 ^ b.val * root 3 ^ b.val = (root 2 * root 3) ^ b.val) b
  have hroot (i : CoreRoot) : (SemidirectProduct.inl (Core.root i) : SylowModel) = root i := rfl
  have hw := congrArg (SemidirectProduct.inl : Core →* SylowModel) (Core.normal_form x.val.left)
  simp only [map_mul, map_pow, hroot, h0, h1, h23,
    ZMod.val_zero, pow_zero, one_mul, hpair] at hw
  have he : (SemidirectProduct.inl x.val.left : SylowModel) = x.val :=
    SemidirectProduct.ext rfl hr.symm
  rw [he] at hw
  rw [← hw]
  have htail (i : CoreRoot) (hi : 4 ≤ i.val) : root i ∈ H :=
    ht (Subgroup.subset_closure ⟨i, hi, rfl⟩)
  repeat apply Subgroup.mul_mem
  · exact H.pow_mem hp _
  all_goals exact H.pow_mem (htail _ (by decide)) _

private def rankThreeAmbient (j : Fin 5) : Subgroup SylowModel :=
  (((rankThreeEncode j).comp ((rankThreeDecode j).comp parityProjection)).eqLocus
    parityProjection).map ParityKernel.subtype

private theorem rankThree_le_ambient (j : Fin 5) :
    residualCandidate (rankThreeIndex j) ≤ rankThreeAmbient j := by
  apply sup_le
  · intro x hx
    have hp := rankThree_le_parity j (tailSubgroup_le_residualCandidate _ hx)
    refine ⟨⟨x, hp⟩, ?_, rfl⟩
    change rankThreeEncode j (rankThreeDecode j (parityCoordinates x)) = parityCoordinates x
    obtain ⟨hr,h0,h1,h2,h3⟩ := (mem_tailSubgroup x).mp hx
    have hc : parityCoordinates x = 1 := by
      change (![_, _, _, _] : Fin 4 → ZMod 2) = 0
      funext i
      fin_cases i
      · change ((x.right.toAdd.val / 2 : ℕ) : ZMod 2) = 0
        rw [hr]; rfl
      · exact h0
      · exact h1
      · change x.left.b2 + x.left.b3 = 0
        rw [h2,h3,add_zero]
    rw [hc, map_one, map_one]
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    have hp := rankThree_le_parity j (Subgroup.mem_sup_right (Subgroup.subset_closure hx))
    refine ⟨⟨x, hp⟩, ?_, rfl⟩
    change rankThreeEncode j (rankThreeDecode j (parityCoordinates x)) = parityCoordinates x
    fin_cases j <;> rcases hx with rfl | rfl | rfl | rfl
    all_goals decide +kernel

/-- The parity coordinates are reconstructed from the rank-three quotient. -/
theorem rankThree_coordinates (j : Fin 5) (x : residualCandidate (rankThreeIndex j)) :
    rankThreeEncode j (rankThreeProjection j x) = parityCoordinates x.val := by
  obtain ⟨y, hy, he⟩ := rankThree_le_ambient j x.property
  change rankThreeEncode j (rankThreeDecode j (parityCoordinates y.val)) =
    parityCoordinates y.val at hy
  change y.val = x.val at he
  change rankThreeEncode j (rankThreeDecode j (parityCoordinates x.val)) = _
  simpa only [he] using hy

/-- The ordered basis lifts as elements of the representative. -/
def rankThreeBasisLift (j : Fin 5) (k : Fin 3) : residualCandidate (rankThreeIndex j) :=
  ⟨rankThreeLift j k, rankThreeLift_mem j k⟩

/-- An explicit representative of every binary quotient value. -/
def rankThreeWord (j : Fin 5) (v : OrderProfileQuotient 3) :
    residualCandidate (rankThreeIndex j) :=
  rankThreeBasisLift j 0 ^ (v.toAdd 0).val *
    rankThreeBasisLift j 1 ^ (v.toAdd 1).val *
    rankThreeBasisLift j 2 ^ (v.toAdd 2).val

/-- The basis word realizes precisely the encoded parity coordinate. -/
theorem rankThreeWord_coordinates : ∀ j v,
    parityProjection (rankThreeToParity j (rankThreeWord j v)) = rankThreeEncode j v := by
  decide +kernel

/-- Every parity element in the encoded subspace belongs to the representative. -/
theorem rankThree_mem_of_coordinates (j : Fin 5) (x : ParityKernel)
    (hx : rankThreeEncode j (rankThreeDecode j (parityProjection x)) = parityProjection x) :
    x.val ∈ residualCandidate (rankThreeIndex j) := by
  let z := rankThreeWord j (rankThreeDecode j (parityProjection x))
  have hz : parityProjection (rankThreeToParity j z) = parityProjection x :=
    (rankThreeWord_coordinates j _).trans hx
  have hk : parityProjection (x * (rankThreeToParity j z)⁻¹) = 1 := by
    rw [map_mul, map_inv, hz, mul_inv_cancel]
  have hm := rankThree_parity_kernel_le_of_tail_pair _ (tailSubgroup_le_residualCandidate _)
    (rankThree_pair_mem j) _ hk
  change x.val * z.val⁻¹ ∈ residualCandidate (rankThreeIndex j) at hm
  exact (Subgroup.mul_mem_cancel_right _ (Subgroup.inv_mem _ z.property)).mp hm

/-- Seven free bits parametrize an element over a quotient value. -/
def rankThreeElement (j : Fin 5) (v : OrderProfileQuotient 3) (w : Fin 7 → ZMod 2) :
    residualCandidate (rankThreeIndex j) :=
  ⟨(parityElement (rankThreeEncode j v) w).val, rankThree_mem_of_coordinates j _ (by
    rw [parityProjection_element, rankThreeDecode_encode])⟩

/-- The parametrized element has the prescribed quotient value. -/
theorem rankThreeProjection_element (j : Fin 5) (v : OrderProfileQuotient 3)
    (w : Fin 7 → ZMod 2) : rankThreeProjection j (rankThreeElement j v w) = v := by
  change rankThreeDecode j (parityProjection (parityElement (rankThreeEncode j v) w)) = v
  rw [parityProjection_element, rankThreeDecode_encode]

/-- Every binary quotient value is realized. -/
theorem rankThreeProjection_surjective (j : Fin 5) : Function.Surjective (rankThreeProjection j) :=
  fun v => ⟨rankThreeElement j v 0, rankThreeProjection_element j v 0⟩

/-- All five profile tables have rank three. -/
theorem rankThree_rank (j : Fin 5) : orderProfileRank (rankThreeIndex j) = 3 := by
  fin_cases j <;> rfl

/-- The required order-count table, uniformly typed over rank three. -/
def rankThreeCounts (j : Fin 5) (v : OrderProfileQuotient 3) : ℕ × ℕ × ℕ :=
  ![orderProfileCounts 2 v, orderProfileCounts 3 v, orderProfileCounts 4 v,
    orderProfileCounts 6 v, orderProfileCounts 8 v] j

/-- The seven free coordinates in a quotient fiber. -/
def rankThreeRemainder (j : Fin 5) (x : residualCandidate (rankThreeIndex j)) : Fin 7 → ZMod 2 :=
  parityRemainder (rankThreeToParity j x)

/-- Quotient and remainder coordinates reconstruct every element. -/
theorem rankThreeElement_coordinates (j : Fin 5) (x : residualCandidate (rankThreeIndex j)) :
    rankThreeElement j (rankThreeProjection j x) (rankThreeRemainder j x) = x := by
  apply Subtype.ext
  change (parityElement (rankThreeEncode j (rankThreeProjection j x))
    (parityRemainder (rankThreeToParity j x))).val = x.val
  rw [rankThree_coordinates]
  exact congrArg Subtype.val (parityElement_coordinates (rankThreeToParity j x))

/-- An explicit bijection between each fiber and seven binary coordinates. -/
def rankThreeFiberEquiv (j : Fin 5) (v : OrderProfileQuotient 3) :
    {x : residualCandidate (rankThreeIndex j) // rankThreeProjection j x = v} ≃
      (Fin 7 → ZMod 2) where
  toFun x := rankThreeRemainder j x.val
  invFun w := ⟨rankThreeElement j v w, rankThreeProjection_element j v w⟩
  left_inv x := by
    apply Subtype.ext
    change rankThreeElement j v (rankThreeRemainder j x.val) = x.val
    simpa only [x.property] using rankThreeElement_coordinates j x.val
  right_inv w := by funext i; fin_cases i <;> rfl

/-- The concrete projection kernel has order 128. -/
theorem rankThreeProjection_ker_card (j : Fin 5) : Nat.card (rankThreeProjection j).ker = 128 := by
  change Nat.card {x : residualCandidate (rankThreeIndex j) // rankThreeProjection j x = 1} = 128
  rw [Nat.card_congr (rankThreeFiberEquiv j 1), Nat.card_fun]
  simp

/-- Order fibers correspond to order predicates on seven binary coordinates. -/
def rankThreeOrderFiberEquiv (j : Fin 5) (v : OrderProfileQuotient 3) (n : ℕ) :
    {x : residualCandidate (rankThreeIndex j) // rankThreeProjection j x = v ∧ orderOf x = n} ≃
      {w : Fin 7 → ZMod 2 // orderOf (rankThreeElement j v w) = n} where
  toFun x := ⟨rankThreeRemainder j x.val, by
    have h : rankThreeElement j v (rankThreeRemainder j x.val) = x.val := by
      simpa only [x.property.1] using rankThreeElement_coordinates j x.val
    rw [h]
    exact x.property.2⟩
  invFun w := ⟨rankThreeElement j v w.val, rankThreeProjection_element j v w.val, w.property⟩
  left_inv x := by
    apply Subtype.ext
    change rankThreeElement j v (rankThreeRemainder j x.val) = x.val
    simpa only [x.property.1] using rankThreeElement_coordinates j x.val
  right_inv w := by
    apply Subtype.ext
    funext i; fin_cases i <;> rfl

/-- Order counts reduce to the explicit seven-bit parametrization. -/
theorem rankThreeProjection_fiberProfile (j : Fin 5) (v : OrderProfileQuotient 3) (n : ℕ) :
    Subgroup.fiberProfile (rankThreeProjection j) orderOf v n =
      Nat.card {w : Fin 7 → ZMod 2 // orderOf (rankThreeElement j v w) = n} := by
  classical
  let : Fintype (residualCandidate (rankThreeIndex j)) := Fintype.ofFinite _
  rw [Subgroup.fiberProfile_eq_card_filter]
  have h := Nat.card_congr (rankThreeOrderFiberEquiv j v n)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

/-- The common coordinate description of the five projection kernels. -/
theorem mem_rankThreeProjection_ker (j : Fin 5) (x : residualCandidate (rankThreeIndex j)) :
    x ∈ (rankThreeProjection j).ker ↔
      x.val.right = 1 ∧ x.val.left.b0 = 0 ∧ x.val.left.b1 = 0 ∧ x.val.left.b2 = x.val.left.b3 := by
  refine Iff.trans ?_ (mem_parityProjection_ker (rankThreeToParity j x))
  change rankThreeProjection j x = 1 ↔ parityProjection (rankThreeToParity j x) = 1
  constructor
  · intro hx
    have h := rankThree_coordinates j x
    rw [hx, map_one] at h
    exact h.symm
  · intro hx
    change rankThreeDecode j (parityProjection (rankThreeToParity j x)) = 1
    rw [hx, map_one]

end ReeTwo.SylowModel
