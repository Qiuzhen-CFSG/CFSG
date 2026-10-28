module
public import Theory.Mathieu.M22.CentralCoverPrelude
public import Theory.GroupTheory.CyclicFourCentralSquares

/-!
# Squaring in actual cyclic-four central covers of M₂₂

Quotient by the squares of the cyclic center. The resulting map to the
literal degree-22 M₂₂ has central kernel of order two. Involution fusion
and the elementary hexad kernel force every lift of an involution through
this double cover to have square one. Consequently squares above M₂₂
involutions in the original cover lie in the shared central involution.
Multiplying a lift by a suitable central element then produces an involution.

Source: Aschbacher–Smith I.2.2(ii), (6), printed pp.410 and 412.
No splitting or central-product recognition is assumed or asserted here.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22CentralCover
open Subgroup Theory.GroupTheory.DoubleCoverInvolutionLifting
variable {K : Type*} [Group K]

section Double
variable [Finite K]

/-- The involution-lifting argument also applies to a specified surjection. -/
theorem involutions_lift_of_kernel_card_two (f : K →* M22)
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 2)
    (u : M22) (hu : orderOf u = 2) :
    ∃ v : K, f v = u ∧ orderOf v = 2 := by
  let E := m22HexadPointwiseKernel m22Hexad123
  let : IsElementaryAbelian 2 E := m22HexadPointwiseKernel_elementaryAbelian m22Hexad123_mem
  obtain ⟨x, hx, _, hxn⟩ := exists_involution_above_elementary_subgroup f hf hk E
    (by rw [m22HexadPointwiseKernel_card m22Hexad123_mem]; decide)
  have hxo : orderOf (f x) = 2 := orderOf_eq_prime_iff.mpr ⟨by
    rw [← map_pow, show x ^ 2 = 1 from hx ▸ pow_orderOf_eq_one x, map_one], hxn⟩
  exact involution_lift_of_isConj f hf hx (m22_involutions_isConj _ u hxo hu)

/-- Centrality upgrades existence of lifts to a square identity for every lift. -/
theorem square_eq_one_of_central_kernel_card_two (f : K →* M22)
    (hf : Function.Surjective f) (hc : f.ker ≤ center K)
    (hk : Nat.card f.ker = 2) (x : K) (hx : f x ^ 2 = 1) : x ^ 2 = 1 := by
  have hs (a : K) (ha : f a = 1) : a ^ 2 = 1 := by
    have hp := pow_card_eq_one' (x := (⟨a, ha⟩ : f.ker))
    rw [hk] at hp
    exact congrArg Subtype.val hp
  by_cases hx1 : f x = 1
  · exact hs x hx1
  obtain ⟨y, hy, hy2⟩ := involutions_lift_of_kernel_card_two f hf hk (f x)
    (orderOf_eq_prime_iff.mpr ⟨hx, hx1⟩)
  have hd : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hy, mul_inv_cancel]
  have hz : x * y⁻¹ ∈ center K := hc hd
  have hcomm : Commute (x * y⁻¹) y := (mem_center_iff.mp hz y).symm
  have hp := hcomm.mul_pow 2
  rw [inv_mul_cancel_right, hs _ hd,
    show y ^ 2 = 1 from hy2 ▸ pow_orderOf_eq_one y, mul_one] at hp
  exact hp

end Double

/-- The actual quotient by the squares of the center, retaining the map to M₂₂. -/
noncomputable def quarticReductionProjection (e : (K ⧸ center K) ≃* M22) :
    (K ⧸ centralSquares K) →* M22 :=
  QuotientGroup.lift (centralSquares K) (projection e) (by
    rw [projection_ker]
    exact centralSquares_le_center)

@[simp] theorem quarticReductionProjection_mk (e : (K ⧸ center K) ≃* M22) (x : K) :
    quarticReductionProjection e (QuotientGroup.mk x) = projection e x := rfl

theorem quarticReductionProjection_surjective (e : (K ⧸ center K) ≃* M22) :
    Function.Surjective (quarticReductionProjection e) :=
  QuotientGroup.lift_surjective_of_surjective _ _ (projection_surjective e) _

theorem quarticReductionProjection_ker (e : (K ⧸ center K) ≃* M22) :
    (quarticReductionProjection e).ker =
      (center K).map (QuotientGroup.mk' (centralSquares K)) := by
  rw [quarticReductionProjection, QuotientGroup.ker_lift, projection_ker]

private theorem reduction_ker_central (e : (K ⧸ center K) ≃* M22) :
    (quarticReductionProjection e).ker ≤ center (K ⧸ centralSquares K) := by
  rw [quarticReductionProjection_ker]
  rintro y ⟨z, hz, rfl⟩
  apply mem_center_iff.mpr
  intro w
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (centralSquares K) w
  simpa only [map_mul] using congrArg (QuotientGroup.mk' (centralSquares K))
    (mem_center_iff.mp hz t)

/-- The center of the reduced cover is precisely the image of the original center. -/
theorem quarticReduction_center (e : (K ⧸ center K) ≃* M22) :
    center (K ⧸ centralSquares K) = (quarticReductionProjection e).ker := by
  apply le_antisymm ?_ (reduction_ker_central e)
  intro x hx
  have hf : quarticReductionProjection e x ∈ center M22 := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := quarticReductionProjection_surjective e y
    simpa only [map_mul] using congrArg (quarticReductionProjection e)
      (mem_center_iff.mp hx z)
  rw [m22_center_eq_bot] at hf
  exact mem_bot.mp hf

/-- An actual central-quotient equivalence for applying the binary-cover APIs. -/
noncomputable def quarticReductionEquiv (e : (K ⧸ center K) ≃* M22) :
    ((K ⧸ centralSquares K) ⧸ center (K ⧸ centralSquares K)) ≃* M22 :=
  (QuotientGroup.quotientMulEquivOfEq (quarticReduction_center e)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (quarticReductionProjection e)
      (quarticReductionProjection_surjective e))

/-- The binary-cover map is exactly the descended original map. -/
@[simp] theorem quarticReductionEquiv_projection (e : (K ⧸ center K) ≃* M22)
    (x : K ⧸ centralSquares K) :
    projection (quarticReductionEquiv e) x = quarticReductionProjection e x := rfl

/-- Restriction of the same quotient map to any actual local full preimage. -/
noncomputable def quarticReductionLocal (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    preimage e H →* preimage (quarticReductionEquiv e) H :=
  ((QuotientGroup.mk' (centralSquares K)).comp (preimage e H).subtype).codRestrict _
    (fun x => x.property)

@[simp] theorem quarticReductionLocal_coe (e : (K ⧸ center K) ≃* M22)
    (H : Subgroup M22) (x : preimage e H) :
    (quarticReductionLocal e H x : K ⧸ centralSquares K) =
      QuotientGroup.mk' (centralSquares K) x := rfl

theorem quarticReductionLocal_surjective (e : (K ⧸ center K) ≃* M22)
    (H : Subgroup M22) : Function.Surjective (quarticReductionLocal e H) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (centralSquares K) y.val
  have hm : x ∈ preimage e H := by
    change projection (quarticReductionEquiv e)
      (QuotientGroup.mk' (centralSquares K) x) ∈ H
    rw [hx]
    exact y.property
  exact ⟨⟨x, hm⟩, Subtype.ext hx⟩

theorem quarticReductionLocal_ker (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    (quarticReductionLocal e H).ker = (centralSquares K).subgroupOf (preimage e H) := by
  ext x
  change quarticReductionLocal e H x = 1 ↔ (x : K) ∈ centralSquares K
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

variable [Finite K]

theorem quarticReduction_center_card (e : (K ⧸ center K) ≃* M22)
    [IsCyclic (center K)] (hZ : Nat.card (center K) = 4) :
    Nat.card (center (K ⧸ centralSquares K)) = 2 := by
  rw [quarticReduction_center e, quarticReductionProjection_ker]
  exact centralSquares_center_image_card hZ

/-- Squares above quotient involutions lie in the actual central involution subgroup. -/
theorem quartic_square_mem (e : (K ⧸ center K) ≃* M22)
    [IsCyclic (center K)] (hZ : Nat.card (center K) = 4)
    (x : K) (hx : projection e x ^ 2 = 1) : x ^ 2 ∈ centralSquares K := by
  have hk2 : Nat.card (quarticReductionProjection e).ker = 2 := by
    rw [quarticReductionProjection_ker]
    exact centralSquares_center_image_card hZ
  have hs := square_eq_one_of_central_kernel_card_two (quarticReductionProjection e)
    (quarticReductionProjection_surjective e) (reduction_ker_central e) hk2
    (QuotientGroup.mk' (centralSquares K) x) hx
  apply (QuotientGroup.eq_one_iff (N := centralSquares K) _).mp
  change (QuotientGroup.mk' (centralSquares K)) (x ^ 2) = 1
  rw [map_pow]
  exact hs

/-- Every M₂₂ involution also has an involution lift through the cyclic-four cover. -/
theorem quartic_involutions_lift (e : (K ⧸ center K) ≃* M22)
    [IsCyclic (center K)] (hZ : Nat.card (center K) = 4)
    (u : M22) (hu : orderOf u = 2) :
    ∃ v : K, projection e v = u ∧ orderOf v = 2 := by
  obtain ⟨x, hx⟩ := projection_surjective e u
  have hxs := quartic_square_mem e hZ x (by rw [hx, ← hu]; exact pow_orderOf_eq_one u)
  obtain ⟨z, hz⟩ := mem_centralSquares.mp hxs
  have hzq : projection e z = 1 := by
    change (z : K) ∈ (projection e).ker
    rw [projection_ker]
    exact z.property
  have hproj : projection e (x * (z : K)⁻¹) = u := by
    rw [map_mul, map_inv, hzq, inv_one, mul_one, hx]
  refine ⟨x * (z : K)⁻¹, hproj, orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩⟩
  · have hc : Commute x (z : K)⁻¹ :=
      mem_center_iff.mp ((center K).inv_mem z.property) x
    rw [hc.mul_pow, inv_pow, hz, mul_inv_cancel]
  · intro h
    have : u = 1 := hproj.symm.trans (by rw [h, map_one])
    simp [this] at hu

end Sporadic.Mathieu.M22CentralCover
