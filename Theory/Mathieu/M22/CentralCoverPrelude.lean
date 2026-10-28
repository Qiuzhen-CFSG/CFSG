module

public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.GroupTheory.DoubleCoverInvolutionLifting
public import Theory.GroupTheory.PCoreSurjective
public import Theory.Frattini.PGroup

/-!
# Elementary preimages in central double covers of M₂₂

The actual hexad kernel has order sixteen. The double-cover involution
lifting theorem gives a noncentral involution above that kernel, and the
single involution class of the degree-22 Mathieu group propagates the lift.
Centrality of the kernel then makes every full elementary preimage elementary.
We retain the actual quotient map and arbitrary local subgroups throughout.

Source: Aschbacher–Smith, I.2.2(ii) and (6), printed pp.410 and 412,
combined manuscript of 1 March 2004. No multiplier or cover recognition is
asserted here; the order of the actual center is an explicit hypothesis.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22CentralCover
open Subgroup Theory.GroupTheory.DoubleCoverInvolutionLifting
variable {K : Type*} [Group K]

/-- The specified isomorphism after the literal central quotient map. -/
noncomputable def projection (e : (K ⧸ center K) ≃* M22) : K →* M22 :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

theorem projection_surjective (e : (K ⧸ center K) ≃* M22) :
    Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

@[simp] theorem projection_ker (e : (K ⧸ center K) ≃* M22) :
    (projection e).ker = center K := by
  exact (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (center K)) e).trans
    (QuotientGroup.ker_mk' (center K))

/-- A full preimage, with no choice of representative local subgroup. -/
noncomputable def preimage (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) : Subgroup K :=
  H.comap (projection e)

theorem center_le_preimage (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    center K ≤ preimage e H := by
  rw [← projection_ker e]
  exact (projection e).ker_le_comap H

/-- The restriction maps the full preimage onto precisely the given subgroup. -/
noncomputable def localProjection (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    preimage e H →* H := (projection e).subgroupComap H

theorem localProjection_surjective (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    Function.Surjective (localProjection e H) :=
  (projection e).subgroupComap_surjective_of_surjective H (projection_surjective e)

@[simp] theorem localProjection_ker (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    (localProjection e H).ker = (center K).subgroupOf (preimage e H) := by
  ext x
  change (⟨projection e x, x.property⟩ : H) = 1 ↔ (x : K) ∈ center K
  rw [Subtype.ext_iff]
  exact (show projection e x = 1 ↔ (x : K) ∈ (projection e).ker from Iff.rfl).trans
    (by rw [projection_ker])

theorem localProjection_ker_card (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    Nat.card (localProjection e H).ker = Nat.card (center K) := by
  rw [localProjection_ker]
  exact Nat.card_congr (subgroupOfEquivOfLe (center_le_preimage e H)).toEquiv

theorem preimage_card (e : (K ⧸ center K) ≃* M22) (H : Subgroup M22) :
    Nat.card (preimage e H) = Nat.card H * Nat.card (center K) := by
  have hi : (localProjection e H).ker.index = Nat.card H := by
    rw [index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
      (localProjection e H) (localProjection_surjective e H)).toEquiv
  rw [← (localProjection e H).ker.index_mul_card, hi, localProjection_ker_card]

private theorem elementary_of_squares {A : Type*} [Group A]
    (hs : ∀ x : A, x ^ 2 = 1) : IsElementaryAbelian 2 A :=
  { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

variable [Finite K]

/-- All quotient involutions lift to involutions in the actual double cover. -/
theorem involutions_lift (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    (u : M22) (hu : orderOf u = 2) :
    ∃ v : K, projection e v = u ∧ orderOf v = 2 := by
  let E := m22HexadPointwiseKernel m22Hexad123
  let : IsElementaryAbelian 2 E := m22HexadPointwiseKernel_elementaryAbelian m22Hexad123_mem
  obtain ⟨x, hx, _, hxn⟩ := exists_involution_above_elementary_subgroup
    (projection e) (projection_surjective e) (by rw [projection_ker, hZ]) E
    (by rw [m22HexadPointwiseKernel_card m22Hexad123_mem]; decide)
  have hxo : orderOf (projection e x) = 2 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨?_, hxn⟩
    rw [← map_pow, show x ^ 2 = 1 from hx ▸ pow_orderOf_eq_one x, map_one]
  exact involution_lift_of_isConj (projection e) (projection_surjective e) hx
    (m22_involutions_isConj _ u hxo hu)

omit [Finite K] in
private theorem square_one_of_card_two (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 2) {x : K} (hx : projection e x = 1) : x ^ 2 = 1 := by
  have hz : x ∈ center K := projection_ker e ▸ hx
  have hp := pow_card_eq_one' (x := (⟨x, hz⟩ : center K))
  rw [hZ] at hp
  exact congrArg Subtype.val hp

/-- A full elementary preimage is elementary; centrality is essential here. -/
theorem elementary_preimage (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 2)
    (E : Subgroup M22) [IsElementaryAbelian 2 E] :
    IsElementaryAbelian 2 (preimage e E) := by
  have hs : ∀ x : preimage e E, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : K) ^ 2 = 1
    by_cases hx : projection e x = 1
    · exact square_one_of_card_two e hZ hx
    have hxo : orderOf (projection e x) = 2 :=
      orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian _ x.property, hx⟩
    obtain ⟨y, hy, hy2⟩ := involutions_lift e hZ _ hxo
    have hd : projection e ((x : K) * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hy, mul_inv_cancel]
    have hz : (x : K) * y⁻¹ ∈ center K := projection_ker e ▸ hd
    have hc : Commute ((x : K) * y⁻¹) y := (mem_center_iff.mp hz y).symm
    have hp := hc.mul_pow 2
    rw [inv_mul_cancel_right, square_one_of_card_two e hZ hd,
      show y ^ 2 = 1 from hy2 ▸ pow_orderOf_eq_one y, mul_one] at hp
    exact hp
  exact elementary_of_squares hs

/-- Core lifting in relative subgroup coordinates. -/
theorem localProjection_comap_twoCore (e : (K ⧸ center K) ≃* M22)
    (hZ : IsPGroup 2 (center K)) (H : Subgroup M22) :
    (pCore 2 H).comap (localProjection e H) = pCore 2 (preimage e H) := by
  apply (localProjection e H).comap_pCore_of_ker_isPGroup (localProjection_surjective e H)
  rw [localProjection_ker]
  exact hZ.comap_subtype

/-- Core lifting in ambient coordinates retains the actual native kernel. -/
theorem preimage_twoCore (e : (K ⧸ center K) ≃* M22)
    (hZ : IsPGroup 2 (center K)) (H : Subgroup M22) :
    preimage e ((pCore 2 H).map H.subtype) =
      (pCore 2 (preimage e H)).map (preimage e H).subtype := by
  rw [← localProjection_comap_twoCore e hZ H]
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    have hx : x ∈ preimage e H :=
      show projection e x ∈ H from he ▸ y.property
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change localProjection e H ⟨x, hx⟩ ∈ pCore 2 H
    exact (show y = localProjection e H ⟨x, hx⟩ from Subtype.ext he) ▸ hy
  · rintro ⟨y, hy, rfl⟩
    exact ⟨localProjection e H y, hy, rfl⟩

/-- The Frattini clause applies to every local subgroup with elementary two-core. -/
theorem local_twoCore_frattini (e : (K ⧸ center K) ≃* M22)
    (hZ : Nat.card (center K) = 2) (H : Subgroup M22)
    [IsElementaryAbelian 2 (pCore 2 H)] :
    frattini (pCore 2 (preimage e H)) = ⊥ := by
  let : IsElementaryAbelian 2 ((pCore 2 H).map H.subtype) := IsElementaryAbelian.map_subtype
  have hE := elementary_preimage e hZ ((pCore 2 H).map H.subtype)
  rw [preimage_twoCore e (IsPGroup.of_card (n := 1) (by simpa using hZ)) H] at hE
  let := hE
  let : IsElementaryAbelian 2 (pCore 2 (preimage e H)) := elementary_of_squares (by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (x.val : K)
      (show (x.val : K) ∈ (pCore 2 (preimage e H)).map (preimage e H).subtype from
        ⟨x.val, x.property, rfl⟩))
  let : Fact (IsPGroup 2 (pCore 2 (preimage e H))) := ⟨pCore_isPGroup⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

end Sporadic.Mathieu.M22CentralCover
