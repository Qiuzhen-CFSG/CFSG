module

public import Stellmacher.Recognition.NormalEightQuaternionAbelianSetup
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber
public import Theory.GroupTheory.QuaternionCentralProductSquareAction
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution
public import Theory.GroupTheory.InvolutionOrbitCentralizerSupplement

/-!
# The fixed four and involution orbit in the cyclic-four quaternion case

The outside involution is a square modulo the core, so its action is an
inner twist of a square of a two-power-order automorphism. The quaternion
square-action theorem makes both factor restrictions outer. The fixed-core
and cocycle calculations then give an elementary fixed four and one core
orbit of involutions in the coset. This route preserves the selected
involution without choosing an odd-order actor.

Source: Janko–Thompson (1970), §4, case (a), printed pp.390–391.
-/

open Subgroup
open Stellmacher.Recognition.NormalFourCentralOmegaTwo
namespace Stellmacher.Recognition.NormalEightNonnormalImage
variable {G : Type*} [Group G] [Finite G]

/-- The selected outside involution has a fixed four and a single core conjugacy orbit in its coset. -/
public theorem quaternion_cyclic_four_fixed_core_and_orbit
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hindex : (omegaCorePreimage S).index = 4) [IsCyclic (S ⧸ omegaCorePreimage S)]
    (B C : Subgroup (pCore 2 (OmegaQuotient S)))
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hjoin : B ⊔ C = ⊤)
    (hinter : Nat.card (B ⊓ C : Subgroup (pCore 2 (OmegaQuotient S))) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (t : S) (ht : orderOf t = 2) (hout : t ∉ omegaCorePreimage S) :
    IsElementaryAbelian 2 (omegaCorePreimage S ⊓ centralizer ({t} : Set S) : Subgroup S) ∧
      Nat.card (omegaCorePreimage S ⊓ centralizer ({t} : Set S) : Subgroup S) = 4 ∧
      ∀ v : S, v ^ 2 = 1 → v * t⁻¹ ∈ omegaCorePreimage S →
        ∃ p : omegaCorePreimage S, (p : S) * t * (p : S)⁻¹ = v := by
  let P := omegaCorePreimage S
  let e := omegaCorePreimageEquiv S
  let a := normalConjThrough P e
  let q := QuotientGroup.mk' P
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ha2 : a t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hcentral : centralizer (P : Set S) ≤ P := by
    intro s hs
    apply omegaQuotient_centralizer_pCore_le hN S hZ
    intro x hx
    rw [← omegaCorePreimage_map S] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    simpa only [map_mul] using congrArg (omegaQuotientHom S) (hs k hk)
  have haout : ¬ ∃ p, a t = MulAut.conj p :=
    normalConjThrough_not_inner P e hcentral t hout
  have hquot : Nat.card (S ⧸ P) = 4 := hindex
  have hqt : (q t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hqtne : q t ≠ 1 := fun h => hout ((QuotientGroup.eq_one_iff _).mp h)
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S ⧸ P)
  rw [hquot] at hb
  have hb2 : orderOf (b ^ 2) = 2 := by rw [orderOf_pow, hb]; norm_num
  have hroot : b ^ 2 = q t := IsCyclic.eq_of_orderOf_eq_two hb2 (orderOf_eq_prime hqt hqtne)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective P b
  have hsP : t * (s ^ 2)⁻¹ ∈ P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (t * (s ^ 2)⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hroot, mul_inv_cancel]
  let p : P := ⟨t * (s ^ 2)⁻¹, hsP⟩
  have htp : t = (p : S) * s ^ 2 := by simp [p]
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_pow_pow_eq_one s
  have has : a s ^ (2 ^ n) = 1 := by rw [← map_pow, hn, map_one]
  have hat : a t = MulAut.conj (e p) * a s ^ 2 := by
    rw [htp, map_mul, map_pow]
    congr 1
    exact normalConjThrough_coe P e p
  obtain ⟨hBB, hCC, hBO, hCO⟩ := quaternion_central_product_square_action
    B C hB hC hjoin hinter hcomm (a t) (a s) (e p) n has hat haout
  obtain ⟨helem, hcard, horbit⟩ := quaternion_central_product_outer_involution
    B C hB hC hjoin hinter hcomm (a t) ha2 hBB hCC hBO hCO
  obtain ⟨helem', hcard'⟩ := normalConjThrough_fixed_elementary_card P e t 4 helem hcard
  exact ⟨helem', hcard', fun v hv hcoset =>
    normalConjThrough_involution_orbit P e t ht2 horbit v hv hcoset⟩
end Stellmacher.Recognition.NormalEightNonnormalImage
