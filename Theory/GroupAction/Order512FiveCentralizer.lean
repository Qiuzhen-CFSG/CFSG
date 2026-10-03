module

public import Theory.GroupAction.BinaryAlternatingFiveKernel
public import Theory.GroupAction.Order512FiveStructure
public import Theory.GroupTheory.Commutator.CentralQuotientPairing
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Commuting derived cosets in the order-512 core

For the class-three two-group of order 512 with an order-five actor fixing
only central elements, the commutator pairing descends to two elementary
groups of order sixteen: V/V′ and V′/Z(V). Both carry fixed-point-free
five-actions. The alternating-pairing kernel theorem shows that commuting
with b outside V′ forces xV′ to be either V′ or bV′.

The nonzero-evaluation hypothesis follows from V′=Z₂(V). This calculation
controls every commuting element, including those of order greater than two.
It supplies C_J(a)=F in Parrott, *A characterization of the Tits' simple group*
(1972), p.678, from the intrinsic structure on pp.672–674.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupAction

private def liftPairingHom {V W : Type*} [Group V] [CommGroup W] :
    (V →* W) →* (V ⧸ commutator V →* W) where
  toFun f := QuotientGroup.lift _ f (Abelianization.commutator_subset_ker f)
  map_one' := by ext x; rfl
  map_mul' := by intros; ext x; rfl

/-- In the intrinsic order-512 core, an element commuting with b outside
the derived subgroup lies in the derived coset of either 1 or b. -/
public theorem parrott_commuting_derived_cosets {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hV : IsPGroup 2 V) (hcard : Nat.card V = 512)
    (hclass : 3 ≤ Group.nilpotencyClass V) (hA : Nat.card A = 5)
    (hfixed : FixedPoints.subgroup A V ≤ center V)
    (b x : V) (hb : b ∉ commutator V) (hbx : Commute b x) :
    x ∈ commutator V ∨ b * x ∈ commutator V := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 V) := ⟨hV⟩
  let _ : Group.IsNilpotent V := hV.isNilpotent
  obtain ⟨_, hZcard, hPhi, hUpper, hElem, hDcard⟩ :=
    parrott_twoGroup_structure hV hcard hclass hA hfixed
  let D := commutator V
  let Z := (center V).subgroupOf D
  let W := D ⧸ Z
  let B := V ⧸ D
  let q : V →* B := QuotientGroup.mk' D
  let r := QuotientGroup.mk' Z
  let _ : IsElementaryAbelian 2 D := hElem
  let _ : IsElementaryAbelian 2 W := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := (Group.exponent_quotient_dvd Z).trans
      (IsElementaryAbelian.exponent_dvd_p 2 D) }
  let _ : IsElementaryAbelian 2 B := by
    let _ := isElementaryAbelian_quotient_frattini (R := V) (p := 2)
    let e := QuotientGroup.quotientMulEquivOfEq hPhi
    refine { is_comm := ⟨fun x y => e.injective ?_⟩, exponent_dvd_p := ?_ }
    · simpa only [map_mul] using mul_comm (e x) (e y)
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply e.injective
        simpa only [map_pow, map_one] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ frattini V)) (e x))
  let _ : IsInvariant A V D := isInvariant_of_characteristic D
  let _ : IsInvariant A V (center V) := isInvariant_of_characteristic (center V)
  let _ : MulDistribMulAction A B := quotientMulDistribMulAction D
    (isInvariant_of_characteristic D)
  let _ : MulDistribMulAction A W := quotientMulDistribMulAction Z
    (isInvariant_subgroupOf (center V) D)
  have hZD : center V ≤ D := by
    rw [show D = Subgroup.upperCentralSeries V 2 from hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using Subgroup.upperCentralSeries_mono V (show 1 ≤ 2 by decide)
  have hBcard : Nat.card B = 16 := by
    have hc := D.index_mul_card
    change Nat.card B * Nat.card D = Nat.card V at hc
    rw [hDcard, hcard] at hc
    omega
  have hWcard : Nat.card W = 16 := by
    have hc := Z.index_mul_card
    change Nat.card W * Nat.card Z = Nat.card D at hc
    rw [Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv, hZcard, hDcard] at hc
    omega
  have hBfixed : FixedPoints.subgroup A B = ⊥ := by
    change FixedPoints.subgroup A (V ⧸ D) = ⊥
    rw [fixedPoints_subgroup_quotient_eq_map_of_solvable_coprime
      (inferInstance : Group.IsSolvable V) (by rw [hA, hcard]; decide)
      D (isInvariant_of_characteristic D), Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hfixed.trans hZD
  have hWfixed : FixedPoints.subgroup A W = ⊥ :=
    (parrott_quotient_actions hV hclass hA hfixed).2.1
  have hcomm : ⁅D, (⊤ : Subgroup V)⁆ ≤ center V := by
    rw [show D = Subgroup.upperCentralSeries V 2 from hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using commutator_upperCentralSeries_top_le V 1
  obtain ⟨f₀, hf₀⟩ := exists_central_quotient_commutator_pairing D (center V) le_rfl hcomm
  let f : B →* (B →* W) := QuotientGroup.lift D (liftPairingHom.comp f₀)
    (Abelianization.commutator_subset_ker _)
  have hf (u v : V) : f (q u) (q v) =
      r ⟨⁅u,v⁆, commutator_mem_commutator (mem_top u) (mem_top v)⟩ := hf₀ u v
  have hsq (w : W) : w * w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w
  have halt : ∀ y, f y y = 1 := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective D y
    change f (q u) (q u) = 1
    rw [hf]
    exact (congrArg r (Subtype.ext (by simp))).trans (map_one r)
  have hsymm : ∀ y t, f y t = f t y := by
    intro y t
    have hh := halt (y * t)
    simp only [map_mul, MonoidHom.mul_apply, halt, one_mul, mul_one] at hh
    exact ((eq_inv_of_mul_eq_one_left hh).trans (inv_eq_of_mul_eq_one_left (hsq _))).symm
  have hequiv : ∀ (a : A) (y t : B), f (a • y) (a • t) = a • f y t := by
    intro a y t
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective D y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective D t
    change f (q (a • u)) (q (a • v)) = a • f (q u) (q v)
    rw [hf, hf]
    change r _ = r (a • _)
    apply congrArg r
    apply Subtype.ext
    change ⁅a • u, a • v⁆ = a • ⁅u,v⁆
    simp only [commutatorElement_def, smul_mul', smul_inv']
  have hbq : q b ≠ 1 := fun hh => hb ((QuotientGroup.eq_one_iff b).mp hh)
  have hbn : f (q b) ≠ 1 := by
    intro hh
    apply hb
    rw [hUpper, Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    have he : f (q b) (q y) = 1 := DFunLike.congr_fun hh (q y)
    rw [hf] at he
    have hz := (QuotientGroup.eq_one_iff (N := Z) _).mp he
    exact hz
  have hfx : f (q b) (q x) = 1 := by
    rw [hf]
    exact (congrArg r (Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr hbx))).trans
      (map_one r)
  rcases alternating_pairing_kernel_eq_line_of_five hA hBcard hWcard hBfixed hWfixed
    f halt hsymm hequiv (q b) hbq hbn (q x) hfx with hx | hx
  · exact Or.inl ((QuotientGroup.eq_one_iff x).mp hx)
  · right
    apply (QuotientGroup.eq_one_iff (b * x)).mp
    change q (b * x) = 1
    rw [map_mul, hx]
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B) (q b)

end Theory.GroupAction
