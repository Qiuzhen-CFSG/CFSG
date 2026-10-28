module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.Definitions
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.SquareCalculation
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.CoverCoordinates
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension
public import Theory.Mathieu.M12.SmallParabolicPair.CoverOrbits
public import Theory.Mathieu.M12.Properties.InvolutionFusion
public import Theory.Mathieu.M12.TwoCentralInvolutions

/-!
# M₁₂ local orbit, binary extension and core-square calculation

The actual five-orbit witness and the constructed coordinates on
R = O₂(O²(C_K(u))) discharge the local structural premises. In the elementary
branch, the cubic action and extra central-class involution give a retraction
of C_K(u) onto Z(K), contradicting restriction (i). Thus the literal quotient
R/⟨v₄⟩ has two embedded quaternion factors and exactly six order-four cosets
modulo the image of Z(K). The square calculation gives v₄ = v₅.

Fusion then forces every lift of the non-two-central class to have order
four. Re-marking the actual central quotient isomorphism proves the unique
core-square clause for every noncentral involution of K, preserving its
original centralizer, residual, core and quotient map.

The final theorem proves I.2.2(5a), the lifting clause of (5b), and (5c) for
M₁₂. Only |Z(K)| = 2 and restriction (i) remain as earlier-source inputs;
quasisimplicity supplies those in the parent. No orbit, coordinate, extension,
retraction or involution-table hypothesis remains. The exceptional-cover
parent retains the independent outer-inversion clause of (5b).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(5), printed pp.409–412 / PDF pp.420–423.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.Mathieu
open Theory.LinearAlgebra.BinaryCubicOrbits
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
open CoverCoordinates
open Sporadic.Mathieu.M12SmallPair
variable {K : Type*} [Group K] [Finite K]

namespace MarkedSquareCoordinates
variable {e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12} {u : K}
  {m : CoverOrbitData} (d : MarkedSquareCoordinates e u m)
include d

omit [Finite K] in
/-- The marked quotient centralizer has odd index 495, so restriction (i)
places the actual ambient center inside its commutator subgroup. -/
theorem centralizer_restriction (hr : CentralCoverRestriction K) :
    center K ≤ (_root_.commutator (centralizer ({u} : Set K))).map
      (centralizer ({u} : Set K)).subtype := by
  apply hr
  · intro a ha
    exact mem_centralizer_singleton_iff.mpr ((mem_center_iff.mp ha u).symm)
  · have hi : firstParabolic.index = 495 := by
      have h := firstParabolic.card_mul_index
      rw [card_firstParabolic, Sporadic.Mathieu.m12_order] at h
      omega
    have he := ((centralizer ({u} : Set K)).map
      (QuotientGroup.mk' (center K))).index_map_equiv e
    rw [map_map] at he
    change ((centralizer ({u} : Set K)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))).index = _ at he
    rw [d.centralizer_image, hi] at he
    rw [← he]
    decide

/-- The extra centralizer involution and cubic splitting exclude the elementary
branch by the source central-cover restriction. -/
theorem quadratic_ne_zero (hZ : Nat.card (center K) = 2)
    (hr : CentralCoverRestriction K) (hu : orderOf u = 2) : d.quadratic ≠ 0 := by
  intro hq
  exact no_centralizer_retraction u hZ (d.centralizer_restriction hr)
    (d.elementary_centralizer_retraction hZ hu hq)

/-- The source's literal double quotient has exactly six order-four cosets. -/
theorem quotient_count_six (hZ : Nat.card (center K) = 2)
    (hr : CentralCoverRestriction K) (hu : orderOf u = 2) :
    d.toSquareCoordinates.quotientOrderFourCosetCount = 6 := by
  have hn : d.quadratic (rep 0) ≠ 0 := by
    intro h
    exact d.quadratic_ne_zero hZ hr hu (zero_of_marked_zero d.quadratic d.invariant
      d.noncentral_fusion d.central_lift d.toSquareCoordinates.first_axis_zero h)
  rw [d.toSquareCoordinates.quotientOrderFourCosetCount_eq,
    count_of_marking d.quadratic d.invariant d.noncentral_fusion
      d.central_lift d.toSquareCoordinates.first_axis_zero, if_neg hn]

/-- The surviving quotient has actual generating quaternion constituents. -/
theorem quaternion_quotient (hZ : Nat.card (center K) = 2)
    (hr : CentralCoverRestriction K) (hu : orderOf u = 2) :
    Nonempty (QuaternionCentralProductData d.toSquareCoordinates.BinaryQuotient) :=
  d.toSquareCoordinates.quotient_quaternion_factors d.noncentral hZ
    (d.quadratic_ne_zero hZ hr hu)

/-- Fusion transfers the order-four conclusion from the first orbit to every
lift of the noncentral involution class. -/
theorem order_four_of_noncentral_fusion (hZ : Nat.card (center K) = 2)
    (hr : CentralCoverRestriction K) (hu : orderOf u = 2) (i : K)
    (hi : IsConj third (projection e i)) : orderOf i = 4 := by
  obtain ⟨r, hr0⟩ := d.coordinates_surjective (Multiplicative.ofAdd (rep 0))
  have hc : (d.coordinates r).toAdd = rep 0 := congrArg Multiplicative.toAdd hr0
  have hr4 : orderOf (r : K) = 4 :=
    (orderOf_injective (centralizerCore u).subtype (centralizerCore u).subtype_injective r).trans
      (d.toSquareCoordinates.noncentral_axis_order_four hZ (d.centralizer_restriction hr)
        (d.elementary_centralizer_retraction hZ hu) r hc)
  let rStar : core := ⟨projection e r, d.core_image r⟩
  have hcStar : (m.coordinates rStar).toAdd = orbit 0 0 := by
    change (m.coordinates ⟨_, d.core_image r⟩).toAdd = _
    rw [d.coordinate_compatibility, hc]
    rfl
  have hfuse : IsConj third (projection e r) := m.noncentral_fusion 0 0 rStar (Or.inl rfl) hcStar
  have hoStar : orderOf (projection e r) = 2 := by
    have h := m.orbit_order 0 0 rStar hcStar
    simpa only [show ¬ ((0 : Fin 5) = 3 ∨ (0 : Fin 5) = 4) by decide, if_false] using h
  have hker : (projection e).ker ≤ center K := by
    intro x hx
    exact (projection_eq_one e x).mp hx
  have hbinary : ∀ x ∈ (projection e).ker, x ^ 2 = 1 := by
    intro x hx
    exact CoreLiftData.ambient_center_square hZ x (hker hx)
  have hsqcenter : (r : K) ^ 2 ∈ center K := by
    rw [← projection_eq_one e, map_pow, ← hoStar, pow_orderOf_eq_one]
  have hs := (projection e).square_eq_of_isConj_map_of_central_binary_kernel
    (projection_surjective e) hker hbinary hsqcenter (hfuse.symm.trans hi)
  have hn : i ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one (hs.trans h)
    rw [hr4] at hd
    norm_num at hd
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one] using hn
  · change i ^ 4 = 1
    rw [show 4 = 2 * 2 from rfl, pow_mul, ← hs, ← pow_mul]
    exact congrArg Subtype.val (d.fourth_power r)
end MarkedSquareCoordinates

/-- The marked local calculation, including the actual binary quotient, has no
remaining orbit, coordinate, extension or retraction premise. -/
theorem marked_local_calculation (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K)
    (u : K) (hu : projection e u = z) :
    orderOf u = 2 ∧ ∃ d : MarkedSquareCoordinates e u coverOrbitData,
      d.toSquareCoordinates.quotientOrderFourCosetCount = 6 ∧
      Nonempty (QuaternionCentralProductData d.toSquareCoordinates.BinaryQuotient) ∧
      (∃ r₅ : centralizerCore u, (d.coordinates r₅).toAdd = rep 4 ∧ r₅ ^ 2 = d.root ^ 2) ∧
      HasUniqueCoreSquareLift u := by
  obtain ⟨hu2, ⟨d⟩⟩ := marked_coordinates e hZ hr coverOrbitData u hu
  exact ⟨hu2, d, d.quotient_count_six hZ hr hu2, d.quaternion_quotient hZ hr hu2,
    d.toSquareCoordinates.exists_second_axis_equal_square d.noncentral,
    d.toSquareCoordinates.hasUniqueCoreSquareLift d.noncentral⟩

/-- Every lift of the noncentral model class has order four. -/
theorem noncentral_class_order_four (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K)
    (i : K) (hi : IsConj third (projection e i)) : orderOf i = 4 := by
  obtain ⟨u, hu⟩ := projection_surjective e z
  obtain ⟨hu2, ⟨d⟩⟩ := marked_coordinates e hZ hr coverOrbitData u hu
  exact d.order_four_of_noncentral_fusion hZ hr hu2 i hi

/-- Re-mark the quotient identification; the original u and its literal core
remain the arguments of the square assertion. -/
theorem central_class_lift (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K)
    (u : K) (hu : IsConj z (projection e u)) :
    orderOf u = 2 ∧ HasUniqueCoreSquareLift u := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hu.symm
  let e' := e.trans (MulAut.conj g)
  have hm : projection e' u = z := hg
  obtain ⟨hu2, d, _, _, _, hs⟩ := marked_local_calculation e' hZ hr u hm
  exact ⟨hu2, hs⟩

/-- The literal I.2.2(5c) statement for every noncentral involution of the cover. -/
theorem hasUniqueCoreSquareLift (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K)
    (u : K) (hu : orderOf u = 2) (huz : u ∉ center K) : HasUniqueCoreSquareLift u := by
  have hp : orderOf (projection e u) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
    · exact fun he => huz ((projection_eq_one e u).mp he)
  rcases Sporadic.Mathieu.M12InvolutionFusion.marked_fusion (projection e u) hp with hc | hn
  · exact (central_class_lift e hZ hr u hc).2
  · have h4 := noncentral_class_order_four e hZ hr u hn
    omega

/-- Every representative of a two-central involution coset is involutory. -/
theorem twoCentral_lift_order_two (e : (K ⧸ center K) ≃* M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K)
    (u : K) (hu : orderOf (QuotientGroup.mk' (center K) u) = 2)
    (hc : TwoCentral (QuotientGroup.mk' (center K) u)) : orderOf u = 2 := by
  apply (central_class_lift e hZ hr u ?_).1
  exact M12Involutions.isConj_z_of_twoCentral _ ((e.orderOf_eq _).trans hu) (hc.map e)

/-- Every representative of a non-two-central involution coset has order four. -/
theorem nonTwoCentral_lift_order_four (e : (K ⧸ center K) ≃* M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K)
    (u : K) (hu : orderOf (QuotientGroup.mk' (center K) u) = 2)
    (hc : ¬ TwoCentral (QuotientGroup.mk' (center K) u)) : orderOf u = 4 := by
  apply noncentral_class_order_four e hZ hr u
  have ho : orderOf (projection e u) = 2 := (e.orderOf_eq _).trans hu
  apply (M12InvolutionFusion.marked_fusion _ ho).resolve_left
  intro h
  have hh := (M12Involutions.twoCentral_iff_isConj_z _ ho).mpr h
  exact hc (by simpa only [projection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using hh.map e.symm)

/-- The exact source two-central lifting clause, using the intrinsic Sylow mark. -/
theorem twoCentral_involution_lifting (e : (K ⧸ center K) ≃* M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K) :
    ∀ x : K ⧸ center K, IsSylowCentralInvolution x →
      ∃ u : K, QuotientGroup.mk' (center K) u = x ∧ orderOf u = 2 := by
  rintro x ⟨ho, P, hxP, hP⟩
  have hc : TwoCentral x := by
    refine ⟨P, hxP, mem_center_iff.mpr ?_⟩
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hP y.property))
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
  exact ⟨u, rfl, twoCentral_lift_order_two e hZ hr u ho hc⟩

/-- The lifting input consumed by the parent's outer-inversion reduction. -/
theorem nonTwoCentral_involution_lifting (e : (K ⧸ center K) ≃* M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K) :
    NonTwoCentralInvolutionLifting K := by
  intro x hx hc
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
  exact ⟨u, rfl, nonTwoCentral_lift_order_four e hZ hr u hx hc⟩

/-- I.2.2(5a), the lifting clause of (5b), and (5c), for M₁₂. Only the
previous center-order and restriction-(i) inputs remain for source assembly. -/
theorem lifting_and_core_square (e : (K ⧸ center K) ≃* M12)
    (hZ : Nat.card (center K) = 2) (hr : CentralCoverRestriction K) :
    (∀ x : K ⧸ center K, IsSylowCentralInvolution x →
      ∃ u : K, QuotientGroup.mk' (center K) u = x ∧ orderOf u = 2) ∧
    NonTwoCentralInvolutionLifting K ∧
    (∀ u : K, orderOf u = 2 → u ∉ center K → HasUniqueCoreSquareLift u) :=
  ⟨twoCentral_involution_lifting e hZ hr, nonTwoCentral_involution_lifting e hZ hr,
    hasUniqueCoreSquareLift e hZ hr⟩

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
