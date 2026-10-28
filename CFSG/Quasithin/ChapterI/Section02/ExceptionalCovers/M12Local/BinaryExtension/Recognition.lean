module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local.BinaryExtension.Quotient
public import Theory.GroupTheory.HyperbolicQuaternionFactors
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
/-!
# Quaternion recognition for the marked binary extension

The supplied fusion marks determine the nonzero square form as a hyperbolic
form on the literal coordinate space. Four lifted basis vectors are involutions;
the two paired products square to the nonidentity element of the injected
ambient center, and all cross pairs commute. Their images generate the
coordinate quotient and their products generate its kernel. The hyperbolic
presentation theorem constructs two actual commuting quaternion subgroups,
with intersection of order two, which generate R/⟨v₄⟩.

Together with the elementary model this gives the sharper alternatives E₃₂
and Q₈ * Q₈. Source: Aschbacher–Smith, I.2.2(5), printed p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
open Theory.LinearAlgebra.BinaryCubicOrbits
variable {K : Type*} [Group K] {u : K}

namespace SquareCoordinates
variable (d : SquareCoordinates u)

/-- The fusion marks force a hyperbolic square form in the nonzero branch. -/
theorem quadratic_apply_of_ne_zero (hq : d.quadratic ≠ 0) (v : Space) :
    d.quadratic v = v.1.1 * v.2.1 + v.1.1 * v.2.2 + v.1.2 * v.2.2 := by
  have h0 : d.quadratic (rep 0) = 1 := by
    have hb : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide +kernel
    apply hb
    intro h
    exact hq (zero_of_marked_zero d.quadratic d.invariant d.noncentral_fusion
      d.central_lift d.first_axis_zero h)
  have h1 : d.quadratic (rep 1) = 1 := d.noncentral_fusion.symm.trans h0
  obtain ⟨o, rfl⟩ := orbitEquiv.surjective v
  rcases o with _ | ⟨j,k⟩
  · exact d.quadratic.map_zero
  · change d.quadratic (orbit j k) =
      (orbit j k).1.1 * (orbit j k).2.1 + (orbit j k).1.1 * (orbit j k).2.2 +
        (orbit j k).1.2 * (orbit j k).2.2
    rw [orbit_invariant d.quadratic d.invariant]
    have hc : ∀ j k, (orbit j k).1.1 * (orbit j k).2.1 +
        (orbit j k).1.1 * (orbit j k).2.2 + (orbit j k).1.2 * (orbit j k).2.2 =
        if j = 0 ∨ j = 1 then 1 else 0 := by decide +kernel
    rw [hc]
    fin_cases j
    · exact h0
    · exact h1
    · exact d.central_lift
    · exact d.first_axis_zero
    · exact d.second_axis_zero

private theorem commute_of_three_squares {G : Type*} [Group G] (x y : G)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : Commute x y := by
  have hi {z : G} (h : z ^ 2 = 1) : z⁻¹ = z :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
  change x * y = y * x
  calc
    x * y = (x * y)⁻¹ := (hi hxy).symm
    _ = y * x := by rw [mul_inv_rev, hi hx, hi hy]

/-- The nonzero branch supplies actual embedded quaternion factors of R/V₄. -/
theorem quotient_quaternion_factors (hu : u ∉ center K)
    (hZ : Nat.card (center K) = 2) (hq : d.quadratic ≠ 0) :
    Nonempty (QuaternionCentralProductData d.BinaryQuotient) := by
  obtain ⟨z, hz, hall⟩ := (Nat.card_eq_two_iff' (1 : d.quotientCenter)).mp
    (d.quotientCenter_card hu hZ)
  have hz1 : (z : d.BinaryQuotient) ≠ 1 := fun h => hz (Subtype.ext h)
  have hz2 : (z : d.BinaryQuotient) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := z)
    rw [d.quotientCenter_card hu hZ] at hh
    exact congrArg Subtype.val hh
  have hzc : (z : d.BinaryQuotient) ∈ center d.BinaryQuotient :=
    d.quotientCenter_le_center z.property
  have hs (r : d.BinaryQuotient) : r ^ 2 =
      if d.quadratic (d.quotientCoordinates r).toAdd = 0 then 1 else z := by
    split_ifs with hr
    · exact (d.quotient_square_eq_one_iff r).mpr hr
    · exact congrArg Subtype.val (hall ⟨r ^ 2, d.quotient_square_mem r⟩
        (fun hh => hr ((d.quotient_square_eq_one_iff r).mp (congrArg Subtype.val hh))))
  obtain ⟨x1, hx1⟩ := d.quotientCoordinates_surjective
    (Multiplicative.ofAdd (((1,0),(0,0)) : Space))
  obtain ⟨y1, hy1⟩ := d.quotientCoordinates_surjective
    (Multiplicative.ofAdd (((0,0),(1,0)) : Space))
  obtain ⟨x2, hx2⟩ := d.quotientCoordinates_surjective
    (Multiplicative.ofAdd (((0,1),(0,0)) : Space))
  obtain ⟨y2, hy2⟩ := d.quotientCoordinates_surjective
    (Multiplicative.ofAdd (((0,0),(1,1)) : Space))
  have sx1 : x1 ^ 2 = 1 := by rw [hs, hx1, d.quadratic_apply_of_ne_zero hq]; norm_num
  have sy1 : y1 ^ 2 = 1 := by rw [hs, hy1, d.quadratic_apply_of_ne_zero hq]; norm_num
  have sx2 : x2 ^ 2 = 1 := by rw [hs, hx2, d.quadratic_apply_of_ne_zero hq]; norm_num
  have sy2 : y2 ^ 2 = 1 := by rw [hs, hy2, d.quadratic_apply_of_ne_zero hq]; norm_num
  have sxy1 : (x1 * y1) ^ 2 = z := by
    rw [hs, map_mul, hx1, hy1, d.quadratic_apply_of_ne_zero hq]; norm_num
  have sxy2 : (x2 * y2) ^ 2 = z := by
    rw [hs, map_mul, hx2, hy2, d.quadratic_apply_of_ne_zero hq]; norm_num
  have cxx : Commute x1 x2 := commute_of_three_squares _ _ sx1 sx2 (by
    rw [hs, map_mul, hx1, hx2, d.quadratic_apply_of_ne_zero hq]; norm_num [show (2 : ZMod 2) = 0 by decide])
  have cxy : Commute x1 y2 := commute_of_three_squares _ _ sx1 sy2 (by
    rw [hs, map_mul, hx1, hy2, d.quadratic_apply_of_ne_zero hq]
    norm_num
    simp [show (2 : ZMod 2) = 0 by decide])
  have cyx : Commute y1 x2 := commute_of_three_squares _ _ sy1 sx2 (by
    rw [hs, map_mul, hy1, hx2, d.quadratic_apply_of_ne_zero hq]; norm_num [show (2 : ZMod 2) = 0 by decide])
  have cyy : Commute y1 y2 := commute_of_three_squares _ _ sy1 sy2 (by
    rw [hs, map_mul, hy1, hy2, d.quadratic_apply_of_ne_zero hq]; norm_num [show (2 : ZMod 2) = 0 by decide])
  have hc {x y : d.BinaryQuotient} (sx : x ^ 2 = 1) (sy : y ^ 2 = 1)
      (sxy : (x*y)^2 = z) : x*y*x⁻¹*y⁻¹=z := by
    have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using sx)
    have hyi : y⁻¹=y := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using sy)
    simpa only [hxi, hyi, pow_two, mul_assoc] using sxy
  have hgen : closure ({x1,y1,x2,y2} : Set d.BinaryQuotient) = ⊤ := by
    let H := closure ({x1,y1,x2,y2} : Set d.BinaryQuotient)
    have mx1 : x1 ∈ H := subset_closure (by simp)
    have my1 : y1 ∈ H := subset_closure (by simp)
    have mx2 : x2 ∈ H := subset_closure (by simp)
    have my2 : y2 ∈ H := subset_closure (by simp)
    have mz : (z : d.BinaryQuotient) ∈ H := sxy1 ▸ H.pow_mem (H.mul_mem mx1 my1) 2
    have hk : d.quotientCoordinates.ker ≤ H := by
      intro r hr
      by_cases h : r = 1
      · simp [h]
      · have hr' : r ∈ d.quotientCenter := d.quotientCoordinates_ker ▸ hr
        have he := congrArg Subtype.val (hall ⟨r,hr'⟩ (fun hh => h (congrArg Subtype.val hh)))
        change r = (z : d.BinaryQuotient) at he
        rw [he]
        exact mz
    have hword : ∀ v : Space, ∃ a b c f : Fin 2,
        Multiplicative.ofAdd v =
          (Multiplicative.ofAdd (((1,0),(0,0)) : Space)) ^ (a : ℕ) *
          (Multiplicative.ofAdd (((0,0),(1,0)) : Space)) ^ (b : ℕ) *
          (Multiplicative.ofAdd (((0,1),(0,0)) : Space)) ^ (c : ℕ) *
          (Multiplicative.ofAdd (((0,0),(1,1)) : Space)) ^ (f : ℕ) := by decide +kernel
    apply top_unique
    intro r _
    obtain ⟨a,b,c,f,hw⟩ := hword (d.quotientCoordinates r).toAdd
    let w := x1 ^ (a : ℕ) * y1 ^ (b : ℕ) * x2 ^ (c : ℕ) * y2 ^ (f : ℕ)
    have mw : w ∈ H := H.mul_mem (H.mul_mem (H.mul_mem
      (H.pow_mem mx1 _) (H.pow_mem my1 _)) (H.pow_mem mx2 _)) (H.pow_mem my2 _)
    have he : d.quotientCoordinates r = d.quotientCoordinates w := by
      simpa only [w, map_mul, map_pow, hx1, hy1, hx2, hy2, ofAdd_toAdd] using hw
    have hd : w⁻¹*r ∈ d.quotientCoordinates.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have hm := H.mul_mem mw (hk hd)
    simpa only [mul_inv_cancel_left] using hm
  obtain ⟨L,R,hL,hR,hspan,hinter,hcomm⟩ :=
    exists_quaternion_factors_of_hyperbolic_involutions x1 y1 x2 y2 z
      sx1 sy1 sx2 sy2 hz1 hz2 hzc (hc sx1 sy1 sxy1) (hc sx2 sy2 sxy2)
      cxx cxy cyx cyy hgen
  exact ⟨⟨L,R,hL,hR,hinter,hcomm,hspan⟩⟩

/-- The marked cover has the sharper two alternatives: E₃₂ or Q₈ * Q₈. -/
theorem quotient_models [Finite K] (hu : u ∉ center K) (hZ : Nat.card (center K) = 2) :
    Nonempty (d.BinaryQuotient ≃* Multiplicative (Fin 5 → ZMod 2)) ∨
      Nonempty (QuaternionCentralProductData d.BinaryQuotient) := by
  by_cases hq : d.quadratic = 0
  · exact Or.inl (d.quotient_equiv_elementary hu hZ hq)
  · exact Or.inr (d.quotient_quaternion_factors hu hZ hq)

end SquareCoordinates

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M12Local
