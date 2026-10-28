module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local.Restriction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit

/-!
# The intrinsic J₂ square orbit in an actual double cover

The literal ATLAS centralizer is perfect and its two-core square roots of the
marked involution form a nonempty conjugacy class. The central-cover restriction
law (i) therefore gives perfection of its preimage. Applying the checked square
orbit lifting theorems produces the distinguished involution square and the
unique core-square lift of every lift of the marked quotient involution.

Only the earlier source inputs, center order two and the restriction law, remain
explicit. No perfection, orbit, or lifting assumption remains. The elementary
quotient and SL₂(5) recognition stay with the final local-cover assembly.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
open Sporadic.LeechRelated.J2
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.FirstParabolic
variable {K : Type*} [Group K]

/-- The two source markings are literally the same subtype element. -/
theorem marked_eq_tL : marked = CoverSquareOrbit.tL := rfl

/-- Source restriction law (i) discharges perfection upstairs. -/
theorem preimage_isPerfect (e : (K ⧸ center K) ≃* Carrier)
    (hi : center K ≤ ⁅preimage e, preimage e⁆) : Group.IsPerfect (preimage e) := by
  let := CoverSquareOrbit.l₁_isPerfect
  exact preimage_perfect_of_restriction e hi

/-- Every lift of the marked involution has a unique core-square lift. -/
theorem unique_core_square [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    (hZ : Nat.card (center K) = 2) (hi : center K ≤ ⁅preimage e, preimage e⁆)
    (u : K) (hu : projection e u = z) : HasUniqueCoreSquareLift u := by
  let := preimage_isPerfect e hi
  exact unique_core_square_of_quotient_orbit e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj u hu

/-- The distinguished square is an involution above the source marking. -/
theorem involution_square_lift [Finite K] (e : (K ⧸ center K) ≃* Carrier)
    (hZ : Nat.card (center K) = 2) (hi : center K ≤ ⁅preimage e, preimage e⁆) :
    ∃ v : K, orderOf v = 2 ∧ projection e v = z ∧
      (∃ x ∈ centralizerCore v, x ^ 2 = v) ∧ HasUniqueCoreSquareLift v := by
  let := preimage_isPerfect e hi
  exact involution_square_lift_of_quotient_orbit e hZ
    CoverSquareOrbit.exists_core_square CoverSquareOrbit.core_square_isConj

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.J2Local
