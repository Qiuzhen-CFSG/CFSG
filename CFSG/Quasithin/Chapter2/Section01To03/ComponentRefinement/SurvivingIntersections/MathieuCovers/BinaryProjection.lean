module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.M22Reduction
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary

/-!
# The original inner involution on a binary M₂₂ component

An inducing element has square in the covering center. Binary involution
lifting makes that square trivial, so the original action has an involution
projection even though the center is nontrivial. Its noncentrality follows
from L not contained in C_G(z), and it lies in the actual component Sylow.
The I.2.2(6b) core-square theorem now applies with its earlier perfectness
and A₆-cover inputs discharged. All groups, actions and quotients are literal.

This does not force the covering center to be normalized by the larger S
or T. Source: Aschbacher–Smith I.2.2(6b), printed pp.410,412, and the
1.1.5(3)(f) input to 2.3.9(7)(f), printed pp.502,525–526.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open ChapterI.Section02.ExceptionalCovers
variable {G : Type*} [Group G]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The precise I.2.2(6b) assertion on the original component, with all
earlier inputs discharged from the binary cover already supplied. -/
theorem LocalSetup.mathieuTwentyTwo_binary_uniqueCoreSquare
    (h : LocalSetup H L M S z) (e : (L ⧸ pCore 2 L) ≃* M22)
    (hc : Nat.card (pCore 2 L) = 2) (u : L)
    (hu : orderOf u = 2) (hun : u ∉ center L) : HasUniqueCoreSquareLift u := by
  let := h.finite
  let := h.quasisimple
  let eZ := h.mathieuTwentyTwo_centerQuotient e
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq e] using hc
  have hp : IsPGroup 2 (center L) := by
    rw [h.mathieuTwentyTwo_center_eq e]
    exact pCore_isPGroup
  apply M22Local.Binary.hasUniqueCoreSquareLift eZ hZ
    AlternatingSix.twoPrimaryInvolutionData _ u hu hun
  intro B hB
  exact M22CentralCover.hexadPreimage_isPerfect eZ hp hB

/-- A genuine projection of the original z in the binary-cover branch.
The Sylow equality identifies R with the literal S ∩ L, not with S. -/
theorem mathieuTwentyTwo_binary_projection
    (h : LocalSetup H L M S z) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      HasUniqueCoreSquareLift t ∧
      ∃ R : Sylow 2 L,
        (R : Subgroup L) = ((S : Subgroup H).map H.subtype).subgroupOf L ∧
        t ∈ (R : Subgroup L) ∧ t ∈ centralizer (R : Set L) := by
  let := h.finite
  obtain ⟨t, ht⟩ := d.inner
  have htn : t ∉ center L := by
    intro htc
    apply h.action_ne_one d.action d.conjugation
    rw [← ht]
    apply MulEquiv.ext
    intro x
    change t * x * t⁻¹ = x
    rw [← mem_center_iff.mp htc x, mul_inv_cancel_right]
  have hts : t ^ 2 ∈ center L := by
    have he : MulAut.conj (t ^ 2) = 1 := by
      rw [map_pow, ht, h.action_sq d.action d.conjugation]
    apply mem_center_iff.mpr
    intro x
    have hx : t ^ 2 * x * (t ^ 2)⁻¹ = x := DFunLike.congr_fun he x
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  let eZ := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  have ht2 : t ^ 2 = 1 := by
    apply M22CentralCover.square_eq_one eZ hZ t
    rw [← map_pow]
    change t ^ 2 ∈ (M22CentralCover.projection eZ).ker
    rwa [M22CentralCover.projection_ker]
  have htord : orderOf t = 2 :=
    orderOf_eq_prime ht2 (fun he => htn (he ▸ (center L).one_mem))
  have hproj : IsConjugationProjection L z t := by
    intro x
    rw [← d.conjugation x, ← ht]
    rfl
  obtain ⟨R, hR⟩ := h.component_sylow
  exact ⟨t, hproj, htord, htn,
    h.mathieuTwentyTwo_binary_uniqueCoreSquare d.quotientIso hc t htord htn,
    R, hR, h.projection_mem_sylow hproj htord R hR,
    h.projection_centralizes_sylow hproj R hR⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
