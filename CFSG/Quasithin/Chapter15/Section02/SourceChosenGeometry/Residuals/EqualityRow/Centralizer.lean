module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EscapingReductions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActions

/-!
# The original three-prime module centralizer in the equality row

The normal action on K/O₂(K) and the rank-two bound already prove that
M intersect Mc has order prime to three. The literal C_M(V) lies in this
intersection by the original intersection factorization. Monotonicity of
O^{3′} therefore proves the exact centralizer premise of 15.2.21(2), used
by the canonical seed argument, without identifying O^{3′}(Mc) with K.

Source: Aschbacher--Smith 15.2.12(4) and 15.2.21(2), pp.1111,1114,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}

/-- The literal module centralizer is a three-prime group in the equality row. -/
theorem ResidualInput.centralizer_threePrime_of_eq
    (r : ResidualInput hsource H B) (he : partnerSpan H Mc = residual H) :
    IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)) := by
  let C := M ⊓ centralizer (V : Set G)
  have hCA : C ≤ M ⊓ Mc := by
    rw [r.partner_intersection_eq]
    exact le_sup_left
  have hm := threePrimeResidual_mono hCA
  rw [r.intersection_residual_eq_bot_of_eq he] at hm
  have hz : threePrimeResidual C = ⊥ := bot_unique hm
  rw [threePrimeResidual_eq] at hz
  exact ((primeToResidual 3 C).map_eq_bot_iff_of_injective C.subtype_injective).mp hz

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
