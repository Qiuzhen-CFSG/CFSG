module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Recognition

/-!
# The fixed-space quotient in MS93 (4.6.8), claim (1)

`Quotient` constructs both V_beta/Z_alpha and the subsequent quotient by
the fixed space of the tilded residual. Both carry the literal action of
the full marked parabolic. The contrary triple hypothesis forces nonzero
residual action on the final quotient, and the full actor has no nontrivial
odd-order quotient.

The displacement and symmetry argument in `GeometryBound` bounds the order
of this quotient by four. `Recognition` then identifies its full action
with the natural SL₂(2) action. `flagNaturalSection` assembles these results
and transports the coordinates through `FlagLayerModule.toRankOneFactor`,
preserving the exact ambient kernel and literal conjugation equation.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), numbered claim (1) in the proof of (4.6.8), printed p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- MS93 (4.6.8), claim (1), in the binary case: under the contrary triple
hypothesis, the quotient of the barred edge layer by the fixed space of the
tilded residual is a natural SL₂(2) module for the full untilded parabolic.
The witness includes the onto actor map, onto coordinates, exact kernel
and ambient-conjugation equation. -/
theorem flagNaturalSection (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    Nonempty (FlagNaturalSection source i) := by
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (flagParabolic source i) := Finite.of_injective
    (inclusion (flagParabolic_le source i)) (inclusion_injective _)
  let d := flagQuotientModule source geometry common.large_distance i hkernel
  have hcard : Nat.card d.Space ≤ 4 := by
    rw [d.card]
    exact flagFixedPreimage_relIndex_le_four source geometry common hb early i hkernel hbad
  obtain ⟨π, hπ, e, he⟩ := exists_natural_sl2_of_residuals_card_le_four d.representation
    (flagParabolic_primeToResidual source i)
    (d.residual_not_le_kernel geometry common.large_distance hkernel hbad) hcard
  exact ⟨d.toRankOneFactor geometry common.large_distance hkernel π hπ e he⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
