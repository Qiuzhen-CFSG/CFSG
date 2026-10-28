module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.Local
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.RankOne
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Selection

/-!
# Reverse midpoint radius displacement

The forward first-layer inequalities fill Q_beta/Q_middle with V_alpha.
The selection theorem then constructs an escaping transported edge whose
parabolic has an index-three join with the original radius and its own core.
The transported fixed-index estimate excludes reverse displacement at most
two, with the denominator changed from Z_alpha to Z_middle by the proved
centralizer calculation.

This assembles the reverse inequality conditional only on the explicit forward
inequalities and the standing source hypotheses. The forward inequalities and
the complete `FlagP905Displacement` remain with the parent assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (1), printed p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- The reverse displacement in the source's symmetric argument, conditional
on the forward first-layer inequalities. The escaping edge, parabolic join,
and all quotient transports are constructed by the imported proofs. -/
theorem FlagCriticalData.two_lt_middle_radius_index_of_forward
    (p : FlagCriticalData source geometry i)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (_hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hexcess : 4 < (flagFixedPreimage source i).relIndex (V R (beta R)))
    (hforward : ∀ p : FlagCriticalData source geometry i, ∀ d : M,
      flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ∀ g : M, flagIncident source i g d →
      localFlagZ source i g ≠ localFlagZ source i 1 →
      2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)) :
    2 < (Q R (alpha R)).relIndex (V R p.middle) := by
  obtain ⟨w⟩ := p.reverseRadiusWitness common hb early hkernel (hforward p)
  exact w.two_lt_middle_radius_index common early hkernel hexcess

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
